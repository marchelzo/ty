#include <string.h>
#include <stdbool.h>

#include "ty.h"
#include "alloc.h"
#include "xd.h"
#include "value.h"
#include "dict.h"
#include "set.h"
#include "log.h"
#include "vm.h"
#include "gc.h"
#include "vec.h"

#define HT                 Dict
#define HT_ITEM            DictItem
#define HT_PAYLOAD(it, src) ((it)->v = (src)->v)
#include "htab.h"

inline static Value *
val(Dict *d, usize i)
{
        return &d->items[i].v;
}

inline static Value *
put(Ty *ty, Dict *d, usize i, u64 h, Value k, Value v)
{
        HT_ENSURE(d);
        i = ht_claim(ty, d, i, h, &k);
        d->items[i].v = v;
        return val(d, ht_robinhood(d, i));
}

inline static bool
has_default(Dict const *d)
{
        return d->dflt.type != VALUE_ZERO;
}

Value *
dict_get_value(Ty *ty, Dict *d, Value *key)
{
        u64 h = value_hash(ty, key);
        usize i = ht_find(ty, d->size, d->items, h, key);

        if (HT_LIVE(d, i)) {
                return val(d, i);
        }

        if (!has_default(d)) {
                return NULL;
        }

        GC_STOP();
        HT_ENSURE(d);
        Value dflt = vm_call1(ty, &d->dflt, key);
        i = ht_find(ty, d->size, d->items, h, key);
        Value *v;
        if (HT_LIVE(d, i)) {
                v = val(d, i);
                *v = dflt;
        } else {
                v = put(ty, d, i, h, *key, dflt);
        }
        GC_RESUME();

        return v;
}

bool
dict_has_value(Ty *ty, Dict *d, Value *key)
{
        return ht_lookup(ty, d, key) != HT_NONE;
}

void
dict_put_value(Ty *ty, Dict *d, Value key, Value value)
{
        gP(&key);
        gP(&value);

        HT_ENSURE(d);

        u64 h = value_hash(ty, &key);
        usize i = ht_find(ty, d->size, d->items, h, &key);

        if (HT_LIVE(d, i)) {
                *val(d, i) = value;
        } else {
                put(ty, d, i, h, key, value);
        }

        gX();
        gX();
}

static Value *
dict_put_value_with(Ty *ty, Dict *d, Value key, Value v, Value const *f)
{
        gP(&key);
        gP(&v);

        HT_ENSURE(d);

        u64 h = value_hash(ty, &key);
        usize i = ht_find(ty, d->size, d->items, h, &key);

        Value *result;
        if (HT_LIVE(d, i)) {
                result = val(d, i);
                *result = vm_eval_function(ty, f, result, &v, NULL);
        } else {
                result = put(ty, d, i, h, key, v);
        }

        gX();
        gX();

        return result;
}

Value *
dict_put_key_if_not_exists(Ty *ty, Dict *d, Value key)
{
        gP(&key);

        HT_ENSURE(d);

        u64 h = value_hash(ty, &key);
        usize i = ht_find(ty, d->size, d->items, h, &key);

        if (HT_LIVE(d, i)) {
                gX();
                return val(d, i);
        }

        Value v = NIL;

        if (has_default(d)) {
                v = vm_call1(ty, &d->dflt, &key);
                i = ht_find(ty, d->size, d->items, h, &key);
                if (HT_LIVE(d, i)) {
                        gX();
                        return val(d, i);
                }
        }

        gP(&v);
        Value *result = put(ty, d, i, h, key, v);
        gX();
        gX();

        return result;
}

Value *
dict_put_member_if_not_exists(Ty *ty, Dict *d, char const *member)
{
        return dict_put_key_if_not_exists(ty, d, STRING_NOGC(member, strlen(member)));
}

Value *
dict_get_member(Ty *ty, Dict *d, char const *key)
{
        Value string = STRING_NOGC(key, strlen(key));
        return dict_get_value(ty, d, &string);
}

void
dict_put_member(Ty *ty, Dict *d, char const *key, Value value)
{
        Value string = STRING_NOGC(key, strlen(key));
        dict_put_value(ty, d, string, value);
}

void
dict_mark(Ty *ty, Dict *d)
{
        if (MARKED(d)) return;

        MARK(d);

        if (has_default(d)) {
                xvP(ty->marking, &d->dflt);
        }

#if defined(TY_TRACE_GC)
        if (d->size > 0) {
                ADD_REACHED(ALLOC_OF(d->items)->size);
        }
#endif

        htfor(it, d) {
                xvP(ty->marking, &it->k);
                xvP(ty->marking, &it->v);
        }
}

void
dict_free(Ty *ty, Dict *d)
{
        mF(d->items);
}

static Value
dict_default(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.default()", 0, 1);

        if (argc == 0) {
                return has_default(d->dict) ? d->dict->dflt : NIL;
        }

        Value dflt = ARG(0);
        d->dict->dflt = !IsNil(dflt) ? dflt : ZERO;

        return *d;
}

static Value
dict_contains(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.contains()", 1);
        return BOOLEAN(ht_lookup(ty, d->dict, &ARG(0)) != HT_NONE);
}

static Value
dict_keys(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.keys()", 0);

        Array *keys = vAn(d->dict->count);
        htfor(it, d->dict) {
                vPx(*keys, it->k);
        }

        return ARRAY(keys);
}

static Value
dict_values(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.values()", 0);

        Array *values = vAn(d->dict->count);
        htfor(it, d->dict) {
                vPx(*values, it->v);
        }

        return ARRAY(values);
}

static Value
dict_items(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.items()", 0);

        Array *items = vAn(d->dict->count);
        Value result = ARRAY(items);
        gP(&result);
        htfor(it, d->dict) {
                vPx(*items, PAIR(it->k, it->v));
        }
        gX();

        return result;
}

Dict *
DictClone(Ty *ty, Dict const *d)
{
        Dict *new = dict_new(ty);

        NOGC(new);
        new->dflt = d->dflt;
        ht_copy(ty, new, d);
        OKGC(new);

        return new;
}

static Value
dict_clone(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.clone()", 0);
        return DICT(DictClone(ty, d->dict));
}

bool
dict_same_keys(Ty *ty, Dict const *d, Dict const *u)
{
        return ht_same_keys(ty, d, u);
}

bool
dict_equal_x(Ty *ty, Dict const *d, Dict const *u, ValueEqFn *eq, void *ctx)
{
        if (d == u) {
                return true;
        }

        if (d->count != u->count) {
                return false;
        }

        htfor(it, d) {
                usize i = ht_find_x(ty, u, it->h, &it->k, eq, ctx);
                if (i == HT_NONE || !(*eq)(ty, &it->v, &u->items[i].v, ctx)) {
                        return false;
                }
        }

        return true;
}

u64
dict_hash_x(Ty *ty, Dict const *d, ValueHashFn *hash, void *ctx)
{
        u64 h = hash64(d->count ^ 0xD1C7D1C7D1C7D1C7ULL);

        htfor(it, d) {
                h += hash64(HashCombine(it->h, (*hash)(ty, &it->v, ctx)));
        }

        return h;
}

static Value
dict_diff(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.diff()", 1);

        Dict *u    = DICT_ARG(0);
        Dict *diff = dict_new(ty);

        NOGC(diff);
        ht_unique(ty, diff, d->dict, u);
        ht_unique(ty, diff, u, d->dict);
        OKGC(diff);

        return DICT(diff);
}

Value
dict_intersect(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.intersect()", 1, 2);

        if (argc == 1 && ARG(0).type == VALUE_SET) {
                DictKeepKeys(ty, d->dict, ARG(0).set);
                return *d;
        }

        Dict *u = DICT_ARG(0);

        if (argc == 1) {
                ht_retain(ty, d->dict, u);
                return *d;
        }

        Value f = ARG(1);
        if (!CALLABLE(f)) {
                zP("the second argument to dict.intersect() must be callable");
        }

        htfor_del(it, d->dict) {
                usize j = ht_seek(ty, u, it);
                if (!HT_LIVE(u, j)) {
                        ht_delete(d->dict, it - d->dict->items);
                } else {
                        it->v = vm_eval_function(ty, &f, &it->v, val(u, j), NULL);
                }
        }

        return *d;
}

static Value
dict_intersect_copy(Ty *ty, Value *d, int argc, Value *kwargs)
{
        Value copy = DICT(DictClone(ty, d->dict));
        gP(&copy);
        Value result = dict_intersect(ty, &copy, argc, kwargs);
        gX();
        return result;
}

Dict *
DictUpdate(Ty *ty, Dict *d, Dict const *u)
{
        htfor(it, u) {
                dict_put_value(ty, d, it->k, it->v);
        }

        return d;
}

Dict *
DictUpdateWith(Ty *ty, Dict *d, Dict const *u, Value const *f)
{
        htfor(it, u) {
                dict_put_value_with(ty, d, it->k, it->v, f);
        }

        return d;
}

static Value
dict_update(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.update()", 1, 2);

        Dict *u = DICT_ARG(0);

        return DICT(
                (argc == 1)
              ? DictUpdate(ty, d->dict, u)
              : DictUpdateWith(ty, d->dict, u, &ARG(1))
        );
}

Value
dict_subtract(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.subtract()", 1, 2);

        if (argc == 1 && ARG(0).type == VALUE_SET) {
                DictDropKeys(ty, d->dict, ARG(0).set);
                return *d;
        }

        Dict *u = DICT_ARG(0);

        if (argc == 1) {
                ht_discard(ty, d->dict, u);
                return *d;
        }

        Value f = ARG(1);

        htfor(it, u) {
                usize j = ht_seek(ty, d->dict, it);
                if (HT_LIVE(d->dict, j)) {
                        vm_eval_function(ty, &f, val(d->dict, j), &it->v, NULL);
                        ht_delete(d->dict, j);
                }
        }

        return *d;
}

Dict *
DictDropKeys(Ty *ty, Dict *d, Set const *keys)
{
        for (SetItem const *it = keys->first; it != NULL && d->count > 0; it = it->next) {
                usize i = ht_find(ty, d->size, d->items, it->h, &it->k);
                if (HT_LIVE(d, i)) {
                        ht_delete(d, i);
                }
        }

        return d;
}

Dict *
DictKeepKeys(Ty *ty, Dict *d, Set const *keys)
{
        htfor_del(it, d) {
                if (!set_has_hashed(ty, keys, it->h, &it->k)) {
                        ht_delete(d, it - d->items);
                }
        }

        return d;
}

static Value
dict_put(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Dict.put()", 1);

        for (int i = 0; i < argc; ++i) {
                dict_put_value(ty, d->dict, ARG(i), NIL);
        }

        return *d;
}

static Value
dict_get_or_put_with(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.get-or-put-with()", 2);

        Value key = ARG(0);
        Value fun = ARG(1);

        Dict *dict = d->dict;

        HT_ENSURE(dict);

        u64   h = value_hash(ty, &key);
        usize i = ht_find(ty, dict->size, dict->items, h, &key);

        if (HT_LIVE(dict, i)) {
                return *val(dict, i);
        }

        usize size = dict->size;
        DictItem *items = dict->items;

        vmP(&key);
        Value v = vmC(&fun, 1);

        gP(&v);
        if (
                (dict->size != size)
             || (dict->items != items)
             || HT_LIVE(dict, i)
        ) {
                i = ht_find(ty, dict->size, dict->items, h, &key);
        }
        if (HT_LIVE(dict, i)) {
                *val(dict, i) = v;
        } else {
                put(ty, dict, i, h, key, v);
        }
        gX();

        return v;
}

static Value
dict_clear(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.clear()", 0);
        ht_clear(d->dict);
        return *d;
}

static Value
dict_pop(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.pop()", 0, 1);

        isize i = (argc == 1) ? INT_ARG(0) : -1;

        if (i < 0) {
                i += d->dict->count;
        }
        if (i < 0 || i >= d->dict->count) {
                bP("index %jd out of range [0, %zu)", i, d->dict->count);
        }

        DictItem *it = ht_nth(d->dict, i);
        Value popped = PAIR(it->k, it->v);

        ht_delete(d->dict, it - d->dict->items);

        return popped;
}

static Value
dict_remove(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.remove()", 1);

        usize i = ht_lookup(ty, d->dict, &ARG(0));

        if (i == HT_NONE) {
                return NIL;
        }

        Value v = *val(d->dict, i);
        ht_delete(d->dict, i);

        return v;
}

static Value
dict_keep_mut(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.keep!()", 1);

        Value f    = ARG(0);
        Dict *dict = d->dict;

        htfor_del(it, dict) {
                Value keep = vm_eval_function(ty, &f, &it->k, &it->v, NULL);
                if (!value_truthy(ty, &keep)) {
                        ht_delete(dict, it - dict->items);
                }
        }

        return *d;
}

static Value
dict_keep(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.keep()", 1);

        Value f   = ARG(0);
        Dict *new = dict_new(ty);

        NOGC(new);

        htfor(it, d->dict) {
                Value keep = vm_eval_function(ty, &f, &it->k, &it->v, NULL);
                if (value_truthy(ty, &keep)) {
                        dict_put_value(ty, new, it->k, it->v);
                }
        }

        OKGC(new);

        return DICT(new);
}

static Value
dict_len(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.len()", 0);
        return INTEGER(d->dict->count);
}

static Value
dict_ptr(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.ptr()", 0);
        return PTR(d->dict);
}

DEFINE_METHOD_TABLE(
        dict,
        { .name = "&",            .func = dict_intersect_copy  },
        { .name = "&=",           .func = dict_intersect       },
        { .name = "<<",           .func = dict_put             },
        { .name = "?",            .func = dict_contains        },
        { .name = "clear",        .func = dict_clear           },
        { .name = "clone",        .func = dict_clone           },
        { .name = "contains?",    .func = dict_contains        },
        { .name = "default",      .func = dict_default         },
        { .name = "diff",         .func = dict_diff            },
        { .name = "getOrPutWith", .func = dict_get_or_put_with },
        { .name = "intersect",    .func = dict_intersect       },
        { .name = "items",        .func = dict_items           },
        { .name = "keep",         .func = dict_keep            },
        { .name = "keep!",        .func = dict_keep_mut        },
        { .name = "keys",         .func = dict_keys            },
        { .name = "len",          .func = dict_len             },
        { .name = "pop",          .func = dict_pop             },
        { .name = "ptr",          .func = dict_ptr             },
        { .name = "put",          .func = dict_put             },
        { .name = "remove",       .func = dict_remove          },
        { .name = "subtract",     .func = dict_subtract        },
        { .name = "update",       .func = dict_update          },
        { .name = "values",       .func = dict_values          },
        { .name = "~=",           .func = dict_remove          },
);

DEFINE_METHOD_LOOKUP(dict);
DEFINE_METHOD_TABLE_BUILDER(dict);
DEFINE_METHOD_COMPLETER(dict);
