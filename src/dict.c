#include <string.h>
#include <stdbool.h>

#include "ty.h"
#include "alloc.h"
#include "xd.h"
#include "value.h"
#include "dict.h"
#include "log.h"
#include "vm.h"
#include "gc.h"
#include "vec.h"

#define INITIAL_SIZE 8
#define NO_SUCH_SPOT SIZE_MAX

#define ENSURE_INIT(d) do {      \
        if ((d)->size == 0) {    \
                initxd(ty, (d)); \
        }                        \
} while (0)

#define OCCUPIED(d, i) ((i != NO_SUCH_SPOT) && ((d)->items[i].k.type != 0))

inline static void
initxd(Ty *ty, Dict *d)
{
        NOGC(d);
        d->items = mA0(sizeof (DictItem) * INITIAL_SIZE);
        d->size  = INITIAL_SIZE;
        OKGC(d);
}

inline static Value *
val(Dict *d, usize i)
{
        return &d->items[i].v;
}

inline static usize
find_spot(
        Ty *ty,
        usize size,
        DictItem const *items,
        u64 h,
        Value const *k
) {
        if (size == 0) {
                return NO_SUCH_SPOT;
        }

        usize mask = size - 1;
        usize i = h & mask;

        while (
                (items[i].k.type != 0)
             && ((items[i].h != h) || !v_eq(&items[i].k, k))
        ) {
                i = (i + 1) & mask;
        }

        return i;
}

inline static usize
delete(Dict *d, usize i)
{
        usize mask = d->size - 1;
        u64 h = d->items[i].h & mask;

        usize j = i;
        usize k = (i + 1) & mask;

        while (d->items[k].k.type != 0) {
                if ((d->items[k].h & mask) == h) {
                        j = k;
                }
                k = (k + 1) & mask;
        }

        if (d->items[i].next != NULL) {
                d->items[i].next->prev = d->items[i].prev;
        } else {
                d->last = d->items[i].next;
        }
        if (d->items[i].prev != NULL) {
                d->items[i].prev->next = d->items[i].next;
        }

        if (i != j) {
                d->items[i] = d->items[j];
                if (d->items[i].next != NULL) {
                        d->items[i].next->prev = &d->items[i];
                } else {
                        d->last = &d->items[i];
                }
                if (d->items[i].prev != NULL) {
                        d->items[i].prev->next = &d->items[i];
                }
        }

        m0(d->items[j]);
        d->count -= 1;

        return min(i, j);
}

inline static void
grow(Ty *ty, Dict *d)
{
        usize size = (d->size * 2);

        DictItem *items = mA0(size * sizeof (DictItem));
        DictItem *last = NULL;

        DictItem *it = d->last;

        while (it->prev != NULL) {
                it = it->prev;
        }

        while (it != NULL) {
                usize i = find_spot(ty, size, items, it->h, &it->k);
                if (last != NULL) {
                        last->next = &items[i];
                }
                items[i].k = it->k;
                items[i].v = it->v;
                items[i].h = it->h;
                items[i].prev = last;
                last = &items[i];
                it = it->next;
        }

        mF(d->items);

        d->items = items;
        d->last  = last;
        d->size  = size;
}

inline static Value *
put(Ty *ty, Dict *d, usize i, u64 h, Value k, Value v)
{
        ENSURE_INIT(d);

        if (4 * d->count >= 3 * d->size) {
                grow(ty, d);
                i = find_spot(ty, d->size, d->items, h, &k);
        }

        if (d->last != NULL) {
                d->last->next = &d->items[i];
        }

        d->items[i].k = k;
        d->items[i].v = v;
        d->items[i].h = h;

        d->items[i].prev = d->last;
        d->items[i].next = NULL;
        d->last = &d->items[i];

        d->count += 1;

        return val(d, i);
}

Value *
dict_get_value(Ty *ty, Dict *d, Value *key)
{
        u64 h = value_hash(ty, key);
        usize i = find_spot(ty, d->size, d->items, h, key);

        if (OCCUPIED(d, i)) {
                return val(d, i);
        }

        if (d->dflt.type != VALUE_ZERO) {
                GC_STOP();
                ENSURE_INIT(d);
                Value dflt = value_apply_callable(ty, &d->dflt, key);
                i = find_spot(ty, d->size, d->items, h, key);
                Value *v = put(ty, d, i, h, *key, dflt);
                GC_RESUME();
                return v;
        }

        return NULL;
}

bool
dict_has_value(Ty *ty, Dict *d, Value *key)
{
        if (d->size == 0) {
                return false;
        }

        u64 h = value_hash(ty, key);
        usize i = find_spot(ty, d->size, d->items, h, key);

        if (d->items[i].k.type != 0) {
                return true;
        }

        return false;
}

void
dict_put_value(Ty *ty, Dict *d, Value key, Value value)
{
        ENSURE_INIT(d);

        u64 h = value_hash(ty, &key);
        usize i = find_spot(ty, d->size, d->items, h, &key);

        if (d->items[i].k.type != 0) {
                d->items[i].v = value;
        } else {
                put(ty, d, i, h, key, value);
        }
}

Value *
dict_put_value_with(Ty *ty, Dict *d, Value key, Value v, Value const *f)
{
        ENSURE_INIT(d);

        u64 h = value_hash(ty, &key);
        usize i = find_spot(ty, d->size, d->items, h, &key);

        if (d->items[i].k.type != 0) {
                d->items[i].v = vm_eval_function(ty, f, &d->items[i].v, &v, NULL);
                return val(d, i);
        } else {
                return put(ty, d, i, h, key, v);
        }
}

Value *
dict_put_key_if_not_exists(Ty *ty, Dict *d, Value key)
{
        ENSURE_INIT(d);

        u64 h = value_hash(ty, &key);
        usize i = find_spot(ty, d->size, d->items, h, &key);

        if (d->items[i].k.type != 0) {
                return val(d, i);
        }

        Value v;

        if (d->dflt.type != VALUE_ZERO) {
                v = value_apply_callable(ty, &d->dflt, &key);
        } else {
                v = NIL;
        }

        return put(ty, d, i, h, key, v);
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

        if (d->dflt.type != VALUE_ZERO) {
                xvP(ty->marking, &d->dflt);
        }

#if defined(TY_TRACE_GC)
        if (d->size > 0) {
                ADD_REACHED(ALLOC_OF(d->items)->size);
        }
#endif

        dfor(d, {
                xvP(ty->marking, key);
                xvP(ty->marking, val);
        });
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
                if (d->dict->dflt.type == VALUE_ZERO) {
                        return NIL;
                } else {
                        return d->dict->dflt;
                }
        }

        d->dict->dflt = ARG(0);

        return *d;
}

static Value
dict_contains(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.contains()", 1);

        if (d->dict->size == 0) {
                return BOOLEAN(false);
        }

        Value *key = &ARG(0);
        u64 h = value_hash(ty, key);
        usize i = find_spot(ty, d->dict->size, d->dict->items, h, key);

        return BOOLEAN(d->dict->items[i].k.type != 0);
}

static Value
dict_keys(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.keys()", 0);

        Array *keys = vAn(d->dict->count);
        dfor(d->dict, vPx(*keys, *key));

        return ARRAY(keys);
}

static Value
dict_values(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.values()", 0);

        Array *values = vAn(d->dict->count);
        dfor(d->dict, vPx(*values, *val));

        return ARRAY(values);
}

static Value
dict_items(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.items()", 0);

        Array *items = vAn(d->dict->count);
        Value result = ARRAY(items);
        gP(&result);
        dfor(d->dict, vPx(*items, PAIR(*key, *val)));
        gX();

        return result;
}

Dict *
DictClone(Ty *ty, Dict const *d)
{
        Dict *new = dict_new(ty);
        new->dflt = d->dflt;

        NOGC(new);
        dfor(d, dict_put_value(ty, new, *key, *val));
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
        if (d->count != u->count) {
                return false;
        }

        for (usize i = 0; i < d->size;) {
                if (d->items[i].k.type == 0) {
                        i += 1;
                        continue;
                }
                usize j = find_spot(
                        ty,
                        u->size,
                        u->items,
                        d->items[i].h,
                        &d->items[i].k
                );
                if (!OCCUPIED(u, j)) {
                        return false;
                }
                i += 1;
        }

        return true;
}

inline static void
copy_unique(Ty *ty, Dict *diff, Dict const *d, Dict const *u)
{
        ENSURE_INIT(diff);

        for (usize i = 0; i < d->size; ++i) {
                if (d->items[i].k.type == 0) {
                        continue;
                }
                usize j = find_spot(
                        ty,
                        u->size,
                        u->items,
                        d->items[i].h,
                        &d->items[i].k
                );
                if (!OCCUPIED(u, j)) {
                        usize k = find_spot(
                                ty,
                                diff->size,
                                diff->items,
                                d->items[i].h,
                                &d->items[i].k
                        );

                        put(ty, diff, k, d->items[i].h, d->items[i].k, d->items[i].v);
                }
        }
}

Value
dict_diff(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("Dict.diff(): expected 1 argument but got %d", argc);
        }

        Value u = ARG(0);
        if (u.type != VALUE_DICT) {
                zP("Dict.diff(): expected Dict but got %s", SHOW(&u));
        }

        Dict *diff = dict_new(ty);
        NOGC(diff);
        copy_unique(ty, diff, d->dict, u.dict);
        copy_unique(ty, diff, u.dict, d->dict);
        OKGC(diff);

        return DICT(diff);
}

Value
dict_intersect(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.intersect()", 1, 2);

        Dict *u = DICT_ARG(0);

        if (argc == 1) {
                for (usize i = 0; i < d->dict->size;) {
                        if (d->dict->items[i].k.type == 0) {
                                i += 1;
                                continue;
                        }
                        usize j = find_spot(
                                ty,
                                u->size,
                                u->items,
                                d->dict->items[i].h,
                                &d->dict->items[i].k
                        );
                        if (!OCCUPIED(u, j)) {
                                i = delete(d->dict, i);
                        } else {
                                i += 1;
                        }
                }
        } else {
                Value f = ARG(1);
                if (!CALLABLE(f)) {
                        zP("the second argument to dict.intersect() must be callable");
                }
                for (usize i = 0; i < d->dict->size;) {
                        if (d->dict->items[i].k.type == 0) {
                                i += 1;
                                continue;
                        }
                        usize j = find_spot(
                                ty,
                                u->size,
                                u->items,
                                d->dict->items[i].h,
                                &d->dict->items[i].k
                        );
                        if (!OCCUPIED(u, j)) {
                                i = delete(d->dict, i);
                        } else {
                                d->dict->items[i].v = vm_eval_function(
                                        ty,
                                        &f,
                                        &d->dict->items[i].v,
                                        &u->items[j].v,
                                        NULL
                                );
                                i += 1;
                        }
                }

        }

        return *d;
}

Value
dict_intersect_copy(Ty *ty, Value *d, int argc, Value *kwargs)
{
        Value copy = dict_clone(ty, d, 0, NULL);
        return dict_intersect(ty, &copy, argc, kwargs);
}

Dict *
DictUpdate(Ty *ty, Dict *d, Dict const *u)
{
        for (usize i = 0; i < u->size; ++i) {
                if (u->items[i].k.type != 0) {
                        dict_put_value(ty, d, u->items[i].k, u->items[i].v);
                }
        }

        return d;
}

Dict *
DictUpdateWith(Ty *ty, Dict *d, Dict const *u, Value const *f)
{
        for (usize i = 0; i < u->size; ++i) {
                if (u->items[i].k.type != 0) {
                        dict_put_value_with(
                                ty,
                                d,
                                u->items[i].k,
                                u->items[i].v,
                                f
                        );
                }
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

        Dict *u = DICT_ARG(0);

        if (argc == 1) {
                for (usize i = 0; i < u->size; ++i) {
                        if (u->items[i].k.type != 0) {
                                usize j = find_spot(
                                        ty,
                                        d->dict->size,
                                        d->dict->items,
                                        u->items[i].h,
                                        &u->items[i].k
                                );
                                if (OCCUPIED(d->dict, j)) {
                                        delete(d->dict, j);
                                }
                        }
                }
        } else {
                Value f = ARG(1);
                for (usize i = 0; i < u->size; ++i) {
                        if (u->items[i].k.type != 0) {
                                usize j = find_spot(
                                        ty,
                                        d->dict->size,
                                        d->dict->items,
                                        u->items[i].h,
                                        &u->items[i].k
                                );
                                if (OCCUPIED(d->dict, j)) {
                                        vm_eval_function(
                                                ty,
                                                &f,
                                                &d->dict->items[i].v,
                                                &u->items[j].v,
                                                NULL
                                        );
                                        delete(d->dict, j);
                                }
                        }
                }

        }

        return *d;
}

static Value
dict_put(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Dict.put()", 1, INT_MAX);

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

        ENSURE_INIT(dict);

        u64   h = value_hash(ty, &key);
        usize i = find_spot(ty, dict->size, dict->items, h, &key);

        if (OCCUPIED(dict, i)) {
                return *val(dict, i);
        }

        usize size = dict->size;
        DictItem *items = dict->items;

        vmP(&key);
        Value val = vmC(&fun, 1);

        gP(&val);
        if (
                (dict->size != size)
             || (dict->items != items)
             || (OCCUPIED(dict, i) && !v_eq(&dict->items[i].k, &key))
        ) {
                i = find_spot(ty, dict->size, dict->items, h, &key);
        }
        put(ty, dict, i, h, key, val);
        gX();

        return val;
}

static Value
dict_clear(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.clear()", 0);

        memset(d->dict->items, 0, sizeof (DictItem) * d->dict->size);
        d->dict->last = NULL;
        d->dict->count = 0;

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

        DictItem *it;

        if (i < d->dict->count / 2) {
                it = DictFirst(d->dict);
                while (i --> 0) {
                        it = it->next;
                }
        } else {
                it = d->dict->last;
                i = d->dict->count - i - 1;
                while (i --> 0) {
                        it = it->prev;
                }
        }

        Value popped = PAIR(it->k, it->v);

        delete(d->dict, it - d->dict->items);

        return popped;
}

static Value
dict_remove(Ty *ty, Value *d, int argc, Value *kwargs)
{
        ASSERT_ARGC("Dict.remove()", 1);

        Value k = ARG(0);
        u64 h = value_hash(ty, &k);

        usize i = find_spot(
                ty,
                d->dict->size,
                d->dict->items,
                h,
                &k
        );

        if (!OCCUPIED(d->dict, i)) {
                return NIL;
        } else {
                Value v = d->dict->items[i].v;
                delete(d->dict, i);
                return v;
        }
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
        { .name = "has?",         .func = dict_contains        },
        { .name = "intersect",    .func = dict_intersect       },
        { .name = "items",        .func = dict_items           },
        { .name = "keys",         .func = dict_keys            },
        { .name = "len",          .func = dict_len             },
        { .name = "pop",          .func = dict_pop             },
        { .name = "ptr",          .func = dict_ptr             },
        { .name = "put",          .func = dict_put             },
        { .name = "remove",       .func = dict_remove          },
        { .name = "update",       .func = dict_update          },
        { .name = "values",       .func = dict_values          },
        { .name = "~=",           .func = dict_remove          },
);

DEFINE_METHOD_LOOKUP(dict);
DEFINE_METHOD_TABLE_BUILDER(dict);
DEFINE_METHOD_COMPLETER(dict);
