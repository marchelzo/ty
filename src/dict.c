#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "ty.h"
#include "alloc.h"
#include "util.h"
#include "value.h"
#include "dict.h"
#include "log.h"
#include "vm.h"
#include "gc.h"
#include "vec.h"

#define INITIAL_SIZE 16

Dict *
dict_new(Ty *ty)
{
        Dict *d = mAo(sizeof *d, GC_DICT);
        NOGC(d);

        d->size = INITIAL_SIZE;
        d->hashes = mA(sizeof (unsigned long [INITIAL_SIZE]));
        d->keys = mA(sizeof (Value [INITIAL_SIZE]));
        d->values = mA(sizeof (Value [INITIAL_SIZE]));
        d->count = 0;
        d->dflt = NONE;
        memset(d->keys, 0, sizeof (Value [INITIAL_SIZE]));

        OKGC(d);

        return d;
}

inline static size_t
find_spot(Ty *ty, size_t size, unsigned long const *hs, Value const *vs, unsigned long h, Value const *v)
{
        size_t mask = size - 1;
        size_t i = h & mask;

        while (vs[i].type != 0 && (hs[i] != h || !value_test_equality(ty, &vs[i], v)))
                i = (i + 1) & mask;

        return i;
}

inline static size_t
delete(Dict *d, size_t i)
{
        size_t mask = d->size - 1;
        unsigned long h = d->hashes[i] & mask;

        size_t j = i;
        size_t k = (i + 1) & mask;

        while (d->keys[k].type != 0) {
                if ((d->hashes[k] & mask) == h) {
                        j = k;
                }
                k = (k + 1) & mask;
        }

        j &= mask;

        if (i != j) {
                d->keys[i] = d->keys[j];
                d->values[i] = d->values[j];
                d->hashes[i] = d->hashes[j];
        }

        d->hashes[j] = d->keys[j].type = d->values[j].type = 0;
        d->count -= 1;

        return min(i, j);
}

inline static void
grow(Ty *ty, Dict *d)
{
        size_t new_size = d->size << 1;

        unsigned long *hashes = mA(new_size * sizeof (unsigned long));
        Value *keys = mA(new_size * sizeof (Value));
        Value *values = mA(new_size * sizeof (Value));

        memset(keys, 0, new_size * sizeof (Value));

        for (size_t i = 0; i < d->size; ++i) {
                if (d->keys[i].type == 0)
                        continue;
                size_t j = find_spot(ty, new_size, hashes, keys, d->hashes[i], &d->keys[i]);
                hashes[j] = d->hashes[i];
                keys[j] = d->keys[i];
                values[j] = d->values[i];
        }

        mF(d->hashes);
        mF(d->keys);
        mF(d->values);

        d->hashes = hashes;
        d->keys = keys;
        d->values = values;

        d->size = new_size;
}

inline static Value *
put(Ty *ty, Dict *d, size_t i, unsigned long h, Value k, Value v)
{
        if (9*d->count >= 4*d->size) {
                grow(ty, d);
                i = find_spot(ty, d->size, d->hashes, d->keys, h, &k);
        }

        d->hashes[i] = h;
        d->keys[i] = k;
        d->values[i] = v;
        d->count += 1;

        return &d->values[i];
}

Value *
dict_get_value(Ty *ty, Dict *d, Value *key)
{
        unsigned long h = value_hash(ty, key);
        size_t i = find_spot(ty, d->size, d->hashes, d->keys, h, key);

        if (d->keys[i].type != 0)
                return &d->values[i];

        if (d->dflt.type != VALUE_NONE) {
                Value dflt = value_apply_callable(ty, &d->dflt, key);
                GC_STOP();
                Value *v = put(ty, d, i, h, *key, dflt);
                GC_RESUME();
                return v;
        }

        return NULL;
}

bool
dict_has_value(Ty *ty, Dict *d, Value *key)
{
        unsigned long h = value_hash(ty, key);
        size_t i = find_spot(ty, d->size, d->hashes, d->keys, h, key);

        if (d->keys[i].type != 0)
                return true;

        return false;
}

void
dict_put_value(Ty *ty, Dict *d, Value key, Value value)
{
        unsigned long h = value_hash(ty, &key);
        size_t i = find_spot(ty, d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0)
                d->values[i] = value;
        else
                put(ty, d, i, h, key, value);
}

Value *
dict_put_value_with(Ty *ty, Dict *d, Value key, Value v, Value const *f)
{
        unsigned long h = value_hash(ty, &key);
        size_t i = find_spot(ty, d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0) {
                return put(ty, d, i, h, key, vm_eval_function(ty, f, &d->values[i], &v, NULL));
        } else {
                return put(ty, d, i, h, key, v);
        }
}

Value *
dict_put_key_if_not_exists(Ty *ty, Dict *d, Value key)
{
        unsigned long h = value_hash(ty, &key);
        size_t i = find_spot(ty, d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0) {
                return &d->values[i];
        } else if (d->dflt.type != VALUE_NONE) {
                return put(ty, d, i, h, key, value_apply_callable(ty, &d->dflt, &key));
        } else {
                return put(ty, d, i, h, key, NIL);
        }
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

        if (d->dflt.type != VALUE_NONE)
                value_mark(ty, &d->dflt);

        for (size_t i = 0; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        value_mark(ty, &d->keys[i]);
                        value_mark(ty, &d->values[i]);
                }
        }
}

void
dict_free(Ty *ty, Dict *d)
{
        mF(d->hashes);
        mF(d->keys);
        mF(d->values);
}

static Value
dict_default(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc == 0) {
                if (d->dict->dflt.type == VALUE_NONE) {
                        return NIL;
                } else {
                        return d->dict->dflt;
                }
        }

        if (argc != 1)
                zP("dict.default() expects 1 or 0 arguments but got %d", argc);

        if (!CALLABLE(ARG(0)))
                zP("the argument to dict.default() must be callable");

        d->dict->dflt = ARG(0);

        return *d;
}

static Value
dict_contains(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("dict.contains() expects 1 argument but got %d", argc);

        Value *key = &ARG(0);
        unsigned long h = value_hash(ty, key);
        size_t i = find_spot(ty, d->dict->size, d->dict->hashes, d->dict->keys, h, key);

        return BOOLEAN(d->dict->keys[i].type != 0);
}

static Value
dict_keys(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("dict.keys() expects 0 arguments but got %d", argc);

        Value keys = ARRAY(vA());

        gP(&keys);

        for (size_t i = 0; i < d->dict->size; ++i)
                if (d->dict->keys[i].type != 0)
                        vAp(keys.array, d->dict->keys[i]);

        gX();

        return keys;
}

static Value
dict_values(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("dict.values() expects 0 arguments but got %d", argc);

        Value values = ARRAY(vA());

        gP(&values);

        for (size_t i = 0; i < d->dict->size; ++i)
                if (d->dict->keys[i].type != 0)
                        vAp(values.array, d->dict->values[i]);

        gX();

        return values;
}

Dict *
DictClone(Ty *ty, Dict const *d)
{
        Dict *new = dict_new(ty);
        new->dflt = d->dflt;

        NOGC(new);

        for (size_t i = 0; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        dict_put_value(ty, new, d->keys[i], d->values[i]);
                }
        }

        OKGC(new);

        return new;
}

static Value
dict_clone(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("dict.clone() expects 0 arguments but got %d", argc);

        return DICT(DictClone(ty, d->dict));
}

bool
dict_same_keys(Ty *ty, Dict const *d, Dict const *u)
{
        if (d->count != u->count)
                return false;

        for (size_t i = 0; i < d->size;) {
                if (d->keys[i].type == 0) {
                        i += 1;
                        continue;
                }
                size_t j = find_spot(
                        ty,
                        u->size,
                        u->hashes,
                        u->keys,
                        d->hashes[i],
                        &d->keys[i]
                );
                if (u->keys[j].type == 0) {
                        return false;
                }
                i += 1;
        }

        return true;
}

inline static void
copy_unique(Ty *ty, Dict *diff, Dict const *d, Dict const *u)
{
        for (size_t i = 0; i < d->size; ++i) {
                if (d->keys[i].type == 0) {
                        continue;
                }

                size_t j = find_spot(
                        ty,
                        u->size,
                        u->hashes,
                        u->keys,
                        d->hashes[i],
                        &d->keys[i]
                );

                if (u->keys[j].type == 0) {
                        size_t k = find_spot(
                                ty,
                                diff->size,
                                diff->hashes,
                                diff->keys,
                                d->hashes[i],
                                &d->keys[i]
                        );

                        put(ty, diff, k, d->hashes[i], d->keys[i], d->values[i]);
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
                zP("Dict.diff(): expected Dict but got %s", value_show(ty, &u));
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
        if (argc != 1 && argc != 2) {
                zP("dict.intersect() expects 1 or 2 arguments but got %d", argc);
        }

        Value u = ARG(0);
        if (u.type != VALUE_DICT)
                zP("the first argument to dict.intersect() must be a dict");

        if (argc == 1) {
                for (size_t i = 0; i < d->dict->size;) {
                        if (d->dict->keys[i].type == 0) {
                                i += 1;
                                continue;
                        }
                        size_t j = find_spot(
                                ty,
                                u.dict->size,
                                u.dict->hashes,
                                u.dict->keys,
                                d->dict->hashes[i],
                                &d->dict->keys[i]
                        );
                        if (u.dict->keys[j].type == 0) {
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
                for (size_t i = 0; i < d->dict->size;) {
                        if (d->dict->keys[i].type == 0) {
                                i += 1;
                                continue;
                        }
                        size_t j = find_spot(
                                ty,
                                u.dict->size,
                                u.dict->hashes,
                                u.dict->keys,
                                d->dict->hashes[i],
                                &d->dict->keys[i]
                        );
                        if (u.dict->keys[j].type == 0) {
                                i = delete(d->dict, i);
                        } else {
                                d->dict->values[i] = vm_eval_function(
                                        ty,
                                        &f,
                                        &d->dict->values[i],
                                        &u.dict->values[j],
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
        for (size_t i = 0; i < u->size; ++i) {
                if (u->keys[i].type != 0) {
                        dict_put_value(ty, d, u->keys[i], u->values[i]);
                }
        }

        return d;
}

Dict *
DictUpdateWith(Ty *ty, Dict *d, Dict const *u, Value const *f)
{
        for (size_t i = 0; i < u->size; ++i) {
                if (u->keys[i].type != 0) {
                        dict_put_value_with(
                                ty,
                                d,
                                u->keys[i],
                                u->values[i],
                                f
                        );
                }
        }

        return d;
}

static Value
dict_update(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2) {
                zP("dict.update(): expected 1 or 2 arguments but got %d", argc);
        }

        Value u = ARG(0);

        if (u.type != VALUE_DICT) {
                zP("dict.update(): expected Dict but got: %s", VSC(&u));
        }

        return DICT(
                (argc == 1)
              ? DictUpdate(ty, d->dict, u.dict)
              : DictUpdateWith(ty, d->dict, u.dict, &ARG(1))
        );
}

Value
dict_subtract(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2) {
                zP("dict.subtract() expects 1 or 2 arguments but got %d", argc);
        }

        Value u = ARG(0);
        if (u.type != VALUE_DICT)
                zP("the first argument to dict.subtract() must be a dict");

        if (argc == 1) {
                for (size_t i = 0; i < u.dict->size; ++i) {
                        if (u.dict->keys[i].type != 0) {
                                size_t j = find_spot(
                                        ty,
                                        d->dict->size,
                                        d->dict->hashes,
                                        d->dict->keys,
                                        u.dict->hashes[i],
                                        &u.dict->keys[i]
                                );
                                if (d->dict->keys[j].type != 0) {
                                        delete(d->dict, j);
                                }
                        }
                }
        } else {
                Value f = ARG(1);
                if (!CALLABLE(f)) {
                        zP("the second argument to dict.subtract() must be callable");
                }
                for (size_t i = 0; i < u.dict->size; ++i) {
                        if (u.dict->keys[i].type != 0) {
                                size_t j = find_spot(
                                        ty,
                                        d->dict->size,
                                        d->dict->hashes,
                                        d->dict->keys,
                                        u.dict->hashes[i],
                                        &u.dict->keys[i]
                                );
                                if (d->dict->keys[j].type != 0) {
                                        vm_eval_function(
                                                ty,
                                                &f,
                                                &d->dict->values[i],
                                                &u.dict->values[j],
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
        if (argc == 0)
                zP("dict.put(ty) expects at least 1 argument but got 0");

        for (int i = 0; i < argc; ++i) {
                dict_put_value(ty, d->dict, ARG(i), NIL);
        }

        return *d;
}

static Value
dict_remove(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("dict.remove() expects 1 argument but got %d", argc);

        Value k = ARG(0);
        unsigned long h = value_hash(ty, &k);

        size_t i = find_spot(
                ty,
                d->dict->size,
                d->dict->hashes,
                d->dict->keys,
                h,
                &k
        );

        if (d->dict->keys[i].type == 0) {
                return NIL;
        } else {
                Value v = d->dict->values[i];
                delete(d->dict, i);
                return v;
        }
}

static Value
dict_len(Ty *ty, Value *d, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("dict.len() expects 0 arguments but got %d", argc);

        return INTEGER(d->dict->count);
}

DEFINE_METHOD_TABLE(
        { .name = "&",            .func = dict_intersect_copy },
        { .name = "&=",           .func = dict_intersect      },
        { .name = "<<",           .func = dict_put            },
        { .name = "?",            .func = dict_contains       },
        { .name = "clone",        .func = dict_clone          },
        { .name = "contains?",    .func = dict_contains       },
        { .name = "default",      .func = dict_default        },
        { .name = "diff",         .func = dict_diff           },
        { .name = "has?",         .func = dict_contains       },
        { .name = "intersect",    .func = dict_intersect      },
        { .name = "keys",         .func = dict_keys           },
        { .name = "len",          .func = dict_len            },
        { .name = "put",          .func = dict_put            },
        { .name = "remove",       .func = dict_remove         },
        { .name = "update",       .func = dict_update         },
        { .name = "values",       .func = dict_values         },
        { .name = "~=",           .func = dict_remove         },
);

DEFINE_METHOD_LOOKUP(dict);
DEFINE_METHOD_COMPLETER(dict);
