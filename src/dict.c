#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "alloc.h"
#include "util.h"
#include "value.h"
#include "dict.h"
#include "log.h"
#include "vm.h"
#include "gc.h"
#include "vec.h"

#define INITIAL_SIZE 16
#define POOL_MAX (1ULL << 18)

struct dead {
        size_t size;
        unsigned long *hashes;
        struct value *keys;
        struct value *values;
};

static vec(struct dict) dp;

struct dict *
dict_new(void)
{
        struct dict *d = gc_alloc_object(sizeof *d, GC_DICT);

        if (dp.count != 0) {
                *d = *vec_pop(dp);
        } else {
                NOGC(d);
                d->size = INITIAL_SIZE;
                d->hashes = gc_alloc(sizeof (unsigned long [INITIAL_SIZE]));
                d->keys = gc_alloc(sizeof (struct value [INITIAL_SIZE]));
                d->values = gc_alloc(sizeof (struct value [INITIAL_SIZE]));
                OKGC(d);
        }


        d->count = 0;
        d->dflt = NONE;
        memset(d->keys, 0, sizeof (struct value [d->size]));

        return d;
}

inline static size_t
find_spot(size_t size, unsigned long const *hs, struct value const *vs, unsigned long h, struct value const *v)
{
        size_t mask = size - 1;
        size_t i = h & mask;

        while (vs[i].type != 0 && (hs[i] != h || !value_test_equality(&vs[i], v)))
                i = (i + 1) & mask;

        return i;
}

inline static size_t
delete(struct dict *d, size_t i)
{
        size_t mask = d->size - 1;
        unsigned long h = d->hashes[i] & mask;

        size_t j = i;
        while ((d->hashes[(j + 1) & mask] & mask) == h && d->keys[(j + 1) & mask].type != 0)
                j = (j + 1) & mask;

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
grow(struct dict *d)
{
        size_t oldsz = d->size;
        d->size <<= 2;

        unsigned long *hashes = gc_resize(NULL, sizeof (unsigned long [d->size]));
        struct value *keys = gc_resize(NULL, sizeof (struct value [d->size]));
        struct value *values = gc_resize(NULL, sizeof (struct value [d->size]));

        memset(keys, 0, sizeof (struct value [d->size]));
        
        for (size_t i = 0; i < oldsz; ++i) {
                if (d->keys[i].type == 0)
                        continue;
                size_t j = find_spot(d->size, hashes, keys, d->hashes[i], &d->keys[i]);
                hashes[j] = d->hashes[i];
                keys[j] = d->keys[i];
                values[j] = d->values[i];
        }

        free(d->hashes);
        free(d->keys);
        free(d->values);

        d->hashes = hashes;
        d->keys = keys;
        d->values = values;
}

inline static struct value *
put(struct dict *d, size_t i, unsigned long h, struct value k, struct value v)
{
        if (4 * d->count >= d->size) {
                grow(d);
                i = find_spot(d->size, d->hashes, d->keys, h, &k);
        }

        d->hashes[i] = h;
        d->keys[i] = k;
        d->values[i] = v;
        d->count += 1;

        return &d->values[i];
}

struct value *
dict_get_value(struct dict *d, struct value *key)
{
        unsigned long h = value_hash(key);
        size_t i = find_spot(d->size, d->hashes, d->keys, h, key);

        if (d->keys[i].type != 0)
                return &d->values[i];

        if (d->dflt.type != VALUE_NONE) {
                struct value dflt = value_apply_callable(&d->dflt, key);
                return put(d, i, h, *key, dflt);
        }

        return NULL;
}

void
dict_put_value(struct dict *d, struct value key, struct value value)
{
        unsigned long h = value_hash(&key);
        size_t i = find_spot(d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0)
                d->values[i] = value;
        else
                put(d, i, h, key, value);
}

struct value *
dict_put_value_with(struct dict *d, struct value key, struct value v, struct value const *f)
{
        unsigned long h = value_hash(&key);
        size_t i = find_spot(d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0) {
                return put(d, i, h, key, vm_eval_function(f, &d->values[i], &v, NULL));
        } else {
                return put(d, i, h, key, v);
        }
}

struct value *
dict_put_key_if_not_exists(struct dict *d, struct value key)
{
        unsigned long h = value_hash(&key);
        size_t i = find_spot(d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0) {
                return &d->values[i];
        } else if (d->dflt.type != VALUE_NONE) {
                return put(d, i, h, key, value_apply_callable(&d->dflt, &key));
        } else {
                return put(d, i, h, key, NIL);
        }
}

struct value *
dict_put_member_if_not_exists(struct dict *d, char const *member)
{
        return dict_put_key_if_not_exists(d, STRING_NOGC(member, strlen(member)));
}

struct value *
dict_get_member(struct dict *d, char const *key)
{
        struct value string = STRING_NOGC(key, strlen(key));
        return dict_get_value(d, &string);
}

void
dict_put_member(struct dict *d, char const *key, struct value value)
{
        struct value string = STRING_NOGC(key, strlen(key));
        dict_put_value(d, string, value);
}

void
dict_mark(struct dict *d)
{
        if (MARKED(d)) return;

        MARK(d);

        if (d->dflt.type != VALUE_NONE)
                value_mark(&d->dflt);

        for (size_t i = 0; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        value_mark(&d->keys[i]);
                        value_mark(&d->values[i]);
                }
        }
}

void
dict_free(struct dict *d)
{
        if (dp.count < POOL_MAX) {
                vec_push(dp, *d);
        } else {
                free(d->hashes);
                free(d->keys);
                free(d->values);
        }
}

static struct value
dict_default(struct value *d, value_vector *args)
{
        if (args->count == 0) {
                if (d->dict->dflt.type == VALUE_NONE) {
                        return NIL;
                } else {
                        return d->dict->dflt;
                }
        }

        if (args->count != 1)
                vm_panic("dict.default() expects 1 or 0 arguments but got %zu", args->count);

        if (!CALLABLE(args->items[0]))
                vm_panic("the argument to dict.default() must be callable");

        d->dict->dflt = args->items[0];

        return *d;
}

static struct value
dict_contains(struct value *d, value_vector *args)
{
        if (args->count != 1)
                vm_panic("dict.contains() expects 1 argument but got %zu", args->count);

        struct value *key = &args->items[0];
        unsigned long h = value_hash(key);
        size_t i = find_spot(d->dict->size, d->dict->hashes, d->dict->keys, h, key);

        return BOOLEAN(d->dict->keys[i].type != 0);
}

static struct value
dict_keys(struct value *d, value_vector *args)
{
        if (args->count != 0)
                vm_panic("dict.keys() expects 0 arguments but got %zu", args->count);

        struct value keys = ARRAY(value_array_new());

        gc_push(&keys);

        for (size_t i = 0; i < d->dict->size; ++i)
                if (d->dict->keys[i].type != 0)
                        value_array_push(keys.array, d->dict->keys[i]);

        gc_pop();

        return keys;
}

static struct value
dict_values(struct value *d, value_vector *args)
{
        if (args->count != 0)
                vm_panic("dict.values() expects 0 arguments but got %zu", args->count);

        struct value values = ARRAY(value_array_new());

        gc_push(&values);

        for (size_t i = 0; i < d->dict->size; ++i)
                if (d->dict->keys[i].type != 0)
                        value_array_push(values.array, d->dict->values[i]);

        gc_pop();

        return values;
}

struct value
dict_clone(struct value *d, value_vector *args)
{
        if (args->count != 0)
                vm_panic("dict.clone() expects 0 arguments but got %zu", args->count);

        struct dict *new = dict_new();
        new->dflt = d->dict->dflt;
        NOGC(new);

        for (size_t i = 0; i < d->dict->size; ++i)
                if (d->dict->keys[i].type != 0)
                        dict_put_value(new, d->dict->keys[i], d->dict->values[i]);

        OKGC(new);
        return DICT(new);
}

struct value
dict_intersect(struct value *d, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("dict.intersect() expects 1 or 2 arguments but got %zu", args->count);
        }

        struct value u = args->items[0];
        if (u.type != VALUE_DICT)
                vm_panic("the first argument to dict.intersect() must be a dict");

        if (args->count == 1) {
                for (size_t i = 0; i < d->dict->size;) {
                        if (d->dict->keys[i].type == 0) {
                                i += 1;
                                continue;
                        }
                        size_t j = find_spot(
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
                struct value f = args->items[1];
                if (!CALLABLE(f)) {
                        vm_panic("the second argument to dict.intersect() must be callable");
                }
                for (size_t i = 0; i < d->dict->size;) {
                        if (d->dict->keys[i].type == 0) {
                                i += 1;
                                continue;
                        }
                        size_t j = find_spot(
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

struct value
dict_intersect_copy(struct value *d, value_vector *args)
{
        struct value copy = dict_clone(d, &((value_vector){ .count = 0 }));
        return dict_intersect(&copy, args);
}

struct value
dict_update(struct value *d, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("dict.update() expects 1 argument but got %zu", args->count);
        }

        struct value u = args->items[0];
        if (u.type != VALUE_DICT)
                vm_panic("the first argument to dict.update() must be a dict");

        if (args->count == 1) {
                for (size_t i = 0; i < u.dict->size; ++i) {
                        if (u.dict->keys[i].type != 0) {
                                dict_put_value(d->dict, u.dict->keys[i], u.dict->values[i]);
                        }
                }
        } else {
                struct value f = args->items[1];
                if (!CALLABLE(f)) {
                        vm_panic("the second argument to dict.update() must be callable");
                }
                for (size_t i = 0; i < u.dict->size; ++i) {
                        if (u.dict->keys[i].type != 0) {
                                dict_put_value_with(
                                        d->dict,
                                        u.dict->keys[i],
                                        u.dict->values[i],
                                        &f
                                );
                        }
                }

        }

        return *d;
}

struct value
dict_subtract(struct value *d, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("dict.subtract() expects 1 or 2 arguments but got %zu", args->count);
        }

        struct value u = args->items[0];
        if (u.type != VALUE_DICT)
                vm_panic("the first argument to dict.subtract() must be a dict");

        if (args->count == 1) {
                for (size_t i = 0; i < u.dict->size; ++i) {
                        if (u.dict->keys[i].type != 0) {
                                size_t j = find_spot(
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
                struct value f = args->items[1];
                if (!CALLABLE(f)) {
                        vm_panic("the second argument to dict.subtract() must be callable");
                }
                for (size_t i = 0; i < u.dict->size; ++i) {
                        if (u.dict->keys[i].type != 0) {
                                size_t j = find_spot(
                                        d->dict->size,
                                        d->dict->hashes,
                                        d->dict->keys,
                                        u.dict->hashes[i],
                                        &u.dict->keys[i]
                                );
                                if (d->dict->keys[j].type != 0) {
                                        vm_eval_function(
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

static struct value
dict_put(struct value *d, value_vector *args)
{
        if (args->count == 0)
                vm_panic("dict.put() expects at least 1 argument but got 0");

        for (int i = 0; i < args->count; ++i) {
                dict_put_value(d->dict, args->items[i], NIL);
        }

        return *d;
}

static struct value
dict_remove(struct value *d, value_vector *args)
{
        if (args->count != 1)
                vm_panic("dict.remove() expects 1 argument but got %zu", args->count);

        struct value k = args->items[0];
        unsigned long h = value_hash(&k);

        size_t i = find_spot(
                d->dict->size,
                d->dict->hashes,
                d->dict->keys,
                h,
                &k
        );

        if (d->dict->keys[i].type == 0) {
                return NIL;
        } else {
                struct value v = d->dict->values[i];
                delete(d->dict, i);
                return v;
        }
}

static struct value
dict_len(struct value *d, value_vector *args)
{
        if (args->count != 0)
                vm_panic("dict.len() expects 0 arguments but got %zu", args->count);

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
