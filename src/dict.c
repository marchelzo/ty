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

struct dict *
dict_new(void)
{
        struct dict *dict = gc_alloc_object(sizeof *dict, GC_DICT);

        dict->size = 16;
        dict->count = 0;
        dict->dflt = NIL;
        dict->hashes = alloc(sizeof (unsigned long [16]));
        dict->keys = alloc(sizeof (struct value [16]));
        dict->values = alloc(sizeof (struct value [16]));

        memset(dict->keys, 0, sizeof (struct value [16]));

        return dict;
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

inline static void
grow(struct dict *d)
{
        size_t oldsz = d->size;
        d->size = oldsz << 2;

        unsigned long *hashes = alloc(sizeof (unsigned long [d->size]));
        struct value *keys = alloc(sizeof (struct value [d->size]));
        struct value *values = alloc(sizeof (struct value [d->size]));

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

        if (d->dflt.type != VALUE_NIL) {
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
dict_put_key_if_not_exists(struct dict *d, struct value key)
{
        unsigned long h = value_hash(&key);
        size_t i = find_spot(d->size, d->hashes, d->keys, h, &key);

        if (d->keys[i].type != 0) {
                return &d->values[i];
        } else if (d->dflt.type != VALUE_NIL) {
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

        if (d->dflt.type != VALUE_NIL)
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
        free(d->hashes);
        free(d->keys);
        free(d->values);
}

static struct value
dict_default(struct value *d, value_vector *args)
{
        if (args->count == 0)
                return d->dict->dflt;

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
                vm_panic("dict.keys() expects 0 argument but got %zu", args->count);

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
                vm_panic("dict.values() expects 0 argument but got %zu", args->count);

        struct value values = ARRAY(value_array_new());

        gc_push(&values);

        for (size_t i = 0; i < d->dict->size; ++i)
                if (d->dict->keys[i].type != 0)
                        value_array_push(values.array, d->dict->values[i]);

        gc_pop();

        return values;
}

static struct value
dict_len(struct value *d, value_vector *args)
{
        if (args->count != 0)
                vm_panic("dict.len() expects 0 argument but got %zu", args->count);

        return INTEGER(d->dict->count);
}

DEFINE_METHOD_TABLE(
        { .name = "contains?",    .func = dict_contains      },
        { .name = "default",      .func = dict_default       },
        { .name = "has?",         .func = dict_contains      },
        { .name = "keys",         .func = dict_keys          },
        { .name = "len",          .func = dict_len           },
        { .name = "values",       .func = dict_values        },
);

DEFINE_METHOD_LOOKUP(dict);
