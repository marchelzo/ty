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

static struct dict_node *
mknode(struct value key, struct value value, struct dict_node *next)
{
        struct dict_node *node = gc_alloc(sizeof *node);

        node->key = key;
        node->value = value;
        node->next = next;

        return node;
}

static struct value *
bucket_find(struct dict_node *node, struct value const *key)
{
        while (node != NULL) {
                if (value_test_equality(&node->key, key))
                        return &node->value;
                else
                        node = node->next;
        }

        return NULL;
}

size_t
dict_item_count(struct dict const *d)
{
        return d->count;
}

struct dict *
dict_new(void)
{
        struct dict *dict = gc_alloc_object(sizeof *dict, GC_DICT);

        for (int i = 0; i < DICT_NUM_BUCKETS; ++i)
                dict->buckets[i] = NULL;

        dict->count = 0;
        dict->dflt = NULL;

        return dict;
}

struct value *
dict_get_value(struct dict const *d, struct value const *key)
{
        unsigned bucket_index = value_hash(key) % DICT_NUM_BUCKETS;
        struct value *v = bucket_find(d->buckets[bucket_index], key);
        return (v != NULL) ? v : d->dflt;
}

void
dict_put_value(struct dict *d, struct value key, struct value value)
{
        unsigned bucket_index = value_hash(&key) % DICT_NUM_BUCKETS;
        struct value *valueptr = bucket_find(d->buckets[bucket_index], &key);
        
        if (valueptr == NULL) {
                d->count += 1;
                d->buckets[bucket_index] = mknode(key, value, d->buckets[bucket_index]);
        } else {
                *valueptr = value;
        }
}

struct value *
dict_put_key_if_not_exists(struct dict *d, struct value key)
{
        unsigned bucket_index = value_hash(&key) % DICT_NUM_BUCKETS;
        struct value *valueptr = bucket_find(d->buckets[bucket_index], &key);
        struct value v = (d->dflt == NULL) ? NIL : *d->dflt;

        if (valueptr != NULL) {
                return valueptr;
        } else {
                d->count += 1;
                d->buckets[bucket_index] = mknode(key, v, d->buckets[bucket_index]);
                return &d->buckets[bucket_index]->value;
        }
}

struct value *
dict_put_member_if_not_exists(struct dict *d, char const *member)
{
        return dict_put_key_if_not_exists(d, STRING_NOGC(member, strlen(member)));
}

struct value *
dict_get_member(struct dict const *d, char const *key)
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
        MARK(d);

        if (d->dflt != NULL)
                value_mark(d->dflt);

        for (int i = 0; i < DICT_NUM_BUCKETS; ++i) {
                for (struct dict_node *node = d->buckets[i]; node != NULL; node = node->next) {
                        value_mark(&node->key);
                        value_mark(&node->value);
                }
        }
}

void
dict_free(struct dict *d)
{
        free(d->dflt);

        for (int i = 0; i < DICT_NUM_BUCKETS; ++i) {
                for (struct dict_node *node = d->buckets[i]; node != NULL;) {
                        struct dict_node *next = node->next;
                        free(node);
                        node = next;
                }
        }
}

static struct value
dict_default(struct value *d, value_vector *args)
{
        if (args->count == 0)
                return (d->dict->dflt == NULL ? NIL : *d->dict->dflt);

        if (args->count != 1)
                vm_panic("dict.default() expects 1 or 0 arguments but got %zu", args->count);

        if (d->dict->dflt == NULL)
                d->dict->dflt = alloc(sizeof (struct value));

        *d->dict->dflt = args->items[0];

        return *d;
}

DEFINE_METHOD_TABLE(
        { .name = "default",      .func = dict_default       },
);

DEFINE_METHOD_LOOKUP(dict);
