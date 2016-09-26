#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "alloc.h"
#include "util.h"
#include "value.h"
#include "dict.h"
#include "log.h"
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
dict_item_count(struct dict const *obj)
{
        return obj->count;
}

struct dict *
dict_new(void)
{
        struct dict *dict = gc_alloc_object(sizeof *dict, GC_DICT);

        for (int i = 0; i < DICT_NUM_BUCKETS; ++i)
                dict->buckets[i] = NULL;

        dict->count = 0;

        return dict;
}

struct value *
dict_get_value(struct dict const *obj, struct value const *key)
{
        unsigned bucket_index = value_hash(key) % DICT_NUM_BUCKETS;
        return bucket_find(obj->buckets[bucket_index], key);
}

void
dict_put_value(struct dict *obj, struct value key, struct value value)
{
        unsigned bucket_index = value_hash(&key) % DICT_NUM_BUCKETS;
        struct value *valueptr = bucket_find(obj->buckets[bucket_index], &key);
        
        if (valueptr == NULL) {
                obj->count += 1;
                obj->buckets[bucket_index] = mknode(key, value, obj->buckets[bucket_index]);
        } else {
                *valueptr = value;
        }
}

struct value *
dict_put_key_if_not_exists(struct dict *obj, struct value key)
{
        unsigned bucket_index = value_hash(&key) % DICT_NUM_BUCKETS;
        struct value *valueptr = bucket_find(obj->buckets[bucket_index], &key);

        if (valueptr != NULL) {
                return valueptr;
        } else {
                obj->count += 1;
                obj->buckets[bucket_index] = mknode(key, NIL, obj->buckets[bucket_index]);
                return &obj->buckets[bucket_index]->value;
        }
}

struct value *
dict_put_member_if_not_exists(struct dict *obj, char const *member)
{
        return dict_put_key_if_not_exists(obj, STRING_NOGC(member, strlen(member)));
}

struct value *
dict_get_member(struct dict const *obj, char const *key)
{
        struct value string = STRING_NOGC(key, strlen(key));
        return dict_get_value(obj, &string);
}

void
dict_put_member(struct dict *obj, char const *key, struct value value)
{
        struct value string = STRING_NOGC(key, strlen(key));
        dict_put_value(obj, string, value);
}

void
dict_mark(struct dict *obj)
{
        MARK(obj);

        for (int i = 0; i < DICT_NUM_BUCKETS; ++i) {
                for (struct dict_node *node = obj->buckets[i]; node != NULL; node = node->next) {
                        value_mark(&node->key);
                        value_mark(&node->value);
                }
        }
}

void
dict_free(struct dict *obj)
{
        for (int i = 0; i < DICT_NUM_BUCKETS; ++i) {
                for (struct dict_node *node = obj->buckets[i]; node != NULL;) {
                        struct dict_node *next = node->next;
                        free(node);
                        node = next;
                }
        }
}

