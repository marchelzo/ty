#ifndef OBJECT_H_INCLUDED
#define OBJECT_H_INCLUDED

#include "value.h"

struct object;

struct object *
object_new(void);

size_t
object_item_count(struct object const *obj);

struct value *
object_get_value(struct object const *obj, struct value const *key);

void
object_put_value(struct object *obj, struct value key, struct value value);

struct value *
object_get_member(struct object const *obj, char const *key);

void
object_put_member(struct object *obj, char const *key, struct value value);

struct value *
object_put_key_if_not_exists(struct object *obj, struct value key);

struct value *
object_put_member_if_not_exists(struct object *obj, char const *member);

struct value
object_keys_array(struct object *obj);

void
object_mark(struct object *obj);

void
object_sweep(void);

void
object_gc_reset(void);

#endif
