#ifndef DICT_H_INCLUDED
#define DICT_H_INCLUDED

#include "value.h"

struct dict *
dict_new(void);

struct value *
dict_get_value(struct dict *obj, struct value *key);

void
dict_put_value(struct dict *obj, struct value key, struct value value);

bool
dict_has_value(struct dict *d, struct value *key);

struct value *
dict_get_member(struct dict *obj, char const *key);

void
dict_put_member(struct dict *obj, char const *key, struct value value);

bool
dict_same_keys(struct dict const *d, struct dict const *u);

struct value *
dict_put_key_if_not_exists(struct dict *obj, struct value key);

struct value *
dict_put_member_if_not_exists(struct dict *obj, char const *member);

struct value
dict_update(struct value *d, int argc);

struct value
dict_intersect(struct value *d, int argc);

struct value
dict_subtract(struct value *d, int argc);

struct value
dict_clone(struct value *d, int argc);

void
dict_mark(struct dict *obj);

void
dict_free(struct dict *obj);

struct value (*get_dict_method(char const *))(struct value *, int);

#endif
