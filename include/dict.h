#ifndef DICT_H_INCLUDED
#define DICT_H_INCLUDED

#include "ty.h"
#include "value.h"

struct dict *
dict_new(Ty *ty);

struct value *
dict_get_value(Ty *ty, struct dict *obj, struct value *key);

void
dict_put_value(Ty *ty, struct dict *obj, struct value key, struct value value);

bool
dict_has_value(Ty *ty, struct dict *d, struct value *key);

struct value *
dict_get_member(Ty *ty, struct dict *obj, char const *key);

void
dict_put_member(Ty *ty, struct dict *obj, char const *key, struct value value);

bool
dict_same_keys(Ty *ty, struct dict const *d, struct dict const *u);

struct value *
dict_put_key_if_not_exists(Ty *ty, struct dict *obj, struct value key);

struct value *
dict_put_member_if_not_exists(Ty *ty, struct dict *obj, char const *member);

struct value
dict_intersect(Ty *ty, struct value *d, int argc, struct value *kwargs);

struct value
dict_subtract(Ty *ty, struct value *d, int argc, struct value *kwargs);

Dict *
DictClone(Ty *ty, Dict const *d);

Dict *
DictUpdateWith(Ty *ty, Dict *d, Dict const *u, Value const *f);

Dict *
DictUpdate(Ty *ty, Dict *d, Dict const *u);

void
dict_mark(Ty *ty, struct dict *obj);

void
dict_free(Ty *ty, struct dict *obj);

void
build_dict_method_table(void);

BuiltinMethod *
get_dict_method(char const *);

BuiltinMethod *
get_dict_method_i(int);

int
dict_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
