#ifndef DICT_H_INCLUDED
#define DICT_H_INCLUDED

#include "ty.h"
#include "value.h"

inline static Dict *
dict_new(Ty *ty)
{
        return mAo0(sizeof (Dict), GC_DICT);
}

Value *
dict_get_value(Ty *ty, Dict *obj, Value *key);

void
dict_put_value(Ty *ty, Dict *obj, Value key, Value value);

bool
dict_has_value(Ty *ty, Dict *d, Value *key);

Value *
dict_get_member(Ty *ty, Dict *obj, char const *key);

void
dict_put_member(Ty *ty, Dict *obj, char const *key, Value value);

bool
dict_same_keys(Ty *ty, Dict const *d, Dict const *u);

Value *
dict_put_key_if_not_exists(Ty *ty, Dict *obj, Value key);

Value *
dict_put_member_if_not_exists(Ty *ty, Dict *obj, char const *member);

Value
dict_intersect(Ty *ty, Value *d, int argc, Value *kwargs);

Value
dict_subtract(Ty *ty, Value *d, int argc, Value *kwargs);

Dict *
DictClone(Ty *ty, Dict const *d);

Dict *
DictUpdateWith(Ty *ty, Dict *d, Dict const *u, Value const *f);

Dict *
DictUpdate(Ty *ty, Dict *d, Dict const *u);

void
dict_mark(Ty *ty, Dict *obj);

void
dict_free(Ty *ty, Dict *obj);

void
build_dict_method_table(void);

BuiltinMethod *
get_dict_method(char const *);

BuiltinMethod *
get_dict_method_i(int);

int
dict_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
