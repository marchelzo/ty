#ifndef ARRAY_H_INCLUDED
#define ARRAY_H_INCLUDED

#include "value.h"

void
build_array_method_table(void);

BuiltinMethod *
get_array_method(char const *);

BuiltinMethod *
get_array_method_i(int);

int
array_get_completions(Ty *ty, char const *prefix, char **out, int max);

SortOrder
sort_order(Ty *ty, Value *kwargs, char const *who);

int
sort_order_cmp(Ty *ty, SortOrder const *o, Value const *a, Value const *b);

#endif
