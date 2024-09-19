#ifndef ARRAY_H_INCLUDED
#define ARRAY_H_INCLUDED

#include "value.h"

BuiltinMethod *
get_array_method(char const *);

int
array_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
