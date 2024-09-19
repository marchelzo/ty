#ifndef STRING_H_INCLUDED
#define STRING_H_INCLUDED

#include "value.h"

BuiltinMethod *
get_string_method(char const *);

int
string_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
