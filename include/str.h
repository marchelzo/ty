#ifndef STRING_H_INCLUDED
#define STRING_H_INCLUDED

#include "value.h"

void
build_string_method_table(void);

BuiltinMethod *
get_string_method(char const *);

BuiltinMethod *
get_string_method_i(int);

int
string_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
