#ifndef STRING_H_INCLUDED
#define STRING_H_INCLUDED

#include "value.h"

struct value (*get_string_method(char const *))(struct value *, int);

int
string_get_completions(char const *prefix, char **out, int max);

#endif
