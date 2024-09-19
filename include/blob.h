#ifndef BLOB_H_INCLUDED
#define BLOB_H_INCLUDED

#include "value.h"

BuiltinMethod *
get_blob_method(char const *);

int
blob_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
