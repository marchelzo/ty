#ifndef BLOB_H_INCLUDED
#define BLOB_H_INCLUDED

#include "value.h"

void
build_blob_method_table(void);

BuiltinMethod *
get_blob_method(char const *);

BuiltinMethod *
get_blob_method_i(int);

int
blob_get_completions(Ty *ty, char const *prefix, char **out, int max);

Value
blob_get(Ty *ty, Value *blob, int argc, Value *kwargs);

#endif
