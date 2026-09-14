#ifndef STRING_H_INCLUDED
#define STRING_H_INCLUDED

#include "value.h"

typedef enum {
        STRING_TEXT,
        STRING_ESCAPE,
        STRING_INVALID
} StringPart;

typedef void StringEmit(Ty *, Bytes, StringPart, void *);

void
str_escape(Ty *ty, Bytes s, char quote, StringEmit *emit, void *ctx);

void
build_string_method_table(void);

BuiltinMethod *
get_string_method(char const *);

BuiltinMethod *
get_string_method_i(int);

int
string_get_completions(Ty *ty, char const *prefix, char **out, int max);

Value
string_char(Ty *ty, Value *string, int argc, Value *kwargs);

Value
string_match(Ty *ty, Value *string, int argc, Value *kwargs);

Value
string_length(Ty *ty, Value *string, int argc, Value *kwargs);

Value
string_slice(Ty *ty, Value *string, int argc, Value *kwargs);

#endif
