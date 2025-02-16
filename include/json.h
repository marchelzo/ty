#ifndef JSON_H_INCLUDED
#define JSON_H_INCLUDED

#include "ty.h"

struct value
json_parse(Ty *ty, char const *s, int n);

struct value
json_encode(Ty *ty, struct value const *v);

bool
json_dump(Ty *ty, Value const  *v, byte_vector *out);

#endif
