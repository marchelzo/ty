#ifndef JSON_H_INCLUDED
#define JSON_H_INCLUDED

#include "ty.h"

Value
json_parse(Ty *ty, char const *s, usize n);

Value
json_parse_xD(Ty *ty, char const *s, usize n);

Value
json_encode(Ty *ty, Value const *v);

bool
json_dump(Ty *ty, Value const  *v, byte_vector *out);

#endif
