#ifndef JSON_H_INCLUDED
#define JSON_H_INCLUDED

struct value
json_parse(Ty *ty, char const *s, int n);

struct value
json_encode(Ty *ty, struct value const *v);

#endif
