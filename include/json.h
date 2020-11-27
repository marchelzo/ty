#ifndef JSON_H_INCLUDED
#define JSON_H_INCLUDED

struct value
json_parse(char const *s, int n);

struct value
json_encode(struct value const *v);

#endif
