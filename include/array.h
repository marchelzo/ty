#ifndef ARRAY_H_INCLUDED
#define ARRAY_H_INCLUDED

#include "value.h"

struct value (*get_array_method(char const *))(struct value *, value_vector *);

#endif
