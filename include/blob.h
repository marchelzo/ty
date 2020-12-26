#ifndef BLOB_H_INCLUDED
#define BLOB_H_INCLUDED

#include "value.h"

struct value (*get_blob_method(char const *))(struct value *, int);

#endif
