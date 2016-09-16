#ifndef FUNCTIONS_H_INCLUDED
#define FUNCTIONS_H_INCLUDED

#include "value.h"

struct value
builtin_print(value_vector *args);

struct value
builtin_rand(value_vector *args);

struct value
builtin_int(value_vector *args);

struct value
builtin_float(value_vector *args);

struct value
builtin_str(value_vector *args);

struct value
builtin_bool(value_vector *args);

struct value
builtin_regex(value_vector *args);

struct value
builtin_blob(value_vector *args);

struct value
builtin_max(value_vector *args);

struct value
builtin_min(value_vector *args);

struct value
builtin_read(value_vector *args);

struct value
builtin_getenv(value_vector *args);

struct value
builtin_setenv(value_vector *args);

struct value
builtin_json_parse(value_vector *args);

struct value
builtin_os_open(value_vector *args);

struct value
builtin_os_close(value_vector *args);

struct value
builtin_os_read(value_vector *args);

struct value
builtin_os_write(value_vector *args);

struct value
builtin_os_listdir(value_vector *args);

struct value
builtin_os_spawn(value_vector *args);

struct value
builtin_errno_get(value_vector *args);

struct value
builtin_errno_str(value_vector *args);

#endif
