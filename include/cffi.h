#ifndef CFFI_H_INCLUDED
#define CFFI_H_INCLUDED

#include <ffi.h>

#include "value.h"

struct value
cffi_cif(int argc, struct value *kwargs);

struct value
cffi_new(int argc, struct value *kwargs);

struct value
cffi_size(int argc, struct value *kwargs);

struct value
cffi_alloc(int argc, struct value *kwargs);

struct value
cffi_realloc(int argc, struct value *kwargs);

struct value
cffi_clone(int argc, struct value *kwargs);

struct value
cffi_as_str(int argc, struct value *kwargs);

struct value
cffi_free(int argc, struct value *kwargs);

struct value
cffi_addr(int argc, struct value *kwargs);

struct value
cffi_member(int argc, struct value *kwargs);

struct value
cffi_pmember(int argc, struct value *kwargs);

struct value
cffi_load(int argc, struct value *kwargs);

struct value
cffi_load_n(int argc, struct value *kwargs);

struct value
cffi_call(int argc, struct value *kwargs);

struct value
cffi_dlsym(int argc, struct value *kwargs);

struct value
cffi_dlopen(int argc, struct value *kwargs);

struct value
cffi_struct(int argc, struct value *kwargs);

struct value
cffi_blob(int argc, struct value *kwargs);

struct value
cffi_store(int argc, struct value *kwargs);

struct value
cffi_str(int argc, struct value *kwargs);

struct value
cffi_closure(int argc, struct value *kwargs);

struct value
cffi_closure_free(int argc, struct value *kwargs);

#endif
