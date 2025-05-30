#ifndef CFFI_H_INCLUDED
#define CFFI_H_INCLUDED

#include <ffi.h>

#include "value.h"

struct value
cffi_cif(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_new(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_size(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_alloc(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_realloc(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_clone(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_as_str(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_free(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_auto(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_addr(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_member(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_pmember(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_load(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_load_n(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_store_atomic(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_load_atomic(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_call(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_dlsym(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_dlopen(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_dlerror(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_struct(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_blob(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_store(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_c_str(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_str(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_closure(Ty *ty, int argc, struct value *kwargs);

struct value
cffi_closure_free(Ty *ty, int argc, struct value *kwargs);

#endif
