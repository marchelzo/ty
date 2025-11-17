#ifndef CFFI_H_INCLUDED
#define CFFI_H_INCLUDED

#include <ffi.h>

#include "value.h"

Value
cffi_cif(Ty *ty, int argc, Value *kwargs);

Value
cffi_new(Ty *ty, int argc, Value *kwargs);

Value
cffi_size(Ty *ty, int argc, Value *kwargs);

Value
cffi_alloc(Ty *ty, int argc, Value *kwargs);

Value
cffi_realloc(Ty *ty, int argc, Value *kwargs);

Value
cffi_clone(Ty *ty, int argc, Value *kwargs);

Value
cffi_as_str(Ty *ty, int argc, Value *kwargs);

Value
cffi_free(Ty *ty, int argc, Value *kwargs);

Value
cffi_auto(Ty *ty, int argc, Value *kwargs);

Value
cffi_addr(Ty *ty, int argc, Value *kwargs);

Value
cffi_member(Ty *ty, int argc, Value *kwargs);

Value
cffi_pmember(Ty *ty, int argc, Value *kwargs);

Value
cffi_load(Ty *ty, int argc, Value *kwargs);

Value
cffi_load_n(Ty *ty, int argc, Value *kwargs);

Value
cffi_store_atomic(Ty *ty, int argc, Value *kwargs);

Value
cffi_load_atomic(Ty *ty, int argc, Value *kwargs);

Value
cffi_call(Ty *ty, int argc, Value *kwargs);

Value
cffi_fast_call(Ty *ty, Value const *fun, int argc, Value *kwargs);

Value
cffi_fun(Ty *ty, int argc, Value *kwargs);

Value
cffi_dlsym(Ty *ty, int argc, Value *kwargs);

Value
cffi_dlopen(Ty *ty, int argc, Value *kwargs);

Value
cffi_dlerror(Ty *ty, int argc, Value *kwargs);

Value
cffi_struct(Ty *ty, int argc, Value *kwargs);

Value
cffi_blob(Ty *ty, int argc, Value *kwargs);

Value
cffi_store(Ty *ty, int argc, Value *kwargs);

Value
cffi_c_str(Ty *ty, int argc, Value *kwargs);

Value
cffi_str(Ty *ty, int argc, Value *kwargs);

Value
cffi_closure(Ty *ty, int argc, Value *kwargs);

Value
cffi_closure_free(Ty *ty, int argc, Value *kwargs);

#endif
