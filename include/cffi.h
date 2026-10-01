#ifndef CFFI_H_INCLUDED
#define CFFI_H_INCLUDED

#include <ffi.h>

#include "value.h"

bool
ptr_from_ty(Ty *ty, Value const *v, void **out);


















Value
cffi_load_n(Ty *ty, int argc, Value *kwargs);




Value
cffi_fast_call(Ty *ty, Value const *fun, int argc, Value *kwargs);















#endif
