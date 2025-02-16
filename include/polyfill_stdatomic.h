#ifndef POLYFILL_STDATOMIC_H_INCLUDED
#define POLYFILL_STDATOMIC_H_INCLUDED 1

#if defined(WIN32) || defined(_WIN32)
#define _Atomic volatile
#define _Atomic(T) T volatile
#define atomic_bool volatile bool
#define atomic_uint_least16_t volatile uint_least16_t
#define atomic_uint64_t volatile uint64_t

#define atomic_load_explicit(A, B) *(A)
#define atomic_store_explicit(A, B, C) *(A) = (B)
#define atomic_fetch_add_explicit(A, B, C) *(A) += (B)
#define atomic_fetch_sub_explicit(A, B, C) *(A) -= (B)
#define atomic_init(A, B) *(A) = (B)
#else
#include <stdatomic.h>
#endif

#endif
