#ifndef DEFS_H_INCLUDED
#define DEFS_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <setjmp.h>
#include <stdbool.h>

#include "vec.h"

#define CAT(a, b) a ## b

#define VA_COUNT_INNER(_1, _2, _3, _4, _5, _6, _7, _8, COUNT, ...) COUNT
#define VA_COUNT(...) VA_COUNT_INNER(__VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1, 0)

#define VA_SELECT_INNER(f, i) CAT(f##_, i)
#define VA_SELECT(f, ...) VA_SELECT_INNER(f, VA_COUNT(__VA_ARGS__))(__VA_ARGS__)

#if defined(TY_RELEASE)
 #include <mimalloc.h>
 #define ty_malloc        mi_malloc
 #define ty_calloc        mi_calloc
 #define ty_realloc       mi_realloc
 #define ty_free          mi_free
 #define ty_aligned_alloc mi_aligned_alloc
#else
 #define ty_malloc        malloc
 #define ty_calloc        calloc
 #define ty_realloc       realloc
 #define ty_free          free
 #define ty_aligned_alloc aligned_alloc
#endif

#if defined(__APPLE__)
#  define rqsort(base, nel, width, cmp, ctx) qsort_r(base, nel, width, ctx, cmp);
#elif defined(__linux__)
#  define rqsort(base, nel, width, cmp, ctx) qsort_r(base, nel, width, cmp, ctx);
#elif defined(_WIN32)
#  define rqsort(base, nel, width, cmp, ctx) qsort_s(base, nel, width, cmp, ctx);
#endif

typedef uint8_t   u8;
typedef uint16_t  u16;
typedef uint32_t  u32;
typedef uint64_t  u64;
typedef size_t    usize;
typedef uintmax_t umax;
typedef uintptr_t uptr;

typedef int8_t   i8;
typedef int16_t  i16;
typedef int32_t  i32;
typedef int64_t  i64;
typedef int64_t  isize;
typedef intmax_t imax;
typedef intptr_t iptr;

typedef vec(char)           byte_vector;
typedef vec(bool)           BoolVector;
typedef vec(int)            int_vector;
typedef vec(i32)            i32Vector;
typedef vec(i16)            i16Vector;
typedef vec(u16)            u16Vector;
typedef vec(u32)            U32Vector;
typedef vec(char *)         StringVector;
typedef vec(char const *)   ConstStringVector;
typedef vec(jmp_buf *)      JmpBufVector;

typedef struct ty0        TY;
typedef struct ty         Ty;
typedef struct ty_save    TySavePoint;
typedef struct value      Value;
typedef struct expression Expr;
typedef struct statement  Stmt;
typedef struct module     Module;
typedef struct symbol     Symbol;
typedef struct scope      Scope;
typedef struct frame      Frame;
typedef struct target     Target;
typedef struct type       Type;
typedef struct constraint Constraint;
typedef struct refinement Refinement;
typedef struct type_env   TypeEnv;
typedef struct frame      Frame;
typedef struct table      ValueTable;
typedef struct class      Class;

typedef struct ty0        TY;
typedef struct ty         Ty;
typedef struct ty_save    TySavePoint;
typedef struct value      Value;
typedef struct expression Expr;
typedef struct statement  Stmt;
typedef struct module     Module;
typedef struct symbol     Symbol;
typedef struct scope      Scope;
typedef struct frame      Frame;
typedef struct target     Target;
typedef struct type       Type;
typedef struct constraint Constraint;
typedef struct refinement Refinement;
typedef struct type_env   TypeEnv;
typedef struct frame      Frame;
typedef struct table      ValueTable;
typedef struct class      Class;

#define m0(x) memset(&(x), 0, sizeof (x))

#define zP(...)    vm_error(ty, __VA_ARGS__)
#define zPx(...)   vm_panic(ty, __VA_ARGS__)
#define zPxx(...)   vm_panic_ex(ty, __VA_ARGS__)

#define mRE(...)   resize(__VA_ARGS__)
#define mREu(...)  resize_unchecked(__VA_ARGS__)
#define mA(...)    gc_alloc(ty, __VA_ARGS__)
#define mA0(...)   gc_alloc0(ty, __VA_ARGS__)
#define mAo(...)   gc_alloc_object(ty, __VA_ARGS__)
#define mAo0(...)  gc_alloc_object0(ty, __VA_ARGS__)
#define mF(p)      gc_free(ty, p)

#define uAo(...)   gc_alloc_object_unchecked(ty, __VA_ARGS__)
#define uAo0(...)  gc_alloc_object0_unchecked(ty, __VA_ARGS__)

#define amA(n)  Allocate(ty, (n))
#define amA0(n) Allocate0(ty, (n))
#define amX(n)  DestroyArena(ty, (n))
#define amF(n)  ReleaseArena(ty, (n))

#define aclone(x) memcpy(amA(sizeof *(x)), (x), sizeof *(x))

#define smA(n) AllocateScratch(ty, (n))
#define smA0(n) AllocateScratch0(ty, (n))

#define xmA(n) mrealloc(NULL, (n))
#define xmF(p) ty_free((p))

#define mresize(ptr, n) ((ptr) = mrealloc((ptr), (n)))
#define Resize(p, n, m) ((p) = __builtin_memcpy(amA(n), (p), (m)))
#define resize_scratch(p, n, m) ((p) = __builtin_memcpy(smA(n), (p), (m)))

#define vSs(s, n)  STRING_CLONE(ty, (s), (n))
#define vSzs(s, n) STRING_C_CLONE(ty, (s), (n))
#define vSsz(s)    STRING_CLONE_C(ty, (s))
#define vSzz(s)    STRING_C_CLONE_C(ty, (s))

#define xSs(s, n) STRING_NOGC((s), (n))
#define xSz(s)    STRING_NOGC_C(s)

#define ss(v) ((v).str)
#define sN(v) ((v).bytes)

#define vA()       value_array_new(ty)
#define vAn(n)     value_array_new_sized(ty, n)
#define vAp(a, x)  value_array_push(ty, a, x)

#define vT(n)     value_tuple(ty, n)
#define vTn(...)  value_named_tuple(ty, __VA_ARGS__, NULL)

#define vvPn(a, b, c)     vec_push_n((a), (b), (c))
#define vvPv(v, u)        vec_push_n((v), (u).items, (u).count)
#define vvP(a, b)         vec_push((a), (b))
#define vvI(v, x, i)      vec_insert((v), (x), (i))
#define vvIn(v, xs, n, i) vec_insert_n((v), (xs), (n), (i))
#define vvF(a)            mF((a).items)
#define vv0(v)            vec_empty(v)
#define vvR(a, b)         vec_reserve((a), (b))

#define vvX  vec_pop
#define vvL  vec_last
#define vvXi vec_pop_ith

#define vN(v)     ((v).count)
#define v0(v)     ((v).count = 0)
#define v00(v)    (((v).count = 0), ((v).items = NULL), ((v).capacity = 0))
#define v_(v, i)  (&(v).items[(i)])
#define v_0(v)    ((v).items[0])
#define v_L(v)    ((v).items[(v).count - 1])
#define v__(v, i) ((v).items[(i)])
#define vv(v)     ((v).items)
#define vZ(v)     ((v).items + (v).count)
#define vPx(v, x) (((v).items[(v).count] = (x)), (v).count += 1)
#define vXx(v)    ((v).items[--(v).count])
#define vC(v)     ((v).capacity)

#define vM(v, i, j, n) memmove((v).items + (i), (v).items + (j), (n) sizeof *(v).items)

#define vfor_4(i, x, v, go) for (isize i = 0; i < vN(v); ++i) { typeof (vv(v)) x = v_((v), i); go; }
#define vfor_3(   x, v, go) vfor_4(_i_##x, x,  (v), go)
#define vfor_2(      v, go) vfor_4(_vfi,   it, (v), go)
#define vfor(...) VA_SELECT(vfor, __VA_ARGS__)

#define dfor_4(_k, _v, _d, go) \
        for (DictItem *_d_item = DictFirst((_d)); _d_item != NULL; _d_item = _d_item->next) { \
                Value *(_k) = &_d_item->k; (void)(_k);\
                Value *(_v) = &_d_item->v; (void)(_v); \
                go; \
        }
#define dfor_3(v, d, go) dfor_4(key, (v), (d), go)
#define dfor_2(   d, go) dfor_4(key, val, (d), go)
#define dfor(...) VA_SELECT(dfor, __VA_ARGS__)

#define avP(a, b)        VPush((a), (b))
#define avPn(a, b, c)    VPushN(a, b, c)
#define avI(v, x, i)     VInsert(v, x, i)
#define avIn(a, b, c, d) VInsertN(a, b, c, d)
#define avPv(a, b)       VPushN((a), ((b).items), ((b).count))
#define avPvn(a, b, n)   VPushN((a), ((b).items), (n))
#define avR(v, n)        VReserve((v), (n))

#define avC(v) (                                       \
        (v).items = memcpy(                            \
                amA((v).capacity * sizeof *(v).items), \
                (v).items,                             \
                ((v).count * sizeof *(v).items)        \
        )                                              \
)

#define uvP(v, x)         vec_push_unchecked((v), (x))
#define uvPn(v, xs, n)    vec_push_n_unchecked((v), (xs), (n))
#define uvPv(v, u)        vec_push_n_unchecked((v), ((u).items), ((u).count))
#define uvI(v, x, i)      vec_insert_unchecked((v), (x), (i))
#define uvIn(v, xs, n, i) vec_insert_n_unchecked((v), (xs), (n), (i))
#define uvR(v, n)         vec_reserve_unchecked((v), (n))

#define xvP(a, b)        vec_nogc_push((a), (b))
#define xvPn(a, b, c)    vec_nogc_push_n((a), (b), (c))
#define xvPv(a, b)       vec_nogc_push_n((a), ((b).items), ((b).count))
#define xvI(a, b, c)     vec_nogc_insert((a), (b), (c))
#define xvIn(a, b, c, d) vec_nogc_insert_n(a, (b), (c), (d))
#define xvR(a, b)        vec_nogc_reserve((a), (b))
#define xvF(v)           ty_free((v).items)

#define svPn(a, b, c)    vec_push_n_scratch((a), (b), (c))
#define svPv(a, b)       vec_push_n_scratch((a), ((b).items), ((b).count))
#define svP(a, b)        vec_push_scratch((a), (b))
#define svI(a, b, c)     vec_insert_scratch((a), (b), (c))
#define svIn(a, b, c, d) vec_insert_n_scratch(a, (b), (c), (d))
#define svR(v, n)        vec_reserve_scratch((v), (n))

#define gP(x) (xvP(RootSet, *(x)))
#define gX()  (vXx(RootSet))

#define lGv(b) ReleaseLock(ty, b)
#define lTk()  TakeLock(ty)

#define vmP(x)   vm_push(ty, x)
#define vmX()    vm_pop(ty)
#define vmE(x)   vm_throw(ty, x)
#define vmC(...) vm_call(ty, __VA_ARGS__)

#endif

/* vim: set sts=8 sw=8 expandtab: */
