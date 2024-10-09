#ifndef TY_H_INCLUDED
#define TY_H_INCLUDED

#include <stddef.h>
#include <setjmp.h>
#include <stdbool.h>
#include <inttypes.h>

#include "vec.h"
#include "intern.h"

typedef struct value Value;

typedef vec(char) byte_vector;
typedef vec(char *) CallStack;
typedef vec(Value) ValueVector;
typedef ValueVector ValueStack;
typedef vec(char const *) StringVector;
typedef vec(struct try *) TryStack;
typedef vec(struct sigfn) SigfnStack;

struct target {
        struct {
                Value *t;
                void *gc;
        };
};

typedef struct target Target;

struct frame;
typedef struct frame Frame;

typedef vec(Target) TargetStack;

typedef struct table ValueTable;

struct try {
        jmp_buf jb;
        bool executing;
        uint8_t state;
        int sp;
        int gc;
        int cs;
        int ts;
        int ds;
        int ctxs;
        int nsp;
        char *catch;
        char *finally;
        char *end;
        enum { TRY_TRY, TRY_THROW, TRY_CATCH, TRY_FINALLY };
};

typedef struct ThrowCtx {
        int ctxs;
        char const *ip;
} ThrowCtx;

typedef vec(size_t) SPStack;
typedef vec(Frame) FrameStack;

typedef vec(struct alloc *) AllocList;

typedef struct {
        InternSet u_ops;
        InternSet b_ops;
} TY;

typedef struct thread_group ThreadGroup;

typedef struct arena {
	char *base;
	char *beg;
	char *end;
	bool gc;
} Arena;

typedef struct {
        TY *ty;
        char *ip;
        ValueStack stack;
        CallStack calls;
        TargetStack targets;
        FrameStack frames;

        AllocList allocs;
        size_t memory_used;
        size_t memory_limit;
        int GC_OFF_COUNT;

        Arena arena;

        ThreadGroup *my_group;
} Ty;

#define MemoryUsed  (ty->memory_used)
#define MemoryLimit (ty->memory_limit)

#define MyGroup (ty->my_group)

extern Ty MainTy;
extern TY xD;

#define dont_printf(...) do { } while (0)

#define GC_STOP() (ty->GC_OFF_COUNT += 1)
#define GC_RESUME() (ty->GC_OFF_COUNT -= 1)

#define zP(...) vm_panic(ty, __VA_ARGS__)
#define mRE(...) resize(__VA_ARGS__)
#define mREu(...) resize_unchecked(__VA_ARGS__)
#define mA(...) gc_alloc(ty, __VA_ARGS__)
#define mAo(...) gc_alloc_object(ty, __VA_ARGS__)
#define mAo0(...) gc_alloc_object0(ty, __VA_ARGS__)
#define mF(p) gc_free(ty, p)

#define amA(n) Allocate(ty, n)
#define amA0(n) Allocate0(ty, n)
#define amX(n) DestroyArena(ty, n)
#define amF(n) ReleaseArena(ty, n)

#define amN(c) NewArena(ty, c)
#define amNg(c) NewArenaGC(ty, c)

#define vSc(s, n) STRING_CLONE(ty, s, n)
#define vSnc(s, n) STRING_C_CLONE(ty, s, n)
#define vScn(s)    STRING_CLONE_C(ty, s)
#define vSncn(s)    STRING_C_CLONE_C(ty, s)

#define vA()       value_array_new(ty)
#define vAn(n)     value_array_new_sized(ty, n)
#define vAp(a, x)  value_array_push(ty, a, x)

#define vT(n)    value_tuple(ty, n)
#define vTn(...)  value_named_tuple(ty, __VA_ARGS__, NULL)

#define vvPn(a, b, c)    vec_push_n(ty, a, b, c)
#define vvP(a, b)       vec_push(ty, a, b)
#define vvI(a, b, c)    vec_insert(ty, a, b, c)
#define vvIn(a, b, c, d) vec_insert_n(ty, a, b, c, d)
#define vvF(a)           vec_empty(ty, a)
#define vvR(a, b)        vec_reserve(ty, a, b)

#define vvX  vec_pop
#define vvL  vec_last
#define vvXi vec_pop_ith

#define avP(a, b)       VPush(ty, a, b)
#define avPn(a, b, c)    VPushN(ty, a, b, c)
#define avI(a, b, c)    VInsert(ty, a, b, c)
#define avIn(a, b, c, d) VInsertN(ty, a, b, c, d)

#define xvP(a, b)       vec_nogc_push(a, b)
#define xvPn(a, b, c)    vec_nogc_push_n(a, b, c)
#define xvI(a, b, c)    vec_nogc_insert(a, b, c)
#define xvIn(a, b, c, d) vec_nogc_insert_n(a, b, c, d)
#define xvR(a, b)       vec_nogc_reserve(a, b)

#define gP(x) gc_push(ty, x)
#define gX()  gc_pop(ty)

#define lGv(b) ReleaseLock(ty, b)
#define lTk()  TakeLock(ty)

#define vmP(x)     vm_push(ty, x)
#define vmX()      vm_pop(ty)
#define vmE(x)     vm_throw(ty, x)
#define vmC(...)   vm_call(ty, __VA_ARGS__)

#define PAIR(a, b)    PAIR_(ty, a, b)
#define TRIPLE(a, b, c) TRIPLE_(ty, a, b, c)

#define TY_BINARY_OPERATORS  \
        X(ADD,       "+"),   \
        X(SUB,       "-"),   \
        X(MUL,       "*"),   \
        X(DIV,       "/"),   \
        X(MOD,       "%"),   \
        X(AND,      "&&"),   \
        X(OR,       "||"),   \
        X(BIT_OR,    "|"),   \
        X(BIT_AND,   "&"),   \
        X(BIT_XOR,   "^"),   \
        X(EQL,      "=="),   \
        X(NEQ,      "!="),   \
        X(CMP,     "<=>"),   \
        X(GT,        ">"),   \
        X(LT,        "<"),   \
        X(GEQ,      ">="),   \
        X(LEQ,      "<=")

#define X(op, id) OP_ ## op
enum {
        TY_BINARY_OPERATORS
};
#undef X

#define FMT_MORE "\n                 "
#define FMT_CS   "%s%s%s"

#define FMT_MAGENTA2(s) TERM(95), (s), TERM(0)

#define VSC(v) value_show_color(ty, v)

#define pT(p) ((uintptr_t)p &  7)
#define pP(p) ((uintptr_t)p & ~7)

#define NEW(x) x = mrealloc(NULL, sizeof *(x))

#endif
