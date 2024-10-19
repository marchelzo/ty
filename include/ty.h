#ifndef TY_H_INCLUDED
#define TY_H_INCLUDED

#include <stdlib.h>
#include <stddef.h>
#include <setjmp.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdalign.h>

#include "vec.h"
#include "intern.h"
#include "panic.h"

typedef struct value Value;

typedef vec(int)           int_vector;
typedef vec(char)          byte_vector;
typedef vec(char *)        CallStack;
typedef vec(Value)         ValueVector;
typedef ValueVector        ValueStack;
typedef vec(char *)        StringVector;
typedef vec(char const *)  ConstStringVector;
typedef vec(struct try *)  TryStack;
typedef vec(struct sigfn)  SigfnStack;

typedef struct target {
        struct {
                Value *t;
                void *gc;
        };
} Target;

struct frame;
typedef struct frame Frame;

typedef vec(Target) TargetStack;

typedef struct table ValueTable;

enum { TRY_TRY, TRY_THROW, TRY_CATCH, TRY_FINALLY };

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
        InternSet members;
} TY;

typedef struct thread_group ThreadGroup;

typedef struct arena {
        char *base;
        char *beg;
        char *end;
        bool gc;
} Arena;

typedef struct {
        int i;
        void *beg;
} ScratchSave;

typedef struct {
        TY *ty;
        char *ip;
        ValueStack stack;
        CallStack calls;
        TargetStack targets;
        FrameStack frames;

        uint64_t prng[4];

        AllocList allocs;
        size_t memory_used;
        size_t memory_limit;
        int GC_OFF_COUNT;

        Arena arena;

        struct {
                int i ;
                vec(Arena) arenas;
        } scratch;

        ThreadGroup *my_group;
} Ty;

struct member_names {
        int missing;
        int slice;
        int fmt;
        int str;
        int question;
        int subscript;
        int len;
        int match;
        int json;
};

#define MemoryUsed  (ty->memory_used)
#define MemoryLimit (ty->memory_limit)

#define MyGroup (ty->my_group)

extern Ty MainTy;
extern TY xD;
extern struct member_names NAMES;

extern bool ColorStdout;
extern bool ColorStderr;
extern bool ColorProfile;

#define dont_printf(...) do { } while (0)

#define GC_STOP()   (ty->GC_OFF_COUNT += 1)
#define GC_RESUME() (ty->GC_OFF_COUNT -= 1)

#ifdef _WIN32
#  define UNLIKELY(x)  (x)
#  define LIKELY(x)    (x)
#  define EXPECT(x, y) (x)
#else
#  define UNLIKELY(x)  __builtin_expect((x), 0)
#  define LIKELY(x)    __builtin_expect((x), 1)
#  define EXPECT(x, y) __builtin_expect((x), (y))
#endif


#define zP(...)   vm_panic(ty, __VA_ARGS__)
#define mRE(...)  resize(__VA_ARGS__)
#define mREu(...) resize_unchecked(__VA_ARGS__)
#define mA(...)   gc_alloc(ty, __VA_ARGS__)
#define mAo(...)  gc_alloc_object(ty, __VA_ARGS__)
#define mAo0(...) gc_alloc_object0(ty, __VA_ARGS__)
#define mF(p)     gc_free(ty, p)

#define amA(n)  Allocate(ty, (n))
#define amA0(n) Allocate0(ty, (n))
#define amX(n)  DestroyArena(ty, (n))
#define amF(n)  ReleaseArena(ty, (n))

#define smA(n) AllocateScratch(ty, (n))

#define amN(c)  NewArena(ty, (c))
#define amNg(c) NewArenaGC(ty, (c))

#define vSs(s, n)  STRING_CLONE(ty, (s), (n))
#define vSzs(s, n) STRING_C_CLONE(ty, (s), (n))
#define vSsz(s)    STRING_CLONE_C(ty, (s))
#define vSzz(s)    STRING_C_CLONE_C(ty, (s))

#define xSs(s, n) STRING_NOGC((s), (n))
#define xSz(s)    STRING_NOGC_C(s)

#define vA()       value_array_new(ty)
#define vAn(n)     value_array_new_sized(ty, n)
#define vAp(a, x)  value_array_push(ty, a, x)

#define vT(n)     value_tuple(ty, n)
#define vTn(...)  value_named_tuple(ty, __VA_ARGS__, NULL)

#define vvPn(a, b, c)    vec_push_n((a), (b), (c))
#define vvP(a, b)        vec_push((a), (b))
#define vvI(a, b, c)     vec_insert((a), (b), (c))
#define vvIn(a, b, c, d) vec_insert_n(a, (b), (c), (d))
#define vvF(a)           vec_empty((a))
#define vvR(a, b)        vec_reserve((a), (b))

#define vvX  vec_pop
#define vvL  vec_last
#define vvXi vec_pop_ith
#define v_(v, i) (&(v).items[(i)])
#define vZ(v) ((v).items + (v).count)

#define avP(a, b)        VPush(a, b)
#define avPn(a, b, c)    VPushN(a, b, c)
#define avI(a, b, c)     VInsert(a, b, c)
#define avIn(a, b, c, d) VInsertN(a, b, c, d)
#define avPv(a, b)       VPushN((a), ((b).items), ((b).count))

#define uvP(v, x)         vec_push_unchecked((v), (x))
#define uvPn(v, xs, n)    vec_push_n_unchecked((v), (xs), (n))
#define uvI(v, x, i)      vec_insert_unchecked((v), (x), (i))
#define uvIn(v, xs, n, i) vec_insert_n_unchecked((v), (xs), (n), (i))

#define xvP(a, b)        vec_nogc_push((a), (b))
#define xvPn(a, b, c)    vec_nogc_push_n((a), (b), (c))
#define xvI(a, b, c)     vec_nogc_insert((a), (b), (c))
#define xvIn(a, b, c, d) vec_nogc_insert_n(a, (b), (c), (d))
#define xvR(a, b)        vec_nogc_reserve((a), (b))

#define svPn(a, b, c)    vec_push_n_scratch((a), (b), (c))
#define svP(a, b)        vec_push_scratch((a), (b))
#define svI(a, b, c)     vec_insert_scratch((a), (b), (c))
#define svIn(a, b, c, d) vec_insert_n_scratch(a, (b), (c), (d))

#define gP(x) gc_push(ty, x)
#define gX()  gc_pop(ty)

#define lGv(b) ReleaseLock(ty, b)
#define lTk()  TakeLock(ty)

#define vmP(x)   vm_push(ty, x)
#define vmX()    vm_pop(ty)
#define vmE(x)   vm_throw(ty, x)
#define vmC(...) vm_call(ty, __VA_ARGS__)

#define PAIR(a, b)            PAIR_(ty, (a), (b))
#define TRIPLE(a, b, c)       TRIPLE_(ty, (a), (b), (c))
#define QUADRUPLE(a, b, c, d) QUADRUPLE_(ty, (a), (b), (c), (d))

#define TY_BINARY_OPERATORS  \
        X(ADD,       "+"),   \
        X(SUB,       "-"),   \
        X(MUL,       "*"),   \
        X(DIV,       "/"),   \
        X(MOD,       "%"),   \
        X(MUT_ADD,   "+="),  \
        X(MUT_SUB,   "-="),  \
        X(MUT_MUL,   "*="),  \
        X(MUT_DIV,   "/="),  \
        X(MUT_MOD,   "%="),  \
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

enum {
        TY_COLOR_AUTO,
        TY_COLOR_ALWAYS,
        TY_COLOR_NEVER
};

#define FMT_MORE "\n                 "
#define FMT_CS   "%s%s%s"

#define FMT_MAGENTA2(s) TERM(95), (s), TERM(0)

#define VSC(v) value_show_color(ty, v)

#define pT(p) ((uintptr_t)p &  7)
#define pP(p) ((uintptr_t)p & ~7)

#define M_ID(m)   intern(&xD.members, (m))->id
#define M_NAME(i) intern_entry(&xD.members, (i))->name

#define PMASK3 ((uintptr_t)7)

inline static void *
mrealloc(void *p, size_t n)
{
        p = realloc(p, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

#define mresize(ptr, n) ((ptr) = mrealloc((ptr), (n)))

inline static void
ExpandScratch(Ty *ty)
{
#define S(x) (ty->scratch . x)
#define SS   (&S(arenas.items)[S(i) - 1])
        if (S(i) == S(arenas.count)) {
                ptrdiff_t cap;

                if (S(i) == 0) {
                        cap = 1LL << 12;
                } else {
                        cap = 2 * (vvL(S(arenas))->end - vvL(S(arenas))->base);
                }

                char *new_ = mrealloc(NULL, cap);

                xvP(
                        S(arenas),
                        ((Arena) {
                                .base = new_,
                                .beg  = new_,
                                .end  = new_ + cap
                        })
                );
        }

        S(i) += 1;
}

inline static void *
AllocateScratch(Ty *ty, size_t n)
{
        for (;;) {
                ptrdiff_t avail = SS->end - SS->beg;
                ptrdiff_t padding = -(intptr_t)SS->beg & ((alignof (void *)) - 1);

                if (n > avail - padding) {
                        ExpandScratch(ty);
                } else {
                        char *new = SS->beg + padding;
                        SS->beg += padding + n;
                        return new;
                }
        }
}

inline static ScratchSave
SaveScratch(Ty *ty)
{
        return (ScratchSave) {
                .i = S(i),
                .beg = SS->beg
        };
}

inline static void
RestoreScratch(Ty *ty, ScratchSave save)
{
        while (S(i) > save.i) {
                SS->beg = SS->base;
                S(i) -= 1;
        }
}
#undef S
#undef SS

#define SCRATCH_SAVE()    ScratchSave _scratch_save = SaveScratch(ty);
#define SCRATCH_RESTORE() RestoreScratch(ty, _scratch_save);

#endif

/* vim: set sts=8 sw=8 expandtab: */
