#ifndef LIR_TEST_H_INCLUDED
#define LIR_TEST_H_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ty.h"
#include "jit/lir.h"

static u32 checks;
static u32 failures;
static Ty  TestTy;
static Ty *ty = &TestTy;

#define CHECK(expr) do {                                                        \
        checks += 1;                                                            \
        if (!(expr)) {                                                          \
                fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #expr);      \
                failures += 1;                                                  \
        }                                                                       \
} while (0)

#define T(...) ((LirType[]) { __VA_ARGS__ })
#define O(...) ((LirOpnd[]) { __VA_ARGS__ })

#define S(f, x) ((LirScalar) { .f = (x) })
#define S0      ((LirScalar) {0})

#define fnm(mode, ret, ...) build((ret), T(__VA_ARGS__), countof(T(__VA_ARGS__)), (mode))
#define fn(ret, ...)        fnm(LIR_MODE_AUTO, (ret), __VA_ARGS__)
#define fna(ret, types)     build((ret), (types), countof(types), LIR_MODE_AUTO)

#define put(L, op, d, ...) emit((L), (op), (d), O(__VA_ARGS__), countof(O(__VA_ARGS__)))
#define ret(L, x)          _Generic((x), LirOpnd: retv, default: retr)((L), (x))

#define callee(f)      lir_i((iptr)(f))
#define deref(r, disp) lir_m((r), LIR_NONE, 1, (disp))
#define field(r, f)    deref((r), offsetof(Value, f))

__attribute__((constructor))
static void
scratch(void)
{
        ExpandScratch(ty);
}

static Lir *
build(LirType ret, LirType const *params, u32 n, LirMode mode)
{
        LirError err;
        LirSig   sig = { .ret = ret, .params = params, .nparams = n, .nfixed = n };
        Lir     *L   = lir_new("test", &sig, mode, &err);

        CHECK(L != NULL);

        if (L == NULL) {
                fprintf(stderr, "%s\n", err.message);
                exit(1);
        }

        return L;
}

static void
emit(Lir *L, LirOp op, LirReg d, LirOpnd const *args, u32 n)
{
        CHECK(lir_emit_to(L, op, d, args, n));
}

static void
push(Lir *L, LirInst in)
{
        CHECK(lir_emit(L, &in));
}

static void
here(Lir *L, LirLabel label)
{
        CHECK(lir_bind(L, label));
}

static void
retv(Lir *L, LirOpnd x)
{
        put(L, LIR_RET, LIR_NONE, x);
}

static void
retr(Lir *L, LirReg r)
{
        if (r == LIR_NONE) {
                put(L, LIR_RET, LIR_NONE);
        } else {
                retv(L, lir_r(r));
        }
}

inline static LirSig
sig(LirType ret, LirType const *params, u32 n)
{
        return (LirSig) { .ret = ret, .params = params, .nparams = n, .nfixed = n };
}

inline static LirSig
vsig(LirType ret, LirType const *params, u32 n, u32 nfixed)
{
        LirSig s = sig(ret, params, n);

        s.nfixed   = nfixed;
        s.variadic = true;

        return s;
}

inline static LirInst
call(LirOpnd target, LirReg d, LirSig s, LirOpnd *args)
{
        return (LirInst) {
                .op         = LIR_CALL,
                .dst        = d,
                .args       = { target },
                .nargs      = 1,
                .sig        = s,
                .call_args  = args,
                .ncall_args = s.nparams
        };
}

inline static LirInst
vcall(LirOpnd target)
{
        return call(target, LIR_NONE, sig(LT_VOID, NULL, 0), NULL);
}

inline static LirInst
tail(LirOpnd target, LirSig s, LirOpnd *args)
{
        LirInst in = call(target, LIR_NONE, s, args);

        in.op = LIR_TAILCALL;

        return in;
}

inline static LirInst
jump_table(LirOpnd x, LirLabel fallback, LirLabel *targets, u32 n)
{
        return (LirInst) {
                .op       = LIR_SWITCH,
                .dst      = LIR_NONE,
                .args     = { x, lir_l(fallback) },
                .nargs    = 2,
                .targets  = targets,
                .ntargets = n
        };
}

inline static u64
xorshift(u64 *seed)
{
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        return *seed;
}

static Ty  EmptyTy;
static Ty *CurrentTy = &EmptyTy;

static volatile sig_atomic_t Interrupt;
static u32                   Polls;
static void const           *LastInfo;

static Ty *
current_ty(void)
{
        return CurrentTy;
}

static i32
handle_poll(Ty *ty, Value *top, void const *info)
{
        Polls    += 1;
        Interrupt = 0;
        LastInfo  = info;

        return info != NULL;
}

static int
report(char const *suite)
{
        printf("%s: %u checks, %u failures\n", suite, checks, failures);
        return failures != 0;
}

#endif
