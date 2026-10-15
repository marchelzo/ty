#ifndef LIR_IMPL_H_INCLUDED
#define LIR_IMPL_H_INCLUDED

#include "ty.h"
#include "jit/lir.h"

#define dupn(p, n) lir_copy((p), (n), sizeof *(p))
#define vdup(v)    ((v).items = dupn((v).items, vN(v)), (v).capacity = vN(v))

#define stA(T, n)  ((T *)smA((usize)(n) * sizeof (T)))
#define stA0(T, n) ((T *)smA0((usize)(n) * sizeof (T)))

#define INST_PAYLOAD(X)                 \
        X(sig.params, sig.nparams)      \
        X(call_args,  ncall_args)       \
        X(targets,    ntargets)         \
        X(raw.arm64,  raw.narm64)       \
        X(raw.x64,    raw.nx64)         \
        X(raw.in,     raw.nin)          \
        X(raw.out,    raw.nout)

#define nopnd(in)   ((in)->nargs + (in)->ncall_args)
#define opnd(in, j) (                                   \
          ((j) < (in)->nargs)                           \
        ? &(in)->args[(j)]                              \
        : &(in)->call_args[(j) - (in)->nargs]           \
)

#define each_read(in, r)                                                        \
        for (u32 _j = 0, _n = nreads(in); _j < _n; ++_j)                        \
        for (LirReg _rs[2], _k = 0, _m = reads_at((in), _j, _rs); _k < _m; ++_k) \
        for (LirReg r = _rs[_k], _go = 1; _go; _go = 0)

#define each_write(in, r)                                                       \
        for (u32 _j = 0, _n = nwrites(in); _j < _n; ++_j)                       \
        for (LirReg r = writes_at((in), _j), _go = 1; _go; _go = 0)

Ty *
lir_scratch(Ty *ty);

void *
lir_copy(void const *src, usize n, usize size);

bool
lir_check_inst(Lir const *L, u32 pc, LirError *err);

bool
lir_check_labels(Lir const *L, LirError *err);

bool
lir_resolve_mode(Lir *L, LirError *err);

inline static bool
iscall(LirInst const *in)
{
        return (in->op == LIR_CALL) || (in->op == LIR_TAILCALL);
}

inline static bool
pow2(i64 n)
{
        return (n > 0) && ((n & (n - 1)) == 0);
}

inline static LirClass
rcls(Lir const *L, LirReg r)
{
        return (r < vN(L->regs)) ? v__(L->regs, r).cls : LIR_CLASS_COUNT;
}

inline static bool
param_ok(Lir const *L, LirRegInfo ri)
{
        if (ri.param == LIR_NONE) {
                return true;
        }

        return (ri.param < L->sig.nparams)
            && (ri.cls == lir_type_class(L->sig.params[ri.param]));
}

inline static void
bset(u64 *bits, u32 i)
{
        bits[i / 64] |= 1ULL << (i % 64);
}

inline static bool
bhas(u64 const *bits, u32 i)
{
        return (bits[i / 64] >> (i % 64)) & 1;
}

inline static u32
nreads(LirInst const *in)
{
        return nopnd(in) + in->raw.nin;
}

inline static u32
reads_at(LirInst const *in, u32 j, LirReg rs[static 2])
{
        if (j >= nopnd(in)) {
                rs[0] = in->raw.in[j - nopnd(in)].reg;
                return 1;
        }

        LirOpnd const *a = opnd(in, j);

        switch (a->kind) {
        case LO_REG:
                rs[0] = a->reg;
                return 1;

        case LO_MEM:
                rs[0] = a->mem.base;
                rs[1] = a->mem.index;
                return 1 + (a->mem.index != LIR_NONE);

        default:
                return 0;
        }
}

inline static u32
nwrites(LirInst const *in)
{
        return (in->dst != LIR_NONE) + in->raw.nout;
}

inline static LirReg
writes_at(LirInst const *in, u32 j)
{
        if (in->dst == LIR_NONE) {
                return in->raw.out[j].reg;
        }

        return (j == 0) ? in->dst : in->raw.out[j - 1].reg;
}

inline static void
clear(LirError *err)
{
        if (err != NULL) {
                *err = (LirError) {0};
        }
}

inline static bool
relay(Lir const *L, LirError *err)
{
        if (L->error.kind == LE_NONE) {
                return false;
        }

        if (err != NULL) {
                *err = L->error;
        }

        return true;
}

inline static void
inst_free(LirInst *in)
{
#define FREE(p, n) xmF((void *)in->p);
        INST_PAYLOAD(FREE)
#undef FREE
}

inline static bool
sig_valid(LirSig const *sig)
{
        if (
                (sig == NULL)
             || ((u32)sig->ret >= LT_COUNT)
             || (sig->nparams != 0 && sig->params == NULL)
             || (sig->nfixed > sig->nparams)
        ) {
                return false;
        }

        for (u32 i = 0; i < sig->nparams; ++i) {
                if (sig->params[i] == LT_VOID || (u32)sig->params[i] >= LT_COUNT) {
                        return false;
                }
        }

        return true;
}

inline static bool
sig_equal(LirSig const *a, LirSig const *b)
{
        if (
                (a->ret != b->ret)
             || (a->nparams != b->nparams)
             || (a->variadic != b->variadic)
             || (a->variadic && a->nfixed != b->nfixed)
        ) {
                return false;
        }

        return (a->nparams == 0)
            || (memcmp(a->params, b->params, a->nparams * sizeof *a->params) == 0);
}

#endif
