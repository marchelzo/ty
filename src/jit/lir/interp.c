#include <math.h>
#include <setjmp.h>

#include "ty.h"
#include "jit/lir.h"

#define onstack(T, n)  ((T *)__builtin_alloca((usize)(n) * sizeof (T)))
#define onstack0(T, n) ((T *)memset(onstack(T, n), 0, (usize)(n) * sizeof (T)))

typedef struct {
        Ty         *ty;
        Lir const  *L;
        LirScalar  *regs;
        u8         *frame;
        usize      *slots;
        Value      *vslots;
        usize       vbase;
        usize       rbase;
        u32         nrefs;
        u32         nresults;
        u32        *returns;
        LirScalar  *out;
        LirError   *err;
        LirMode     mode;
} LirMachine;

typedef struct {
        uptr  base;
        usize capacity;
} StackMark;

typedef struct {
        Lir const   *L;
        LirMode      mode;
        ffi_cif      cif;
        ffi_closure *closure;
        ffi_type    *types[];
} LirInterpCode;

static ffi_type *const FfiTypes[LT_COUNT] = {
        [LT_VOID] = &ffi_type_void,
        [LT_I8]   = &ffi_type_sint8,
        [LT_U8]   = &ffi_type_uint8,
        [LT_I16]  = &ffi_type_sint16,
        [LT_U16]  = &ffi_type_uint16,
        [LT_I32]  = &ffi_type_sint32,
        [LT_U32]  = &ffi_type_uint32,
        [LT_I64]  = &ffi_type_sint64,
        [LT_U64]  = &ffi_type_uint64,
        [LT_F32]  = &ffi_type_float,
        [LT_F64]  = &ffi_type_double,
        [LT_BOOL] = &ffi_type_uint8,
        [LT_PTR]  = &ffi_type_pointer,
        [LT_REF]  = &ffi_type_pointer,
        [LT_VAL]  = &ffi_type_pointer
};

inline static ffi_type *
ctype(LirType type)
{
        return FfiTypes[type];
}

inline static LirScalar
word(u64 u)
{
        return (LirScalar) { .u = u };
}

inline static LirScalar
addr(void const *p)
{
        return (LirScalar) { .ptr = (void *)p };
}

inline static u64
zext(LirScalar a, LirClass cls)
{
        return (cls == LIR_I32) ? (u32)a.u : a.u;
}

inline static i64
sext(LirScalar a, LirClass cls)
{
        return (cls == LIR_I32) ? (i32)a.u : a.i;
}

inline static double
floating(LirScalar a, LirClass cls)
{
        return (cls == LIR_F32) ? a.f32 : a.f64;
}

inline static LirClass
rcls(Lir const *L, LirReg r)
{
        return v__(L->regs, r).cls;
}

inline static bool
ishole(LirOpnd a)
{
        return a.kind >= LO_HOLE_IMM;
}

inline static LirRuntime const *
vmrt(Ty const *ty)
{
        LirRuntime const *rt = lir_runtime();

        if (
                (ty == NULL)
             || (rt == NULL)
             || (rt->reserve == NULL)
             || (rt->restore == NULL)
        ) {
                return NULL;
        }

        return rt;
}

static bool
bad(LirMachine *m, u32 pc, char const *message)
{
        LirSpan span = v__(m->L->insts, pc).span;
        return lir_fail(m->err, LE_TARGET, pc, span, "%s", message);
}

static StackMark
mark(Ty const *ty)
{
        if (ty == NULL) {
                return (StackMark) {0};
        }

        return (StackMark) { (uptr)vv(ty->stack), vC(ty->stack) };
}

static void
rebase(Ty const *ty, StackMark old, LirScalar *x)
{
        if (x->u >= old.base && x->u < old.base + old.capacity * sizeof (Value)) {
                x->u = (uptr)vv(ty->stack) + x->u - old.base;
        }
}

static LirScalar
narrow(LirScalar a, LirType type)
{
        switch (type) {
        case LT_I8:   a.i = (i8)a.u;     break;
        case LT_U8:   a.u = (u8)a.u;     break;
        case LT_I16:  a.i = (i16)a.u;    break;
        case LT_U16:  a.u = (u16)a.u;    break;
        case LT_I32:  a.i = (i32)a.u;    break;
        case LT_U32:  a.u = (u32)a.u;    break;
        case LT_BOOL: a.u = (a.u != 0);  break;
        default:                         break;
        }

        return a;
}

static LirScalar
ref_value(Value const *v)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_OBJECT: return addr(v->object);
        case VALUE_TUPLE:  return addr(v->items);
        case VALUE_STRING: return addr((v->str0 == NULL) ? (void const *)v->str : v->str0);
        default:           return addr(v->ptr);
        }
}

static LirClass
operand_class(LirMachine const *m, LirOpnd a)
{
        switch (a.kind) {
        case LO_REG:      return rcls(m->L, a.reg);
        case LO_FIMM:     return LIR_F64;
        case LO_CONST:
        case LO_VSLOT:
        case LO_MEM:      return LIR_PTR;
        case LO_REFCONST: return LIR_REF;
        default:          return LIR_I64;
        }
}

static u64
address(LirMachine const *m, LirMem mem)
{
        u64 p = m->regs[mem.base].u + (u64)(i64)mem.disp;

        if (mem.index != LIR_NONE) {
                p += zext(m->regs[mem.index], rcls(m->L, mem.index)) * mem.scale;
        }

        return p;
}

static LirScalar
real(double x, LirClass cls)
{
        return (cls == LIR_F32) ? (LirScalar) { .f32 = x } : (LirScalar) { .f64 = x };
}

static LirScalar
operand(LirMachine const *m, LirOpnd a, LirClass cls)
{
        switch (a.kind) {
        case LO_REG:      return m->regs[a.reg];
        case LO_IMM:      return word(zext(word(a.imm), cls));
        case LO_FIMM:     return real(a.fimm, cls);
        case LO_MEM:      return word(address(m, a.mem));
        case LO_CONST:    return addr(v_(m->L->roots, a.index));
        case LO_REFCONST: return ref_value(v_(m->L->roots, a.index));
        case LO_VSLOT:    return addr(&m->vslots[a.index]);
        case LO_CODE:     return addr(a.code->body);
        case LO_HELPER:   return addr(a.helper->address);
        default:          return (LirScalar) {0};
        }
}

inline static LirScalar
natural(LirMachine const *m, LirOpnd a)
{
        return operand(m, a, operand_class(m, a));
}

inline static LirScalar
arg(LirMachine const *m, LirInst const *in, u32 i, LirClass cls)
{
        return (i < in->nargs) ? operand(m, in->args[i], cls) : (LirScalar) {0};
}

static LirClass
compare_class(LirMachine const *m, LirInst const *in)
{
        bool flip = (in->args[1].kind != LO_REG) && (in->args[2].kind == LO_REG);
        return operand_class(m, in->args[flip ? 2 : 1]);
}

static bool
condition(LirCC cc, LirScalar a, LirScalar b, LirClass cls)
{
        i64    x = sext(a, cls);
        i64    y = sext(b, cls);
        u64    u = zext(a, cls);
        u64    v = zext(b, cls);
        double f = floating(a, cls);
        double g = floating(b, cls);

        switch (cc) {
        case LIR_EQ:  return u == v;
        case LIR_NE:  return u != v;
        case LIR_LT:  return x <  y;
        case LIR_LE:  return x <= y;
        case LIR_GT:  return x >  y;
        case LIR_GE:  return x >= y;
        case LIR_ULT: return u <  v;
        case LIR_ULE: return u <= v;
        case LIR_UGT: return u >  v;
        case LIR_UGE: return u >= v;
        case LIR_FEQ: return f == g;
        case LIR_FNE: return f != g;
        case LIR_FLT: return f <  g;
        case LIR_FLE: return f <= g;
        case LIR_FGT: return f >  g;
        case LIR_FGE: return f >= g;
        case LIR_FUN: return isnan(f) || isnan(g);
        default:      return false;
        }
}

static i64
sdiv(i64 s, i64 t, i64 min)
{
        if (t == 0) {
                return 0;
        }

        return (s == min && t == -1) ? min : s / t;
}

static i64
srem(i64 s, i64 t, i64 min)
{
        if (t == 0) {
                return s;
        }

        return (s == min && t == -1) ? 0 : s % t;
}

static LirScalar
integer_binary(LirOp op, LirScalar a, LirScalar b, LirClass cls)
{
        u64 x     = zext(a, cls);
        u64 y     = zext(b, cls);
        i64 s     = sext(a, cls);
        i64 t     = sext(b, cls);
        u32 bits  = (cls == LIR_I32) ? 32 : 64;
        u32 shift = y & (bits - 1);
        i64 min   = (cls == LIR_I32) ? INT32_MIN : INT64_MIN;

        switch (op) {
        case LIR_ADD:   return word(x + y);
        case LIR_SUB:   return word(x - y);
        case LIR_MUL:   return word(x * y);
        case LIR_MULHS: return word((unsigned __int128)((__int128)s * t) >> bits);
        case LIR_MULHU: return word(((unsigned __int128)x * y) >> bits);
        case LIR_SDIV:  return word(sdiv(s, t, min));
        case LIR_SREM:  return word(srem(s, t, min));
        case LIR_UDIV:  return word((y == 0) ? 0 : x / y);
        case LIR_UREM:  return word((y == 0) ? x : x % y);
        case LIR_AND:   return word(x & y);
        case LIR_OR:    return word(x | y);
        case LIR_XOR:   return word(x ^ y);
        case LIR_SHL:   return word(x << shift);
        case LIR_SHR:   return word(x >> shift);
        case LIR_SAR:   return word(s >> shift);
        case LIR_ROTR:  return word((x >> shift) | (x << (-shift & (bits - 1))));
        default:        return word(0);
        }
}

static LirScalar
integer_unary(LirOp op, LirScalar a, LirClass cls)
{
        u64 x    = zext(a, cls);
        u32 bits = (cls == LIR_I32) ? 32 : 64;

        switch (op) {
        case LIR_NEG:    return word(-x);
        case LIR_NOT:    return word(~x);
        case LIR_CLZ:    return word((x == 0) ? bits : __builtin_clzll(x) - (64 - bits));
        case LIR_CTZ:    return word((x == 0) ? bits : __builtin_ctzll(x));
        case LIR_POPCNT: return word(__builtin_popcountll(x));
        case LIR_BSWAP:  return word(__builtin_bswap64(x) >> (64 - bits));
        case LIR_SEXT8:  return word((i8)x);
        case LIR_SEXT16: return word((i16)x);
        case LIR_SEXT32: return word((i32)x);
        case LIR_ZEXT8:  return word((u8)x);
        case LIR_ZEXT16: return word((u16)x);
        case LIR_ZEXT32: return word((u32)x);
        default:         return word(0);
        }
}

static bool
checked(LirOp op, LirScalar a, LirScalar b, LirClass cls, LirScalar *out)
{
        i64  x = sext(a, cls);
        i64  y = sext(b, cls);
        bool o;

        switch (op) {
        case LIR_ADDO: o = __builtin_add_overflow(x, y, &out->i); break;
        case LIR_SUBO: o = __builtin_sub_overflow(x, y, &out->i); break;
        default:       o = __builtin_mul_overflow(x, y, &out->i); break;
        }

        return (cls == LIR_I32) ? (out->i != (i32)out->i) : o;
}

static LirScalar
float_op(LirOp op, LirScalar a, LirScalar b, LirScalar c, LirClass cls)
{
        LirScalar r = {0};

#define FOPS(f, s)                                                      \
        switch (op) {                                                   \
        case LIR_FADD:  r.f = a.f + b.f;                 break;         \
        case LIR_FSUB:  r.f = a.f - b.f;                 break;         \
        case LIR_FMUL:  r.f = a.f * b.f;                 break;         \
        case LIR_FDIV:  r.f = a.f / b.f;                 break;         \
        case LIR_FMIN:  r.f = fmin##s(a.f, b.f);         break;         \
        case LIR_FMAX:  r.f = fmax##s(a.f, b.f);         break;         \
        case LIR_FSQRT: r.f = sqrt##s(a.f);              break;         \
        case LIR_FABS:  r.f = fabs##s(a.f);              break;         \
        case LIR_FNEG:  r.f = -a.f;                      break;         \
        case LIR_FMA:   r.f = fma##s(a.f, b.f, c.f);     break;         \
        }

        if (cls == LIR_F32) {
                FOPS(f32, f)
        } else {
                FOPS(f64, )
        }

#undef FOPS

        return r;
}

static LirScalar
itof(LirMachine const *m, LirInst const *in, LirClass cls)
{
        LirClass  src = operand_class(m, in->args[0]);
        LirScalar a   = operand(m, in->args[0], src);
        bool      u   = (in->op == LIR_U2F);

        if (cls == LIR_F32) {
                return (LirScalar) { .f32 = u ? (float)a.u : (float)sext(a, src) };
        }

        return (LirScalar) { .f64 = u ? (double)a.u : (double)sext(a, src) };
}

static LirScalar
ftoi(LirMachine const *m, LirInst const *in, LirClass cls)
{
        LirClass src = operand_class(m, in->args[0]);
        double   f   = floating(operand(m, in->args[0], src), src);
        double   lim = (cls == LIR_I32) ? 0x1p31 : 0x1p63;
        i64      min = (cls == LIR_I32) ? INT32_MIN : INT64_MIN;
        bool     ok  = isfinite(f) && (f >= -lim) && (f < lim);

        return (LirScalar) { .i = ok ? (i64)f : min };
}

static LirScalar
load(LirOp op, void const *p)
{
        LirType   type = LirOps[op].type;
        LirScalar r    = {0};

        memcpy(&r, p, lir_type_size(type));

        return narrow(r, type);
}

static void
store(LirOp op, void *p, LirScalar a)
{
        memcpy(p, &a, lir_type_size(LirOps[op].type));
}

static LirScalar
atomic_op(LirOp op, void *p, LirScalar a, LirScalar b, LirClass cls)
{
#define ATOMIC(T) {                                                             \
                T *q = p;                                                       \
                T  x = a.u;                                                     \
                switch (op) {                                                   \
                case LIR_CAS:                                                   \
                        __atomic_compare_exchange_n(                            \
                                q,                                              \
                                &x,                                             \
                                (T)b.u,                                         \
                                false,                                          \
                                __ATOMIC_SEQ_CST,                               \
                                __ATOMIC_SEQ_CST                                \
                        );                                                      \
                        return word(x);                                         \
                case LIR_XADD:                                                  \
                        return word(__atomic_fetch_add(q, x, __ATOMIC_SEQ_CST)); \
                default:                                                        \
                        return word(__atomic_exchange_n(q, x, __ATOMIC_SEQ_CST)); \
                }                                                               \
        }

        if (cls == LIR_I32) {
                ATOMIC(u32)
        }

        ATOMIC(u64)

#undef ATOMIC
}

static void
root_refs(LirMachine *m)
{
        if (m->nrefs == 0) {
                return;
        }

        Value *out = vv(m->ty->stack) + m->rbase;

        for (u32 r = 0; r < vN(m->L->regs); ++r) {
                if (rcls(m->L, r) == LIR_REF) {
                        void *p = m->regs[r].ptr;
                        *out++ = (Value) {
                                .type  = VALUE_PTR,
                                .ptr   = p,
                                .gcptr = p,
                                .extra = &LirRefRoot
                        };
                }
        }
}

static void
rebase_regs(LirMachine *m, StackMark old, LirReg dst)
{
        if (m->ty == NULL || old.base == (uptr)vv(m->ty->stack)) {
                return;
        }

        for (u32 r = 0; r < vN(m->L->regs); ++r) {
                if (r != dst && rcls(m->L, r) == LIR_PTR) {
                        rebase(m->ty, old, &m->regs[r]);
                }
        }

        if (m->L->nvslots != 0) {
                m->vslots = vv(m->ty->stack) + m->vbase;
        }
}

static void
promote(LirScalar *a, ffi_type **t, LirType type)
{
        if (type == LT_F32) {
                a->f64 = a->f32;
                *t     = &ffi_type_double;
        } else if (lir_type_size(type) < 4) {
                *t = &ffi_type_sint32;
        }
}

static bool
prepare(ffi_cif *cif, LirSig const *sig, ffi_type **types)
{
        ffi_type  *ret = ctype(sig->ret);
        ffi_status st;

        if (sig->variadic) {
                st = ffi_prep_cif_var(
                        cif,
                        FFI_DEFAULT_ABI,
                        sig->nfixed,
                        sig->nparams,
                        ret,
                        types
                );
        } else {
                st = ffi_prep_cif(cif, FFI_DEFAULT_ABI, sig->nparams, ret, types);
        }

        return st == FFI_OK;
}

static bool
enter(
        Ty *ty,
        Lir const *L,
        LirMode mode,
        LirLabel entry,
        LirScalar const *args,
        u32 nargs,
        LirScalar *out,
        LirError *err
);

static bool
call(LirMachine *m, LirInst const *in, u32 pc, LirScalar *out)
{
        u32        n      = in->ncall_args;
        ffi_type **types  = onstack(ffi_type *, n);
        void     **args   = onstack(void *, n);
        LirScalar *values = onstack(LirScalar, n);
        LirOpnd    target = in->args[0];
        LirCode   *code   = (target.kind == LO_CODE) ? target.code : NULL;
        LirScalar  callee = operand(m, target, LIR_PTR);
        LirScalar  result = {0};
        bool       direct = (code != NULL)
                         && (code->body == NULL)
                         && (code->lir != NULL);
        bool       slots  = (code != NULL)
                         && (code->nvslots != 0)
                         && (code->interp_state == NULL);
        ffi_cif    cif;

        for (u32 i = 0; i < n; ++i) {
                LirType   type = in->sig.params[i];
                LirScalar a    = operand(m, in->call_args[i], lir_type_class(type));
                values[i] = narrow(a, type);
                types[i]  = ctype(type);
                args[i]   = &values[i];
                if (in->sig.variadic && i >= in->sig.nfixed) {
                        promote(&values[i], &types[i], type);
                }
        }

        if (!direct && callee.ptr == NULL) {
                return bad(m, pc, "null call target");
        }

        if (!direct && !prepare(&cif, &in->sig, types)) {
                return bad(m, pc, "libffi rejected the call signature");
        }

        root_refs(m);

        LirRuntime const *rt    = vmrt(m->ty);
        LirEntryFrame     frame = {0};
        StackMark         old   = mark(m->ty);

        if (slots) {
                if (rt == NULL) {
                        return bad(m, pc, "callee value slots require a VM runtime");
                }
                rt->reserve(m->ty, &frame, code->nvslots);
                rebase_regs(m, old, LIR_NONE);
                for (u32 i = 0; i < n; ++i) {
                        if (lir_type_class(in->sig.params[i]) == LIR_PTR) {
                                rebase(m->ty, old, &values[i]);
                        }
                }
                old = mark(m->ty);
        }

        bool ok = true;

        if (direct) {
                ok = enter(
                        m->ty,
                        code->lir,
                        code->mode,
                        LIR_NONE,
                        values,
                        n,
                        &result,
                        m->err
                );
        } else {
                ffi_call(&cif, FFI_FN(callee.ptr), &result, args);
        }

        rebase_regs(m, old, in->dst);

        if (ok && m->returns[pc] != LIR_NONE) {
                Value *slot = vv(m->ty->stack) + m->rbase + m->nrefs + m->returns[pc];
                *slot = *(Value *)result.ptr;
                result = addr(slot);
        }

        if (slots) {
                rt->restore(m->ty, &frame);
        }

        *out = (in->sig.ret == LT_VOID) ? word(0) : narrow(result, in->sig.ret);

        return ok;
}

static bool
safepoint(LirMachine *m, LirInst const *in, u32 pc, bool *deopt)
{
        LirRuntime const *rt   = lir_runtime();
        Ty               *ty   = m->ty;
        Value            *top  = (ty == NULL) ? NULL : vZ(ty->stack);
        void const       *info = NULL;

        *deopt = false;

        if (rt == NULL || rt->interrupt == NULL || rt->poll == NULL) {
                return bad(m, pc, "POLL requires a VM runtime");
        }

        if (*rt->interrupt == 0) {
                return true;
        }

        if (in != NULL && in->nargs == 4) {
                ty   = arg(m, in, 0, LIR_PTR).ptr;
                top  = arg(m, in, 1, LIR_PTR).ptr;
                info = arg(m, in, 2, LIR_PTR).ptr;
        }

        root_refs(m);

        StackMark old = mark(m->ty);

        *deopt = rt->poll(ty, top, info) != 0;
        rebase_regs(m, old, LIR_NONE);

        return true;
}

static bool
run(LirMachine *m, u32 pc);

static bool
returns_twice(LirMachine *m, LirInst const *in, u32 pc)
{
        jmp_buf      *env     = operand(m, in->call_args[0], LIR_PTR).ptr;
        i32           result  = _setjmp(*env);
        volatile u32  barrier = 0;

        if (in->dst != LIR_NONE) {
                m->regs[in->dst].i = result;
        }

        bool ok = run(m, pc + 1);

        barrier += 1;

        return ok && barrier == 1;
}

static bool
calls_setjmp(LirInst const *in, void const *callee)
{
        return (in->flags & LIR_RETURNS_TWICE)
            && (callee == (void *)_setjmp)
            && (in->ncall_args == 1)
            && (in->sig.params[0] == LT_PTR)
            && (in->sig.ret == LT_I32);
}

static bool
run(LirMachine *m, u32 pc)
{
        Lir const *L   = m->L;
        LirType    ret = L->sig.ret;

#define A(i) arg(m, in, (i), cls)
#define P(i) arg(m, in, (i), LIR_PTR).ptr

        while (pc < vN(L->insts)) {
                LirInst const *in     = v_(L->insts, pc);
                LirForm        form   = LirOps[in->op].form;
                LirClass       cls    = (in->dst == LIR_NONE) ? LIR_I64 : rcls(L, in->dst);
                LirScalar      result = {0};
                LirScalar      a;
                LirLabel       target = LIR_NONE;
                bool           branch = false;

                if (form == LF_RAW) {
                        return bad(m, pc, "RAW cannot execute in the reference interpreter");
                }

                for (u32 i = 0; i < in->nargs; ++i) {
                        if (ishole(in->args[i])) {
                                return bad(m, pc, "unfilled hole in executable LIR");
                        }
                }

                switch (form) {
                case LF_MOV:
                case LF_LI:
                case LF_FLI:
                case LF_LEA:
                        result = A(0);
                        break;

                case LF_IBINARY:
                        result = integer_binary(in->op, A(0), A(1), cls);
                        break;

                case LF_IUNARY:
                        result = integer_unary(in->op, A(0), cls);
                        break;

                case LF_CHECKED:
                        branch = checked(in->op, A(0), A(1), cls, &result);
                        target = in->args[2].label;
                        break;

                case LF_FBINARY:
                case LF_FUNARY:
                case LF_FMA:
                        result = float_op(in->op, A(0), A(1), A(2), cls);
                        break;

                case LF_I2F:
                        result = itof(m, in, cls);
                        break;

                case LF_F2I:
                        result = ftoi(m, in, cls);
                        break;

                case LF_FEXT:
                        result.f64 = arg(m, in, 0, LIR_F32).f32;
                        break;

                case LF_FTRUNC:
                        result.f32 = arg(m, in, 0, LIR_F64).f64;
                        break;

                case LF_BITCAST:
                        result = natural(m, in->args[0]);
                        if (cls == LIR_F32 || cls == LIR_I32) {
                                result.u = (u32)result.u;
                        }
                        break;

                case LF_LD:
                        result = load(in->op, P(0));
                        break;

                case LF_ST:
                        a = arg(m, in, 1, lir_type_class(LirOps[in->op].type));
                        store(in->op, P(0), a);
                        break;

                case LF_SETCC:
                case LF_FSETCC:
                case LF_SELECT:
                case LF_FSELECT:
                case LF_BR:
                case LF_FBR: {
                        LirClass  src  = compare_class(m, in);
                        LirScalar x    = arg(m, in, 1, src);
                        LirScalar y    = arg(m, in, 2, src);
                        bool      test = condition(in->args[0].cc, x, y, src);
                        if (form == LF_BR || form == LF_FBR) {
                                branch = test;
                                target = in->args[3].label;
                        } else if (form == LF_SELECT || form == LF_FSELECT) {
                                result = A(test ? 3 : 4);
                        } else {
                                result = word(test);
                        }
                        break;
                }

                case LF_BRZ:
                        branch = (in->op == LIR_BRZ) == (natural(m, in->args[0]).u == 0);
                        target = in->args[1].label;
                        break;

                case LF_JMP:
                        branch = true;
                        target = in->args[0].label;
                        break;

                case LF_SWITCH:
                        a      = natural(m, in->args[0]);
                        branch = true;
                        target = (a.u < in->ntargets) ? in->targets[a.u] : in->args[1].label;
                        break;

                case LF_RET:
                        *m->out = narrow(arg(m, in, 0, lir_type_class(ret)), ret);
                        return true;

                case LF_CALL:
                case LF_TAILCALL:
                        if (calls_setjmp(in, P(0))) {
                                return returns_twice(m, in, pc);
                        }
                        for (u32 i = 0; i < in->ncall_args; ++i) {
                                if (ishole(in->call_args[i])) {
                                        return bad(m, pc, "unfilled call argument hole");
                                }
                        }
                        if (!call(m, in, pc, &result)) {
                                return false;
                        }
                        if (in->flags & LIR_NORETURN) {
                                return bad(m, pc, "NORETURN callee returned");
                        }
                        if (form == LF_TAILCALL) {
                                *m->out = narrow(result, ret);
                                return true;
                        }
                        break;

                case LF_CAS:
                case LF_ATOMIC:
                        result = atomic_op(in->op, P(0), A(1), A(2), cls);
                        break;

                case LF_FENCE:
                        __atomic_thread_fence(__ATOMIC_SEQ_CST);
                        break;

                case LF_COPY:
                        memmove(P(0), P(1), 32);
                        break;

                case LF_ALLOCA:
                        result = addr(m->frame + m->slots[pc]);
                        break;

                case LF_POLL:
                        if (!safepoint(m, in, pc, &branch)) {
                                return false;
                        }
                        target = in->args[in->nargs - 1].label;
                        break;

                case LF_SITE:
                case LF_ENTRY:
                case LF_RAW:
                        break;
                }

                if (in->dst != LIR_NONE) {
                        m->regs[in->dst] = (cls == LIR_I32) ? word((u32)result.u) : result;
                }

                if (!branch) {
                        pc += 1;
                        continue;
                }

                u32  next = v__(L->labels, target).pos;
                bool deopt;

                if (
                        (next <= pc)
                     && (m->mode == LIR_MODE_ATTACHED)
                     && (in->op != LIR_POLL)
                     && !safepoint(m, NULL, pc, &deopt)
                ) {
                        return false;
                }

                pc = next;
        }

#undef P
#undef A

        *m->out = word(0);

        return true;
}

static bool
layout(LirMachine *m, usize *size, usize *align)
{
        Lir const *L = m->L;

        *size  = 0;
        *align = 8;

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (in->op != LIR_ALLOCA) {
                        continue;
                }
                usize n = in->args[0].imm;
                usize a = in->args[1].imm;
                if (*size > SIZE_MAX - (a - 1) || *size + a - 1 > SIZE_MAX - n) {
                        return bad(m, pc, "frame size overflow");
                }
                *size        = (*size + a - 1) & ~(a - 1);
                m->slots[pc] = *size;
                *size       += n;
                *align       = zmaxu(*align, a);
        }

        if (*size > SIZE_MAX - *align) {
                return lir_fail(m->err, LE_TARGET, LIR_NOWHERE, "frame size overflow");
        }

        return true;
}

static void
count_roots(LirMachine *m)
{
        Lir const *L = m->L;

        for (u32 r = 0; r < vN(L->regs); ++r) {
                m->nrefs += (rcls(L, r) == LIR_REF);
        }

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (
                        (in->op == LIR_CALL || in->op == LIR_TAILCALL)
                     && (in->args[0].kind == LO_CODE)
                     && (in->sig.ret == LT_VAL)
                     && (in->dst != LIR_NONE || in->op == LIR_TAILCALL)
                ) {
                        m->returns[pc] = m->nresults++;
                }
        }
}

static bool
enter(
        Ty *ty,
        Lir const *L,
        LirMode mode,
        LirLabel entry,
        LirScalar const *args,
        u32 nargs,
        LirScalar *out,
        LirError *err
)
{
        LirMachine m     = { .ty = ty, .L = L, .mode = mode, .out = out, .err = err };
        u32        start = 0;
        usize      size;
        usize      align;

        if (out == NULL || nargs != L->sig.nparams || (nargs != 0 && args == NULL)) {
                return lir_fail(
                        err,
                        LE_SIGNATURE,
                        LIR_NOWHERE,
                        "interpreter arguments do not match signature"
                );
        }

        if (entry != LIR_NONE) {
                if (entry >= vN(L->labels) || !v__(L->labels, entry).entry) {
                        return lir_fail(
                                err,
                                LE_ENTRY,
                                LIR_NOWHERE,
                                "invalid interpreter resume entry"
                        );
                }
                start = v__(L->labels, entry).pos;
        }

        if (L->nvslots != 0) {
                if (ty == NULL || vN(ty->stack) < L->nvslots) {
                        return lir_fail(
                                err,
                                LE_MODE,
                                LIR_NOWHERE,
                                "entry has not reserved value slots"
                        );
                }
                m.vbase  = vN(ty->stack) - L->nvslots;
                m.vslots = vv(ty->stack) + m.vbase;
        }

        m.regs    = onstack0(LirScalar, vN(L->regs));
        m.slots   = onstack(usize, vN(L->insts));
        m.returns = memset(onstack(u32, vN(L->insts)), 0xff, vN(L->insts) * sizeof (u32));

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirRegInfo const *ri = v_(L->regs, r);
                if (ri->param != LIR_NONE) {
                        m.regs[r] = narrow(args[ri->param], L->sig.params[ri->param]);
                }
        }

        if (!layout(&m, &size, &align)) {
                return false;
        }

        m.frame = ALIGNED_TO(__builtin_alloca(size + align), align);

        LirRuntime const *rt    = vmrt(ty);
        LirEntryFrame     roots = {0};

        if (rt != NULL) {
                count_roots(&m);
        }

        bool rooted = (m.nrefs != 0) || (m.nresults != 0);

        if (rooted) {
                StackMark old = mark(ty);
                rt->reserve(ty, &roots, m.nrefs + m.nresults);
                m.rbase = roots.top;
                rebase_regs(&m, old, LIR_NONE);
                root_refs(&m);
        }

        bool ok = run(&m, start);

        if (rooted) {
                rt->restore(ty, &roots);
        }

        return ok;
}

bool
lir_interpret_entry(
        Ty *ty,
        Lir const *L,
        LirLabel entry,
        LirScalar const *args,
        u32 nargs,
        LirScalar *out,
        LirError *err
)
{
        Lir copy = *L;

        if (!lir_validate(ty, &copy, err)) {
                return false;
        }

        return enter(ty, L, copy.resolved_mode, entry, args, nargs, out, err);
}

bool
lir_interpret(
        Ty *ty,
        Lir const *L,
        LirScalar const *args,
        u32 nargs,
        LirScalar *out,
        LirError *err
)
{
        return lir_interpret_entry(ty, L, LIR_NONE, args, nargs, out, err);
}

inline static u32
abi_size(LirType type)
{
        return (type == LT_VAL) ? sizeof (void *) : lir_type_size(type);
}

static void
interp_closure(ffi_cif *cif, void *result, void **args, void *data)
{
        LirInterpCode const *code     = data;
        Lir const           *L        = code->L;
        LirSig const        *sig      = &L->sig;
        LirScalar           *values   = onstack0(LirScalar, sig->nparams);
        LirRuntime const    *rt       = lir_runtime();
        LirScalar            out      = {0};
        LirError             err      = {0};
        LirEntryFrame        slots    = {0};
        bool                 reserved = false;
        Ty                  *ty       = NULL;

        if (rt != NULL && rt->current_ty != NULL) {
                ty = rt->current_ty();
        }

        for (u32 i = 0; i < sig->nparams; ++i) {
                memcpy(&values[i], args[i], abi_size(sig->params[i]));
        }

        if (L->nvslots != 0) {
                if (vmrt(ty) == NULL) {
                        lir_fail(
                                &err,
                                LE_MODE,
                                LIR_NOWHERE,
                                "interpreter value slots require a VM runtime"
                        );
                        goto Fail;
                }
                StackMark old = mark(ty);
                rt->reserve(ty, &slots, L->nvslots);
                reserved = true;
                for (u32 i = 0; i < sig->nparams; ++i) {
                        if (lir_type_class(sig->params[i]) == LIR_PTR) {
                                rebase(ty, old, &values[i]);
                        }
                }
        }

        if (!enter(ty, L, code->mode, LIR_NONE, values, sig->nparams, &out, &err)) {
                goto Fail;
        }

        if (reserved) {
                rt->restore(ty, &slots);
        }

        if (sig->ret != LT_VOID) {
                memcpy(result, &out, abi_size(sig->ret));
        }

        return;

Fail:
        if (reserved) {
                rt->restore(ty, &slots);
        }

        if (rt != NULL && rt->interpret_error != NULL) {
                rt->interpret_error(ty, &err);
        }

        fprintf(stderr, "LIR interpreter: %s\n", err.message);
        abort();
}

bool
lir_interp_emit(LirCode *code, LirError *err)
{
        Lir const    *L   = code->lir;
        LirSig const *sig = &code->sig;

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (in->op == LIR_RAW) {
                        return lir_fail(
                                err,
                                LE_TARGET,
                                pc,
                                in->span,
                                "RAW cannot execute in the reference interpreter"
                        );
                }
        }

        LirInterpCode *state = alloc0(sizeof *state + sig->nparams * sizeof *state->types);

        state->L    = L;
        state->mode = code->mode;
        code->interp_state = state;

        for (u32 i = 0; i < sig->nparams; ++i) {
                state->types[i] = ctype(sig->params[i]);
        }

        if (sig->variadic || !prepare(&state->cif, sig, state->types)) {
                goto Fail;
        }

        state->closure = ffi_closure_alloc(sizeof *state->closure, &code->body);

        if (
                (state->closure == NULL)
             || ffi_prep_closure_loc(
                        state->closure,
                        &state->cif,
                        interp_closure,
                        state,
                        code->body
                ) != FFI_OK
        ) {
                goto Fail;
        }

        return true;

Fail:
        return lir_fail(
                err,
                LE_TARGET,
                LIR_NOWHERE,
                "could not create interpreter call interface"
        );
}

void
lir_interp_destroy(LirCode *code)
{
        LirInterpCode *state = code->interp_state;

        if (state == NULL) {
                return;
        }

        if (state->closure != NULL) {
                ffi_closure_free(state->closure);
        }

        xmF(state);
        code->interp_state = NULL;
}
