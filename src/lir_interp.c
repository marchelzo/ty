#include <math.h>
#include <limits.h>
#include <stdatomic.h>
#include <setjmp.h>

#include "ty.h"
#include "lir.h"

#define LIR_STACK_ALLOC(n) __builtin_alloca(n)

typedef struct lir_machine {
        Ty *ty;
        Lir const *L;
        LirScalar *regs;
        u8 *frame;
        usize *slots;
        Value *vslots;
        usize vbase;
        usize rbase;
        u32 nrefs;
        u32 nresults;
        u32 *returns;
        LirScalar *out;
        LirError *err;
        LirMode mode;
} LirMachine;

static bool
interp_fail(LirMachine *m, u32 pc, char const *message)
{
        if (m->err != NULL) {
                *m->err = (LirError) {
                        .kind = LIR_ERROR_TARGET, .op = pc,
                        .span = m->L->insts[pc].span
                };
                snprintf(m->err->message, sizeof m->err->message, "%s", message);
        }
        return false;
}

static LirScalar
ref_value(Value const *v)
{
        LirScalar result = {0};
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_OBJECT: result.ptr = v->object; break;
        case VALUE_TUPLE:  result.ptr = v->items; break;
        case VALUE_STRING: result.ptr = v->str0 == NULL ? (void *)v->str : v->str0; break;
        default: result.ptr = v->ptr; break;
        }
        return result;
}

static LirClass
operand_class(LirMachine const *m, LirOpnd a)
{
        switch (a.kind) {
        case LIR_OPERAND_REG: return m->L->regs[a.reg].cls;
        case LIR_OPERAND_FIMM: return LIR_F64;
        case LIR_OPERAND_CONST:
        case LIR_OPERAND_VSLOT:
        case LIR_OPERAND_MEM: return LIR_PTR;
        case LIR_OPERAND_REFCONST: return LIR_REF;
        default: return LIR_I64;
        }
}

static LirScalar
operand(LirMachine const *m, LirOpnd a, LirClass cls)
{
        LirScalar result = {0};
        switch (a.kind) {
        case LIR_OPERAND_REG: return m->regs[a.reg];
        case LIR_OPERAND_IMM:
                result.u = cls == LIR_I32 ? (u32)a.imm : (u64)a.imm;
                break;
        case LIR_OPERAND_FIMM:
                if (cls == LIR_F32) {
                        result.f32 = a.fimm;
                } else {
                        result.f64 = a.fimm;
                }
                break;
        case LIR_OPERAND_MEM:
                result.u = m->regs[a.mem.base].u + (u64)(i64)a.mem.disp;
                if (a.mem.index != LIR_NONE) {
                        u64 index = m->regs[a.mem.index].u;
                        if (m->L->regs[a.mem.index].cls == LIR_I32) {
                                index = (u32)index;
                        }
                        result.u += index * a.mem.scale;
                }
                break;
        case LIR_OPERAND_CONST:
                result.ptr = &m->L->roots[a.index];
                break;
        case LIR_OPERAND_REFCONST:
                return ref_value(&m->L->roots[a.index]);
        case LIR_OPERAND_VSLOT:
                result.ptr = &m->vslots[a.index];
                break;
        case LIR_OPERAND_CODE:
                result.ptr = a.code->body;
                break;
        case LIR_OPERAND_HELPER:
                result.ptr = a.helper->address;
                break;
        default:
                break;
        }
        return result;
}

static double
floating(LirScalar a, LirClass cls)
{
        return cls == LIR_F32 ? a.f32 : a.f64;
}

static i64
signed_int(LirScalar a, LirClass cls)
{
        return cls == LIR_I32 ? (i32)a.u : a.i;
}

static LirScalar
narrow(LirScalar a, LirType type)
{
        switch (type) {
        case LIR_TYPE_I8:   a.i = (i8)a.u; break;
        case LIR_TYPE_U8:   a.u = (u8)a.u; break;
        case LIR_TYPE_I16:  a.i = (i16)a.u; break;
        case LIR_TYPE_U16:  a.u = (u16)a.u; break;
        case LIR_TYPE_I32:  a.i = (i32)a.u; break;
        case LIR_TYPE_U32:  a.u = (u32)a.u; break;
        case LIR_TYPE_BOOL: a.u = a.u != 0; break;
        default: break;
        }
        return a;
}

static LirClass
compare_class(LirMachine const *m, LirInst const *in)
{
        if (in->args[1].kind != LIR_OPERAND_REG && in->args[2].kind == LIR_OPERAND_REG) {
                return operand_class(m, in->args[2]);
        }
        return operand_class(m, in->args[1]);
}

static bool
condition(LirCC cc, LirScalar a, LirScalar b, LirClass cls)
{
        i64 x = signed_int(a, cls);
        i64 y = signed_int(b, cls);
        u64 u = cls == LIR_I32 ? (u32)a.u : a.u;
        u64 v = cls == LIR_I32 ? (u32)b.u : b.u;
        double f;
        double g;
        if (cc < LIR_FEQ) {
                switch (cc) {
                case LIR_EQ:  return u == v;
                case LIR_NE:  return u != v;
                case LIR_LT:  return x < y;
                case LIR_LE:  return x <= y;
                case LIR_GT:  return x > y;
                case LIR_GE:  return x >= y;
                case LIR_ULT: return u < v;
                case LIR_ULE: return u <= v;
                case LIR_UGT: return u > v;
                case LIR_UGE: return u >= v;
                default: return false;
                }
        }
        f = floating(a, cls);
        g = floating(b, cls);
        switch (cc) {
        case LIR_FEQ: return f == g;
        case LIR_FNE: return f != g;
        case LIR_FLT: return f < g;
        case LIR_FLE: return f <= g;
        case LIR_FGT: return f > g;
        case LIR_FGE: return f >= g;
        case LIR_FUN: return isnan(f) || isnan(g);
        default: return false;
        }
}

static LirScalar
integer_binary(LirOp op, LirScalar a, LirScalar b, LirClass cls)
{
        LirScalar result = {0};
        u64 x = cls == LIR_I32 ? (u32)a.u : a.u;
        u64 y = cls == LIR_I32 ? (u32)b.u : b.u;
        i64 s = signed_int(a, cls);
        i64 t = signed_int(b, cls);
        u32 bits = cls == LIR_I32 ? 32 : 64;
        u32 shift = y & (bits - 1);
        i64 min = cls == LIR_I32 ? INT32_MIN : INT64_MIN;
        switch (op) {
        case LIR_ADD: result.u = x + y; break;
        case LIR_SUB: result.u = x - y; break;
        case LIR_MUL: result.u = x * y; break;
        case LIR_MULHS:
                result.u = (unsigned __int128)((__int128)s * t) >> bits;
                break;
        case LIR_MULHU:
                result.u = ((unsigned __int128)x * y) >> bits;
                break;
        case LIR_SDIV:
                if (t == 0) {
                        result.i = 0;
                } else if (s == min && t == -1) {
                        result.i = min;
                } else {
                        result.i = s / t;
                }
                break;
        case LIR_SREM:
                if (t == 0) {
                        result.i = s;
                } else if (s == min && t == -1) {
                        result.i = 0;
                } else {
                        result.i = s % t;
                }
                break;
        case LIR_UDIV: result.u = y == 0 ? 0 : x / y; break;
        case LIR_UREM: result.u = y == 0 ? x : x % y; break;
        case LIR_AND:  result.u = x & y; break;
        case LIR_OR:   result.u = x | y; break;
        case LIR_XOR:  result.u = x ^ y; break;
        case LIR_SHL:  result.u = x << shift; break;
        case LIR_SHR:  result.u = x >> shift; break;
        case LIR_SAR:  result.i = s >> shift; break;
        case LIR_ROTR: result.u = (x >> shift) | (x << ((-shift) & (bits - 1))); break;
        default: break;
        }
        if (cls == LIR_I32) {
                result.u = (u32)result.u;
        }
        return result;
}

static LirScalar
integer_unary(LirOp op, LirScalar a, LirClass cls)
{
        LirScalar result = {0};
        u64 x = cls == LIR_I32 ? (u32)a.u : a.u;
        u32 bits = cls == LIR_I32 ? 32 : 64;
        switch (op) {
        case LIR_NEG: result.u = -x; break;
        case LIR_NOT: result.u = ~x; break;
        case LIR_CLZ:
                if (x == 0) {
                        result.u = bits;
                } else {
                        result.u = cls == LIR_I32 ? __builtin_clz((u32)x) : __builtin_clzll(x);
                }
                break;
        case LIR_CTZ:
                if (x == 0) {
                        result.u = bits;
                } else {
                        result.u = cls == LIR_I32 ? __builtin_ctz((u32)x) : __builtin_ctzll(x);
                }
                break;
        case LIR_POPCNT: result.u = __builtin_popcountll(x); break;
        case LIR_BSWAP: result.u = cls == LIR_I32 ? __builtin_bswap32(x) : __builtin_bswap64(x); break;
        case LIR_SEXT8:  result.i = (i8)x; break;
        case LIR_SEXT16: result.i = (i16)x; break;
        case LIR_SEXT32: result.i = (i32)x; break;
        case LIR_ZEXT8:  result.u = (u8)x; break;
        case LIR_ZEXT16: result.u = (u16)x; break;
        case LIR_ZEXT32: result.u = (u32)x; break;
        default: break;
        }
        if (cls == LIR_I32) {
                result.u = (u32)result.u;
        }
        return result;
}

static bool
checked(LirOp op, LirScalar a, LirScalar b, LirClass cls, LirScalar *result)
{
        i32 z;
        bool overflow;
        if (cls == LIR_I32) {
                switch (op) {
                case LIR_ADDO: overflow = __builtin_add_overflow((i32)a.u, (i32)b.u, &z); break;
                case LIR_SUBO: overflow = __builtin_sub_overflow((i32)a.u, (i32)b.u, &z); break;
                default:      overflow = __builtin_mul_overflow((i32)a.u, (i32)b.u, &z); break;
                }
                result->u = (u32)z;
        } else {
                switch (op) {
                case LIR_ADDO: overflow = __builtin_add_overflow(a.i, b.i, &result->i); break;
                case LIR_SUBO: overflow = __builtin_sub_overflow(a.i, b.i, &result->i); break;
                default:      overflow = __builtin_mul_overflow(a.i, b.i, &result->i); break;
                }
        }
        return overflow;
}

static LirScalar
float_op(LirOp op, LirScalar a, LirScalar b, LirScalar c, LirClass cls)
{
        LirScalar result = {0};
        if (cls == LIR_F32) {
                switch (op) {
                case LIR_FADD:  result.f32 = a.f32 + b.f32; break;
                case LIR_FSUB:  result.f32 = a.f32 - b.f32; break;
                case LIR_FMUL:  result.f32 = a.f32 * b.f32; break;
                case LIR_FDIV:  result.f32 = a.f32 / b.f32; break;
                case LIR_FMIN:  result.f32 = fminf(a.f32, b.f32); break;
                case LIR_FMAX:  result.f32 = fmaxf(a.f32, b.f32); break;
                case LIR_FSQRT: result.f32 = sqrtf(a.f32); break;
                case LIR_FABS:  result.f32 = fabsf(a.f32); break;
                case LIR_FNEG:  result.f32 = -a.f32; break;
                case LIR_FMA:   result.f32 = fmaf(a.f32, b.f32, c.f32); break;
                default: break;
                }
        } else {
                switch (op) {
                case LIR_FADD:  result.f64 = a.f64 + b.f64; break;
                case LIR_FSUB:  result.f64 = a.f64 - b.f64; break;
                case LIR_FMUL:  result.f64 = a.f64 * b.f64; break;
                case LIR_FDIV:  result.f64 = a.f64 / b.f64; break;
                case LIR_FMIN:  result.f64 = fmin(a.f64, b.f64); break;
                case LIR_FMAX:  result.f64 = fmax(a.f64, b.f64); break;
                case LIR_FSQRT: result.f64 = sqrt(a.f64); break;
                case LIR_FABS:  result.f64 = fabs(a.f64); break;
                case LIR_FNEG:  result.f64 = -a.f64; break;
                case LIR_FMA:   result.f64 = fma(a.f64, b.f64, c.f64); break;
                default: break;
                }
        }
        return result;
}

static LirScalar
load(LirOp op, void const *p)
{
        LirScalar result = {0};
        i8 s8;
        u8 u8v;
        i16 s16;
        u16 u16v;
        i32 s32;
        u32 u32v;
        switch (op) {
        case LIR_LD_I8:  memcpy(&s8, p, sizeof s8); result.i = s8; break;
        case LIR_LD_U8:  memcpy(&u8v, p, sizeof u8v); result.u = u8v; break;
        case LIR_LD_I16: memcpy(&s16, p, sizeof s16); result.i = s16; break;
        case LIR_LD_U16: memcpy(&u16v, p, sizeof u16v); result.u = u16v; break;
        case LIR_LD_I32: memcpy(&s32, p, sizeof s32); result.i = s32; break;
        case LIR_LD_U32: memcpy(&u32v, p, sizeof u32v); result.u = u32v; break;
        case LIR_LD_I64: memcpy(&result.u, p, sizeof result.u); break;
        case LIR_LD_F32: memcpy(&result.f32, p, sizeof result.f32); break;
        case LIR_LD_F64: memcpy(&result.f64, p, sizeof result.f64); break;
        default: break;
        }
        return result;
}

static void
store(LirOp op, void *p, LirScalar a)
{
        u8 u8v = a.u;
        u16 u16v = a.u;
        u32 u32v = a.u;
        switch (op) {
        case LIR_ST8:    memcpy(p, &u8v, sizeof u8v); break;
        case LIR_ST16:   memcpy(p, &u16v, sizeof u16v); break;
        case LIR_ST32:   memcpy(p, &u32v, sizeof u32v); break;
        case LIR_ST64:   memcpy(p, &a.u, sizeof a.u); break;
        case LIR_ST_F32: memcpy(p, &a.f32, sizeof a.f32); break;
        case LIR_ST_F64: memcpy(p, &a.f64, sizeof a.f64); break;
        default: break;
        }
}

static ffi_type *
ctype(LirType type)
{
        switch (type) {
        case LIR_VOID: return &ffi_type_void;
        case LIR_TYPE_I8: return &ffi_type_sint8;
        case LIR_TYPE_U8:
        case LIR_TYPE_BOOL: return &ffi_type_uint8;
        case LIR_TYPE_I16: return &ffi_type_sint16;
        case LIR_TYPE_U16: return &ffi_type_uint16;
        case LIR_TYPE_I32: return &ffi_type_sint32;
        case LIR_TYPE_U32: return &ffi_type_uint32;
        case LIR_TYPE_I64: return &ffi_type_sint64;
        case LIR_TYPE_U64: return &ffi_type_uint64;
        case LIR_TYPE_F32: return &ffi_type_float;
        case LIR_TYPE_F64: return &ffi_type_double;
        default: return &ffi_type_pointer;
        }
}

static void
root_refs(LirMachine *m)
{
        if (m->nrefs == 0) {
                return;
        }
        u32 n = 0;
        for (u32 r = 0; r < m->L->nregs; ++r) {
                if (m->L->regs[r].cls == LIR_REF) {
                        void *p = m->regs[r].ptr;
                        m->ty->stack.items[m->rbase + n++] = (Value) {
                                .type = VALUE_PTR, .ptr = p, .gcptr = p, .extra = &LirRefRoot
                        };
                }
        }
}

static void
rebase_regs(LirMachine *m, uptr base, usize capacity, LirReg dst)
{
        if (m->ty == NULL || base == (uptr)m->ty->stack.items) {
                return;
        }
        uptr end = base + capacity * sizeof (Value);
        for (u32 r = 0; r < m->L->nregs; ++r) {
                uptr p = m->regs[r].u;
                if (r != dst && m->L->regs[r].cls == LIR_PTR && p >= base && p < end) {
                        m->regs[r].u = (uptr)m->ty->stack.items + p - base;
                }
        }
        if (m->L->nvslots != 0) {
                m->vslots = m->ty->stack.items + m->vbase;
        }
}

static bool
call(LirMachine *m, LirInst const *in, u32 pc, LirScalar *out)
{
        ffi_cif cif;
        ffi_status status;
        ffi_type **types = LIR_STACK_ALLOC((usize)in->ncall_args * sizeof *types);
        void **args = LIR_STACK_ALLOC((usize)in->ncall_args * sizeof *args);
        LirScalar *values = LIR_STACK_ALLOC((usize)in->ncall_args * sizeof *values);
        LirOpnd target = in->args[0];
        LirScalar address = operand(m, target, LIR_PTR);
        LirScalar result = {0};
        for (u32 i = 0; i < in->ncall_args; ++i) {
                LirType type = in->sig.params[i];
                LirScalar a = operand(m, in->call_args[i], lir_type_class(type));
                a = narrow(a, type);
                types[i] = ctype(type);
                if (in->sig.variadic && i >= in->sig.nfixed) {
                        if (type == LIR_TYPE_F32) {
                                a.f64 = a.f32;
                                types[i] = &ffi_type_double;
                        } else if ((type >= LIR_TYPE_I8 && type <= LIR_TYPE_U16)
                                   || type == LIR_TYPE_BOOL) {
                                types[i] = &ffi_type_sint32;
                        }
                }
                values[i] = a;
                args[i] = &values[i];
        }
        bool direct = target.kind == LIR_OPERAND_CODE && target.code->body == NULL
                   && target.code->lir != NULL;
        if (!direct) {
                if (address.ptr == NULL) {
                        return interp_fail(m, pc, "null call target");
                }
                if (in->sig.variadic) {
                        status = ffi_prep_cif_var(&cif, FFI_DEFAULT_ABI, in->sig.nfixed, in->sig.nparams,
                                                 ctype(in->sig.ret), types);
                } else {
                        status = ffi_prep_cif(&cif, FFI_DEFAULT_ABI, in->sig.nparams, ctype(in->sig.ret), types);
                }
                if (status != FFI_OK) {
                        return interp_fail(m, pc, "libffi rejected the call signature");
                }
        }
        root_refs(m);
        LirRuntime const *rt = lir_runtime();
        LirEntryFrame frame = {0};
        bool reserve = target.kind == LIR_OPERAND_CODE && target.code->nvslots != 0
                    && target.code->interp_state == NULL;
        uptr base = m->ty == NULL ? 0 : (uptr)m->ty->stack.items;
        usize capacity = m->ty == NULL ? 0 : m->ty->stack.capacity;
        if (reserve) {
                if (m->ty == NULL || rt == NULL || rt->reserve == NULL || rt->restore == NULL) {
                        return interp_fail(m, pc, "callee value slots require a VM runtime");
                }
                rt->reserve(m->ty, &frame, target.code->nvslots);
                rebase_regs(m, base, capacity, LIR_NONE);
                for (u32 i = 0; i < in->ncall_args; ++i) {
                        uptr p = values[i].u;
                        if (lir_type_class(in->sig.params[i]) == LIR_PTR
                            && p >= base && p < base + capacity * sizeof (Value)) {
                                values[i].u = (uptr)m->ty->stack.items + p - base;
                        }
                }
                base = (uptr)m->ty->stack.items;
                capacity = m->ty->stack.capacity;
        }
        bool ok = true;
        if (direct) {
                ok = lir_interpret(m->ty, target.code->lir, values, in->ncall_args, &result, m->err);
        } else {
                ffi_call(&cif, FFI_FN(address.ptr), &result, args);
        }
        rebase_regs(m, base, capacity, in->dst);
        if (ok && m->returns[pc] != LIR_NONE) {
                Value *slot = m->ty->stack.items + m->rbase + m->nrefs + m->returns[pc];
                *slot = *(Value *)result.ptr;
                result.ptr = slot;
        }
        if (reserve) {
                rt->restore(m->ty, &frame);
        }
        if (in->sig.ret == LIR_VOID) {
                result.u = 0;
        }
        *out = narrow(result, in->sig.ret);
        return ok;
}

static bool
poll(LirMachine *m, LirInst const *in, u32 pc, bool *deopt)
{
        LirRuntime const *rt = lir_runtime();
        Ty *ty = m->ty;
        Value *top = ty == NULL || ty->stack.items == NULL
                   ? NULL : ty->stack.items + ty->stack.count;
        void const *info = NULL;
        *deopt = false;
        if (rt == NULL || rt->interrupt == NULL || rt->poll == NULL) {
                return interp_fail(m, pc, "POLL requires a VM runtime");
        }
        if (*rt->interrupt == 0) {
                return true;
        }
        if (in != NULL && in->nargs == 4) {
                ty = operand(m, in->args[0], LIR_PTR).ptr;
                top = operand(m, in->args[1], LIR_PTR).ptr;
                info = operand(m, in->args[2], LIR_PTR).ptr;
        }
        root_refs(m);
        uptr base = m->ty == NULL ? 0 : (uptr)m->ty->stack.items;
        usize capacity = m->ty == NULL ? 0 : m->ty->stack.capacity;
        *deopt = rt->poll(ty, top, info) != 0;
        rebase_regs(m, base, capacity, LIR_NONE);
        return true;
}

static LirScalar
atomic_op(LirOp op, void *p, LirScalar a, LirScalar b, LirClass cls)
{
        LirScalar result = {0};
        if (cls == LIR_I32) {
                u32 expected = a.u;
                if (op == LIR_CAS) {
                        __atomic_compare_exchange_n((u32 *)p, &expected, (u32)b.u, false,
                                                    __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
                        result.u = expected;
                } else if (op == LIR_XADD) {
                        result.u = __atomic_fetch_add((u32 *)p, (u32)a.u, __ATOMIC_SEQ_CST);
                } else {
                        result.u = __atomic_exchange_n((u32 *)p, (u32)a.u, __ATOMIC_SEQ_CST);
                }
        } else {
                u64 expected = a.u;
                if (op == LIR_CAS) {
                        __atomic_compare_exchange_n((u64 *)p, &expected, b.u, false,
                                                    __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST);
                        result.u = expected;
                } else if (op == LIR_XADD) {
                        result.u = __atomic_fetch_add((u64 *)p, a.u, __ATOMIC_SEQ_CST);
                } else {
                        result.u = __atomic_exchange_n((u64 *)p, a.u, __ATOMIC_SEQ_CST);
                }
        }
        return result;
}

static bool
run(LirMachine *m, u32 pc);

static bool
returns_twice(LirMachine *m, LirInst const *in, u32 pc)
{
        jmp_buf *env = operand(m, in->call_args[0], LIR_PTR).ptr;
        i32 result = _setjmp(*env);
        volatile u32 barrier = 0;
        bool ok;
        if (in->dst != LIR_NONE) {
                m->regs[in->dst].i = result;
        }
        ok = run(m, pc + 1);
        ++barrier;
        return ok && barrier == 1;
}

static bool
run(LirMachine *m, u32 pc)
{
        Lir const *L = m->L;
        while (pc < L->ninsts) {
                LirInst const *in = &L->insts[pc];
                LirForm form = LirOps[in->op].form;
                LirClass cls = in->dst == LIR_NONE ? LIR_I64 : L->regs[in->dst].cls;
                LirScalar a = {0};
                LirScalar b = {0};
                LirScalar c = {0};
                LirScalar result = {0};
                bool branch = false;
                LirLabel target = LIR_NONE;
                if (form == LIR_FORM_RAW) {
                        return interp_fail(m, pc, "RAW cannot execute in the reference interpreter");
                }
                for (u32 i = 0; i < in->nargs; ++i) {
                        if (in->args[i].kind >= LIR_HOLE_IMM
                            && in->args[i].kind <= LIR_HOLE_CALLEE) {
                                return interp_fail(m, pc, "unfilled hole in executable LIR");
                        }
                }
                switch (form) {
                case LIR_FORM_MOV:
                case LIR_FORM_LI:
                case LIR_FORM_FLI:
                case LIR_FORM_LEA:
                        result = operand(m, in->args[0], cls);
                        break;
                case LIR_FORM_IBINARY:
                case LIR_FORM_IUNARY:
                case LIR_FORM_CHECKED:
                        a = operand(m, in->args[0], cls);
                        if (in->nargs > 1) {
                                b = operand(m, in->args[1], cls);
                        }
                        if (form == LIR_FORM_IUNARY) {
                                result = integer_unary(in->op, a, cls);
                        } else if (form == LIR_FORM_CHECKED) {
                                branch = checked(in->op, a, b, cls, &result);
                                target = in->args[2].label;
                        } else {
                                result = integer_binary(in->op, a, b, cls);
                        }
                        break;
                case LIR_FORM_FBINARY:
                case LIR_FORM_FUNARY:
                case LIR_FORM_FMA:
                        a = operand(m, in->args[0], cls);
                        if (in->nargs > 1) {
                                b = operand(m, in->args[1], cls);
                        }
                        if (in->nargs > 2) {
                                c = operand(m, in->args[2], cls);
                        }
                        result = float_op(in->op, a, b, c, cls);
                        break;
                case LIR_FORM_I2F: {
                        LirClass src = operand_class(m, in->args[0]);
                        a = operand(m, in->args[0], src);
                        if (cls == LIR_F32) {
                                result.f32 = in->op == LIR_U2F
                                           ? (float)a.u : (float)signed_int(a, src);
                        } else {
                                result.f64 = in->op == LIR_U2F
                                           ? (double)a.u : (double)signed_int(a, src);
                        }
                        break;
                }
                case LIR_FORM_F2I: {
                        LirClass src = operand_class(m, in->args[0]);
                        double f = floating(operand(m, in->args[0], src), src);
                        if (cls == LIR_I32) {
                                result.i = isfinite(f) && f >= -0x1p31 && f < 0x1p31 ? (i32)f : INT32_MIN;
                        } else {
                                result.i = isfinite(f) && f >= -0x1p63 && f < 0x1p63 ? (i64)f : INT64_MIN;
                        }
                        break;
                }
                case LIR_FORM_FEXT:
                        result.f64 = operand(m, in->args[0], LIR_F32).f32;
                        break;
                case LIR_FORM_FTRUNC:
                        result.f32 = operand(m, in->args[0], LIR_F64).f64;
                        break;
                case LIR_FORM_BITCAST:
                        a = operand(m, in->args[0], operand_class(m, in->args[0]));
                        if (cls == LIR_F32) {
                                u32 u = a.u;
                                memcpy(&result.f32, &u, sizeof u);
                        } else if (cls == LIR_I32) {
                                u32 u;
                                memcpy(&u, &a.f32, sizeof u);
                                result.u = u;
                        } else {
                                memcpy(&result, &a, sizeof result);
                        }
                        break;
                case LIR_FORM_LD:
                        a = operand(m, in->args[0], LIR_PTR);
                        result = load(in->op, a.ptr);
                        break;
                case LIR_FORM_ST:
                        a = operand(m, in->args[0], LIR_PTR);
                        b = operand(m, in->args[1], lir_type_class(LirOps[in->op].type));
                        store(in->op, a.ptr, b);
                        break;
                case LIR_FORM_SETCC:
                case LIR_FORM_FSETCC:
                case LIR_FORM_SELECT:
                case LIR_FORM_FSELECT:
                case LIR_FORM_BR:
                case LIR_FORM_FBR: {
                        LirClass src = compare_class(m, in);
                        bool test;
                        a = operand(m, in->args[1], src);
                        b = operand(m, in->args[2], src);
                        test = condition(in->args[0].cc, a, b, src);
                        if (form == LIR_FORM_BR || form == LIR_FORM_FBR) {
                                branch = test;
                                target = in->args[3].label;
                        } else if (form == LIR_FORM_SELECT || form == LIR_FORM_FSELECT) {
                                result = operand(m, in->args[test ? 3 : 4], cls);
                        } else {
                                result.u = test;
                        }
                        break;
                }
                case LIR_FORM_BRZ:
                        a = operand(m, in->args[0], operand_class(m, in->args[0]));
                        branch = in->op == LIR_BRZ ? a.u == 0 : a.u != 0;
                        target = in->args[1].label;
                        break;
                case LIR_FORM_JMP:
                        branch = true;
                        target = in->args[0].label;
                        break;
                case LIR_FORM_SWITCH:
                        a = operand(m, in->args[0], operand_class(m, in->args[0]));
                        branch = true;
                        target = a.u < in->ntargets ? in->targets[a.u] : in->args[1].label;
                        break;
                case LIR_FORM_RET:
                        if (in->nargs != 0) {
                                result = operand(m, in->args[0], lir_type_class(L->sig.ret));
                                *m->out = narrow(result, L->sig.ret);
                        } else {
                                *m->out = (LirScalar) {0};
                        }
                        return true;
                case LIR_FORM_CALL:
                case LIR_FORM_TAILCALL:
                        a = operand(m, in->args[0], LIR_PTR);
                        if ((in->flags & LIR_RETURNS_TWICE) && a.ptr == (void *)_setjmp
                            && in->ncall_args == 1 && in->sig.params[0] == LIR_TYPE_PTR
                            && in->sig.ret == LIR_TYPE_I32) {
                                return returns_twice(m, in, pc);
                        }
                        for (u32 i = 0; i < in->ncall_args; ++i) {
                                if (in->call_args[i].kind >= LIR_HOLE_IMM) {
                                        return interp_fail(m, pc, "unfilled call argument hole");
                                }
                        }
                        if (!call(m, in, pc, &result)) {
                                return false;
                        }
                        if (in->flags & LIR_NORETURN) {
                                return interp_fail(m, pc, "NORETURN callee returned");
                        }
                        if (form == LIR_FORM_TAILCALL) {
                                *m->out = narrow(result, L->sig.ret);
                                return true;
                        }
                        break;
                case LIR_FORM_CAS:
                case LIR_FORM_ATOMIC:
                        a = operand(m, in->args[0], LIR_PTR);
                        b = operand(m, in->args[1], cls);
                        if (in->nargs > 2) {
                                c = operand(m, in->args[2], cls);
                        }
                        result = atomic_op(in->op, a.ptr, b, c, cls);
                        break;
                case LIR_FORM_FENCE:
                        __atomic_thread_fence(__ATOMIC_SEQ_CST);
                        break;
                case LIR_FORM_COPY:
                        a = operand(m, in->args[0], LIR_PTR);
                        b = operand(m, in->args[1], LIR_PTR);
                        memmove(a.ptr, b.ptr, 32);
                        break;
                case LIR_FORM_ALLOCA:
                        result.ptr = m->frame + m->slots[pc];
                        break;
                case LIR_FORM_POLL:
                        if (!poll(m, in, pc, &branch)) {
                                return false;
                        }
                        target = in->args[in->nargs - 1].label;
                        break;
                case LIR_FORM_SITE:
                case LIR_FORM_ENTRY:
                        break;
                case LIR_FORM_RAW:
                        break;
                }
                if (in->dst != LIR_NONE) {
                        if (cls == LIR_I32) {
                                result.u = (u32)result.u;
                        }
                        m->regs[in->dst] = result;
                }
                if (branch) {
                        u32 next = L->labels[target].pos;
                        if (next <= pc && m->mode == LIR_MODE_ATTACHED && in->op != LIR_POLL) {
                                bool deopt;
                                if (!poll(m, NULL, pc, &deopt)) {
                                        return false;
                                }
                        }
                        pc = next;
                } else {
                        ++pc;
                }
        }
        *m->out = (LirScalar) {0};
        return true;
}

bool
lir_interpret_entry(Ty *ty, Lir const *L, LirLabel entry,
                    LirScalar const *args, u32 nargs, LirScalar *out, LirError *err)
{
        Lir checked_lir = *L;
        LirMachine m = { .ty = ty, .L = L, .out = out, .err = err };
        usize frame_size = 0;
        usize align = 8;
        u32 start = 0;
        if (!lir_validate(&checked_lir, err)) {
                return false;
        }
        m.mode = checked_lir.resolved_mode;
        if (out == NULL || nargs != L->sig.nparams || (nargs != 0 && args == NULL)) {
                if (err != NULL) {
                        *err = (LirError) { .kind = LIR_ERROR_SIGNATURE, .op = LIR_NONE };
                        snprintf(err->message, sizeof err->message, "interpreter arguments do not match signature");
                }
                return false;
        }
        if (entry != LIR_NONE) {
                if (entry >= L->nlabels || !L->labels[entry].entry) {
                        if (err != NULL) {
                                *err = (LirError) { .kind = LIR_ERROR_ENTRY, .op = LIR_NONE };
                                snprintf(err->message, sizeof err->message, "invalid interpreter resume entry");
                        }
                        return false;
                }
                start = L->labels[entry].pos;
        }
        if (L->nvslots != 0) {
                if (ty == NULL || ty->stack.count < L->nvslots) {
                        if (err != NULL) {
                                *err = (LirError) { .kind = LIR_ERROR_MODE, .op = LIR_NONE };
                                snprintf(err->message, sizeof err->message, "entry has not reserved value slots");
                        }
                        return false;
                }
                m.vbase = ty->stack.count - L->nvslots;
                m.vslots = ty->stack.items + m.vbase;
        }
        m.regs = LIR_STACK_ALLOC(((usize)L->nregs + 1) * sizeof *m.regs);
        memset(m.regs, 0, ((usize)L->nregs + 1) * sizeof *m.regs);
        m.slots = LIR_STACK_ALLOC(((usize)L->ninsts + 1) * sizeof *m.slots);
        m.returns = LIR_STACK_ALLOC(((usize)L->ninsts + 1) * sizeof *m.returns);
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                m.returns[pc] = LIR_NONE;
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                LirRegInfo const *ri = &L->regs[r];
                if (ri->param != LIR_NONE) {
                        m.regs[r] = narrow(args[ri->param], L->sig.params[ri->param]);
                }
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (in->op == LIR_ALLOCA) {
                        usize n = in->args[0].imm;
                        usize a = in->args[1].imm;
                        if (frame_size > SIZE_MAX - (a - 1) || frame_size + a - 1 > SIZE_MAX - n) {
                                return interp_fail(&m, pc, "frame size overflow");
                        }
                        frame_size = (frame_size + a - 1) & ~(a - 1);
                        m.slots[pc] = frame_size;
                        frame_size += n;
                        if (a > align) {
                                align = a;
                        }
                }
        }
        if (frame_size > SIZE_MAX - align) {
                if (err != NULL) {
                        *err = (LirError) { .kind = LIR_ERROR_MEMORY, .op = LIR_NONE };
                }
                return false;
        }
        void *frame = LIR_STACK_ALLOC(frame_size + align);
        m.frame = (void *)(((uptr)frame + align - 1) & ~(uptr)(align - 1));
        LirEntryFrame roots = {0};
        LirRuntime const *rt = lir_runtime();
        if (ty != NULL && rt != NULL && rt->reserve != NULL && rt->restore != NULL) {
                for (u32 r = 0; r < L->nregs; ++r) {
                        m.nrefs += L->regs[r].cls == LIR_REF;
                }
                for (u32 pc = 0; pc < L->ninsts; ++pc) {
                        LirInst const *in = &L->insts[pc];
                        if ((in->op == LIR_CALL || in->op == LIR_TAILCALL)
                            && in->args[0].kind == LIR_OPERAND_CODE && in->sig.ret == LIR_TYPE_VAL
                            && (in->dst != LIR_NONE || in->op == LIR_TAILCALL)) {
                                m.returns[pc] = m.nresults++;
                        }
                }
                if (m.nrefs != 0 || m.nresults != 0) {
                        uptr base = (uptr)ty->stack.items;
                        usize capacity = ty->stack.capacity;
                        rt->reserve(ty, &roots, m.nrefs + m.nresults);
                        m.rbase = roots.top;
                        rebase_regs(&m, base, capacity, LIR_NONE);
                        root_refs(&m);
                }
        }
        bool ok = run(&m, start);
        if (m.nrefs != 0 || m.nresults != 0) {
                rt->restore(ty, &roots);
        }
        return ok;
}

bool
lir_interpret(Ty *ty, Lir const *L, LirScalar const *args, u32 nargs, LirScalar *out, LirError *err)
{
        return lir_interpret_entry(ty, L, LIR_NONE, args, nargs, out, err);
}

typedef struct lir_interp_code {
        Lir const *L;
        ffi_cif cif;
        ffi_type **types;
        ffi_closure *closure;
} LirInterpCode;

static void
interp_closure(ffi_cif *cif, void *result, void **args, void *data)
{
        LirInterpCode const *code = data;
        Lir const *L = code->L;
        LirScalar *values = LIR_STACK_ALLOC(((usize)L->sig.nparams + 1) * sizeof *values);
        LirRuntime const *rt = lir_runtime();
        Ty *ty = rt == NULL || rt->current_ty == NULL ? NULL : rt->current_ty();
        LirScalar out = {0};
        LirError err = {0};
        LirEntryFrame slots = {0};
        bool reserved = false;
        memset(values, 0, ((usize)L->sig.nparams + 1) * sizeof *values);
        for (u32 i = 0; i < L->sig.nparams; ++i) {
                u32 size = L->sig.params[i] == LIR_TYPE_VAL ? sizeof (void *) : lir_type_size(L->sig.params[i]);
                memcpy(&values[i], args[i], size);
        }
        if (L->nvslots != 0) {
                if (ty == NULL || rt->reserve == NULL || rt->restore == NULL) {
                        err = (LirError) { .kind = LIR_ERROR_MODE, .op = LIR_NONE,
                                          .message = "interpreter value slots require a VM runtime" };
                        goto Bad;
                }
                uptr base = (uptr)ty->stack.items;
                usize capacity = ty->stack.capacity;
                rt->reserve(ty, &slots, L->nvslots);
                reserved = true;
                for (u32 i = 0; i < L->sig.nparams; ++i) {
                        LirClass cls = lir_type_class(L->sig.params[i]);
                        uptr p = values[i].u;
                        if (cls == LIR_PTR && p >= base && p < base + capacity * sizeof (Value)) {
                                values[i].u = (uptr)ty->stack.items + p - base;
                        }
                }
        }
        if (!lir_interpret(ty, L, values, L->sig.nparams, &out, &err)) {
                goto Bad;
        }
        if (reserved) {
                rt->restore(ty, &slots);
        }
        if (L->sig.ret != LIR_VOID) {
                u32 size = L->sig.ret == LIR_TYPE_VAL ? sizeof (void *) : lir_type_size(L->sig.ret);
                memcpy(result, &out, size);
        }
        (void)cif;
        return;
Bad:
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
        LirInterpCode *state = calloc(1, sizeof *state);
        if (state == NULL) {
                goto Bad;
        }
        code->interp_state = state;
        state->L = code->lir;
        state->types = calloc((usize)code->sig.nparams + 1, sizeof *state->types);
        if (state->types == NULL) {
                goto Bad;
        }
        for (u32 pc = 0; pc < code->lir->ninsts; ++pc) {
                if (code->lir->insts[pc].op == LIR_RAW) {
                        if (err != NULL) {
                                *err = (LirError) { .kind = LIR_ERROR_TARGET, .op = pc,
                                                   .span = code->lir->insts[pc].span,
                                                   .message = "RAW cannot execute in the reference interpreter" };
                        }
                        return false;
                }
        }
        for (u32 i = 0; i < code->sig.nparams; ++i) {
                state->types[i] = ctype(code->sig.params[i]);
        }
        if (code->sig.variadic
            || ffi_prep_cif(&state->cif, FFI_DEFAULT_ABI, code->sig.nparams,
                            ctype(code->sig.ret), state->types) != FFI_OK) {
                goto Bad;
        }
        state->closure = ffi_closure_alloc(sizeof *state->closure, &code->body);
        if (state->closure == NULL
            || ffi_prep_closure_loc(state->closure, &state->cif, interp_closure,
                                    state, code->body) != FFI_OK) {
                goto Bad;
        }
        return true;
Bad:
        if (err != NULL) {
                *err = (LirError) { .kind = LIR_ERROR_TARGET, .op = LIR_NONE,
                                   .message = "could not create interpreter call interface" };
        }
        return false;
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
        free(state->types);
        free(state);
        code->interp_state = NULL;
}
