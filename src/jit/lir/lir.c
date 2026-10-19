#include <stdarg.h>

#include "impl.h"

LirOpInfo const LirOps[LIR_OP_COUNT] = {
#define INFO(name, form, type, argc, signature) \
        [LIR_##name] = { #name, LF_##form, LT_##type, argc, signature },
        LIR_OPS(INFO)
#undef INFO
};

static _Atomic(LirRuntime const *) Runtime;

char LirRefRoot;

void
lir_set_runtime(LirRuntime const *runtime)
{
        atomic_store_explicit(&Runtime, runtime, memory_order_release);
}

LirRuntime const *
lir_runtime(void)
{
        return atomic_load_explicit(&Runtime, memory_order_acquire);
}

bool
lir_fail(LirError *err, LirErrorKind kind, u32 op, LirSpan span, char const *fmt, ...)
{
        va_list ap;

        if (err != NULL) {
                *err = (LirError) { .kind = kind, .op = op, .span = span };
                va_start(ap, fmt);
                vsnprintf(err->message, sizeof err->message, fmt, ap);
                va_end(ap);
        }

        return false;
}

Ty *
lir_scratch(Ty *ty)
{
        static _Thread_local Ty *spare;

        if (ty == NULL) {
                ty = (spare != NULL) ? spare : (spare = alloc0(sizeof *spare));
        }

        if (ty->scratch.i == 0) {
                ExpandScratch(ty);
        }

        return ty;
}

void *
lir_copy(void const *src, usize n, usize size)
{
        return (n == 0) ? NULL : memcpy(xmA(n * size), src, n * size);
}

LirClass
lir_type_class(LirType type)
{
        switch (type) {
        case LT_F32:   return LIR_F32;
        case LT_F64:   return LIR_F64;
        case LT_PTR:
        case LT_VAL:   return LIR_PTR;
        case LT_REF:   return LIR_REF;
        case LT_VOID:
        case LT_COUNT: return LIR_CLASS_COUNT;
        default:       return LIR_I64;
        }
}

u32
lir_type_size(LirType type)
{
        switch (type) {
        case LT_I8:
        case LT_U8:
        case LT_BOOL: return 1;
        case LT_I16:
        case LT_U16:  return 2;
        case LT_I32:
        case LT_U32:
        case LT_F32:  return 4;
        case LT_I64:
        case LT_U64:
        case LT_F64:
        case LT_PTR:
        case LT_REF:  return 8;
        case LT_VAL:  return sizeof (Value);
        default:      return 0;
        }
}

inline static bool
broken(Lir const *L)
{
        return L->error.kind != LE_NONE;
}

static bool
reject(Lir *L, LirErrorKind kind, char const *why)
{
        if (!broken(L)) {
                lir_fail(&L->error, kind, vN(L->insts), (LirSpan) {0}, "%s", why);
        }

        return false;
}

Lir *
lir_new(char const *name, LirSig const *sig, LirMode mode, LirError *err)
{
        if (!sig_valid(sig) || sig->variadic || (u32)mode > LIR_MODE_ATTACHED) {
                lir_fail(
                        err,
                        LE_SIGNATURE,
                        LIR_NOWHERE,
                        "invalid function signature or execution mode"
                );
                return NULL;
        }

        Lir *L = alloc0(sizeof *L);

        memset(L->pins, 0xff, sizeof L->pins);

        L->name       = S2((name != NULL) ? name : "");
        L->sig        = *sig;
        L->sig.params = dupn(sig->params, sig->nparams);
        L->sig.nfixed = sig->nparams;
        L->params     = xtA0(LirReg, sig->nparams);
        L->mode       = mode;
        L->pc_param   = LIR_NONE;
        L->ty_param   = LIR_NONE;

        for (u32 i = 0; i < sig->nparams; ++i) {
                L->params[i] = lir_reg(L, lir_type_class(sig->params[i]));
                v_(L->regs, L->params[i])->param = i;
        }

        clear(err);

        return L;
}

void
lir_destroy(Lir *L)
{
        if (L == NULL) {
                return;
        }

        vfor(L->insts, inst_free(it));

        xmF(L->name);
        xmF((void *)L->sig.params);
        xmF(L->params);
        xvF(L->regs);
        xvF(L->labels);
        xvF(L->insts);
        xvF(L->roots);
}

void
lir_free(Lir *L)
{
        lir_destroy(L);
        xmF(L);
}

Lir *
lir_clone(Lir *L, LirError *err)
{
        Lir *D = memcpy(xmA(sizeof *D), L, sizeof *D);

        D->name       = S2(L->name);
        D->sig.params = dupn(L->sig.params, L->sig.nparams);
        D->params     = dupn(L->params, L->sig.nparams);
        D->trusted    = false;
        D->error      = (LirError) {0};

        vdup(D->regs);
        vdup(D->labels);
        vdup(D->roots);
        v00(D->insts);

        for (u32 i = 0; i < vN(L->insts); ++i) {
                if (!lir_emit(D, v_(L->insts, i))) {
                        relay(D, err);
                        lir_free(D);
                        return NULL;
                }
        }

        D->error = L->error;

        return D;
}

LirReg
lir_reg(Lir *L, LirClass cls)
{
        if (broken(L)) {
                return LIR_NONE;
        }

        if ((u32)cls >= LIR_CLASS_COUNT) {
                reject(L, LE_CLASS, "invalid register class");
                return LIR_NONE;
        }

        xvP(L->regs, ((LirRegInfo) { .cls = cls, .param = LIR_NONE, .pin = LIR_NONE }));

        return vN(L->regs) - 1;
}

LirReg
lir_pinned(Lir *L, LirPin pin)
{
        if ((u32)pin >= LIR_MAX_PINS) {
                reject(L, LE_OPERAND, "invalid pin");
                return LIR_NONE;
        }

        if (L->pins[pin] != LIR_NONE) {
                return L->pins[pin];
        }

        LirReg r = lir_reg(L, LIR_PTR);

        if (r != LIR_NONE) {
                L->pins[pin]        = r;
                v_(L->regs, r)->pin = pin;
        }

        return r;
}

bool
lir_pin_param(Lir *L, LirPin pin, u32 param)
{
        if (param >= L->sig.nparams) {
                return reject(L, LE_SIGNATURE, "pin parameter is out of range");
        }

        LirReg r = lir_pinned(L, pin);

        if (r == LIR_NONE) {
                return false;
        }

        LirRegInfo *ri  = v_(L->regs, r);
        LirClass    cls = lir_type_class(L->sig.params[param]);

        if (ri->param != LIR_NONE && ri->param != param) {
                return reject(L, LE_SIGNATURE, "pin already has a parameter");
        }

        if (isfloat(cls)) {
                return reject(L, LE_CLASS, "pins require a GPR parameter");
        }

        ri->param = param;
        ri->cls   = cls;

        return true;
}

bool
lir_pc_param(Lir *L, u32 param)
{
        if (param >= L->sig.nparams || L->sig.params[param] != LT_PTR) {
                return reject(L, LE_SIGNATURE, "pc slot requires a pointer parameter");
        }

        L->pc_param = param;

        return true;
}

LirLabel
lir_label(Lir *L)
{
        if (broken(L)) {
                return LIR_NONE;
        }

        xvP(L->labels, ((LirLabelInfo) { .pos = LIR_NONE }));

        return vN(L->labels) - 1;
}

bool
lir_bind(Lir *L, LirLabel label)
{
        if (broken(L)) {
                return false;
        }

        if (label >= vN(L->labels) || v__(L->labels, label).pos != LIR_NONE) {
                return reject(L, LE_LABEL, "label is invalid or already bound");
        }

        v_(L->labels, label)->pos = vN(L->insts);

        return true;
}

bool
lir_entry(Lir *L, LirLabel label)
{
        if (!lir_bind(L, label)) {
                return false;
        }

        v_(L->labels, label)->entry = true;

        return lir_emit_to(L, LIR_ENTRY, LIR_NONE, (LirOpnd[]) { lir_l(label) }, 1);
}

LirReg
lir_vslot(Lir *L)
{
        LirReg r = lir_reg(L, LIR_PTR);

        if (r == LIR_NONE) {
                return LIR_NONE;
        }

        LirOpnd slot = { .kind = LO_VSLOT, .index = L->nvslots++ };

        return lir_emit_to(L, LIR_MOV, r, &slot, 1) ? r : LIR_NONE;
}

static LirOpnd
root(Lir *L, Value const *v, LirOpndKind kind)
{
        if (broken(L)) {
                return (LirOpnd) {0};
        }

        if (v == NULL) {
                reject(L, LE_OPERAND, "missing rooted value");
                return (LirOpnd) {0};
        }

        xvP(L->roots, *v);

        return (LirOpnd) { .kind = kind, .index = vN(L->roots) - 1 };
}

LirOpnd
lir_const(Lir *L, Value const *value)
{
        return root(L, value, LO_CONST);
}

LirOpnd
lir_ref_const(Lir *L, Value const *value)
{
        return root(L, value, LO_REFCONST);
}

bool
lir_emit(Lir *L, LirInst const *inst)
{
        if (broken(L)) {
                return false;
        }

        if (
                (inst == NULL)
             || ((u32)inst->op >= LIR_OP_COUNT)
             || (inst->nargs > LIR_MAX_OPERANDS)
        ) {
                return reject(L, LE_OPERAND, "invalid instruction");
        }

#define MISSING(p, n) || (inst->n != 0 && inst->p == NULL)
        if (false INST_PAYLOAD(MISSING)) {
                return reject(L, LE_OPERAND, "missing instruction payload");
        }
#undef MISSING

        LirInst *in = xvP(L->insts, *inst);

        if (in->origin == 0) {
                in->origin = L->origin;
        }

#define DUP(p, n) in->p = dupn(inst->p, inst->n);
        INST_PAYLOAD(DUP)
#undef DUP

        return true;
}

bool
lir_emit_owned(Lir *L, LirInst const *inst)
{
        if (broken(L)) {
                return false;
        }

        xvP(L->insts, *inst);

        return true;
}

bool
lir_emit_to(Lir *L, LirOp op, LirReg dst, LirOpnd const *args, u32 nargs)
{
        if (broken(L)) {
                return false;
        }

        if (
                (nargs > LIR_MAX_OPERANDS)
             || (nargs != 0 && args == NULL)
             || ((u32)op >= LIR_OP_COUNT)
        ) {
                return reject(L, LE_OPERAND, "invalid operand count");
        }

        LirInst *in = xvP(L->insts, ((LirInst) { .op = op, .dst = dst, .origin = L->origin }));

        in->nargs = nargs;

        for (u32 i = 0; i < nargs; ++i) {
                in->args[i] = args[i];
        }

        return true;
}

static char const *const ClassNames[] = {
        [LIR_I32] = "i32",
        [LIR_I64] = "i64",
        [LIR_F32] = "f32",
        [LIR_F64] = "f64",
        [LIR_PTR] = "ptr",
        [LIR_REF] = "ref"
};

static void
dump_operand(LirOpnd a, FILE *out)
{
        switch (a.kind) {
        case LO_MEM:
                fprintf(out, "[r%u", a.mem.base);
                if (a.mem.index != LIR_NONE) {
                        fprintf(out, "+r%u*%u", a.mem.index, a.mem.scale);
                }
                fprintf(out, "%+d]", a.mem.disp);
                break;

        case LO_REG:    fprintf(out, "r%u", a.reg);                     break;
        case LO_IMM:    fprintf(out, "%" PRId64, a.imm);                break;
        case LO_FIMM:   fprintf(out, "%.17g", a.fimm);                  break;
        case LO_LABEL:  fprintf(out, "L%u", a.label);                   break;
        case LO_CC:     fprintf(out, "cc%u", a.cc);                     break;
        case LO_CODE:   fprintf(out, "code(%s)", a.code->name);         break;
        case LO_HELPER: fprintf(out, "rt.%s", a.helper->name);          break;
        default:        fprintf(out, "operand%u(%u)", a.kind, a.index); break;
        }
}

static void
dump_list(char const *open, LirOpnd const *xs, u32 n, FILE *out)
{
        for (u32 i = 0; i < n; ++i) {
                fputs((i == 0) ? open : ", ", out);
                dump_operand(xs[i], out);
        }
}

static void
dump_inst(LirInst const *in, u32 pc, FILE *out)
{
        fprintf(out, "  %u  %s", pc, LirOps[in->op].name);

        if (in->dst != LIR_NONE) {
                fprintf(out, " r%u%s", in->dst, (in->nargs != 0) ? "," : "");
        }

        dump_list(" ", in->args, in->nargs, out);
        dump_list(" (", in->call_args, in->ncall_args, out);

        if (in->ncall_args != 0) {
                fputc(')', out);
        }

        for (u32 i = 0; i < in->ntargets; ++i) {
                fprintf(out, " L%u", in->targets[i]);
        }

        fputc('\n', out);
}

void
lir_dump(Lir const *L, FILE *out)
{
        fprintf(
                out,
                "%s: %zu registers, %u vslots\n",
                L->name,
                vN(L->regs),
                L->nvslots
        );

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirRegInfo ri = v__(L->regs, r);
                fprintf(out, "  r%u: %s", r, ClassNames[ri.cls]);
                if (ri.param != LIR_NONE) {
                        fprintf(out, " param%u", ri.param);
                }
                if (ri.pin != LIR_NONE) {
                        fprintf(out, " pin%u", ri.pin);
                }
                fputc('\n', out);
        }

        for (u32 pc = 0; pc <= vN(L->insts); ++pc) {
                for (u32 l = 0; l < vN(L->labels); ++l) {
                        if (v__(L->labels, l).pos == pc) {
                                fprintf(out, "L%u:\n", l);
                        }
                }
                if (pc < vN(L->insts)) {
                        dump_inst(v_(L->insts, pc), pc, out);
                }
        }
}
