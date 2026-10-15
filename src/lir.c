#include <stdarg.h>
#include <limits.h>

#include "ty.h"
#include "lir.h"

LirOpInfo const LirOps[LIR_OP_COUNT] = {
#define LIR_INFO(name, form, type, argc, signature) \
        [LIR_##name] = { #name, LIR_FORM_##form, LIR_TYPE_##type, argc, signature },
#define LIR_TYPE_VOID LIR_VOID
        LIR_OPS(LIR_INFO)
#undef LIR_TYPE_VOID
#undef LIR_INFO
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

static bool
fail(LirError *err, LirErrorKind kind, u32 op, LirSpan span, char const *fmt, ...)
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

static bool
grow(void *ptr, u32 *cap, u32 count, usize size)
{
        void *p;
        u32 n = *cap;
        void *q;
        if (count <= n) {
                return true;
        }
        n = n == 0 ? 8 : n;
        while (n < count) {
                if (n > UINT32_MAX / 2) {
                        n = count;
                        break;
                }
                n *= 2;
        }
        if (n > SIZE_MAX / size) {
                return false;
        }
        memcpy(&p, ptr, sizeof p);
        q = realloc(p, n * size);
        if (q == NULL) {
                return false;
        }
        memcpy(ptr, &q, sizeof q);
        *cap = n;
        return true;
}

static void *
copy(void const *src, usize n, usize size)
{
        void *p;
        if (n == 0) {
                return NULL;
        }
        if (src == NULL || n > SIZE_MAX / size) {
                return NULL;
        }
        p = malloc(n * size);
        if (p != NULL) {
                memcpy(p, src, n * size);
        }
        return p;
}

static bool
sig_valid(LirSig const *sig)
{
        if (
                sig == NULL
             || (u32)sig->ret >= LIR_TYPE_COUNT
             || (sig->nparams != 0 && sig->params == NULL)
             || sig->nfixed > sig->nparams
        ) {
                return false;
        }
        for (u32 i = 0; i < sig->nparams; ++i) {
                if (sig->params[i] == LIR_VOID || (u32)sig->params[i] >= LIR_TYPE_COUNT) {
                        return false;
                }
        }
        return true;
}

LirClass
lir_type_class(LirType type)
{
        switch (type) {
        case LIR_TYPE_F32: return LIR_F32;
        case LIR_TYPE_F64: return LIR_F64;
        case LIR_TYPE_PTR:
        case LIR_TYPE_VAL: return LIR_PTR;
        case LIR_TYPE_REF: return LIR_REF;
        case LIR_VOID:
        case LIR_TYPE_COUNT: return LIR_CLASS_COUNT;
        default: return LIR_I64;
        }
}

u32
lir_type_size(LirType type)
{
        switch (type) {
        case LIR_TYPE_I8:
        case LIR_TYPE_U8:
        case LIR_TYPE_BOOL: return 1;
        case LIR_TYPE_I16:
        case LIR_TYPE_U16: return 2;
        case LIR_TYPE_I32:
        case LIR_TYPE_U32:
        case LIR_TYPE_F32: return 4;
        case LIR_TYPE_I64:
        case LIR_TYPE_U64:
        case LIR_TYPE_F64:
        case LIR_TYPE_PTR:
        case LIR_TYPE_REF: return 8;
        case LIR_TYPE_VAL: return sizeof (Value);
        default: return 0;
        }
}

static bool
build_fail(Lir *L, LirErrorKind kind, char const *message)
{
        if (L->error.kind == LIR_ERROR_NONE) {
                fail(&L->error, kind, L->ninsts, (LirSpan) {0}, "%s", message);
        }
        return false;
}

Lir *
lir_new(char const *name, LirSig const *sig, LirMode mode, LirError *err)
{
        Lir *L;
        if (!sig_valid(sig) || sig->variadic || (u32)mode > LIR_MODE_ATTACHED) {
                fail(err, LIR_ERROR_SIGNATURE, LIR_NONE, (LirSpan) {0},
                     "invalid function signature or execution mode");
                return NULL;
        }
        L = calloc(1, sizeof *L);
        if (L == NULL) {
                goto NoMemory;
        }
        for (u32 i = 0; i < LIR_MAX_PINS; ++i) {
                L->pins[i] = LIR_NONE;
        }
        L->name = copy(name == NULL ? "" : name, strlen(name == NULL ? "" : name) + 1, 1);
        L->sig = *sig;
        L->sig.params = copy(sig->params, sig->nparams, sizeof *sig->params);
        L->sig.nfixed = sig->nparams;
        L->params = calloc(sig->nparams, sizeof *L->params);
        L->mode = mode;
        L->pc_param = LIR_NONE;
        L->ty_param = LIR_NONE;
        if (
                L->name == NULL
             || (sig->nparams != 0 && (L->sig.params == NULL || L->params == NULL))
        ) {
                goto NoMemory;
        }
        for (u32 i = 0; i < sig->nparams; ++i) {
                LirReg r = lir_reg(L, lir_type_class(sig->params[i]));
                if (r == LIR_NONE) {
                        goto NoMemory;
                }
                L->params[i]     = r;
                L->regs[r].param = i;
        }
        if (err != NULL) {
                *err = (LirError) {0};
        }
        return L;
NoMemory:
        lir_free(L);
        fail(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory");
        return NULL;
}

static void
inst_free(LirInst *inst)
{
        free((void *)inst->sig.params);
        free(inst->call_args);
        free(inst->targets);
        free((void *)inst->raw.arm64);
        free((void *)inst->raw.x64);
        free((void *)inst->raw.in);
        free((void *)inst->raw.out);
}

void
lir_destroy(Lir *L)
{
        if (L == NULL) {
                return;
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                inst_free(&L->insts[i]);
        }
        free(L->name);
        free((void *)L->sig.params);
        free(L->params);
        free(L->regs);
        free(L->labels);
        free(L->insts);
        free(L->roots);
}

void
lir_free(Lir *L)
{
        if (L == NULL) {
                return;
        }
        lir_destroy(L);
        free(L);
}

Lir *
lir_clone(Lir *L, LirError *err)
{
        Lir *D = calloc(1, sizeof *D);
        if (D == NULL) {
                goto NoMemory;
        }
        D->name = copy(L->name, strlen(L->name) + 1, 1);
        D->sig = L->sig;
        D->sig.params = copy(L->sig.params, L->sig.nparams, sizeof *L->sig.params);
        D->params = copy(L->params, L->sig.nparams, sizeof *L->params);
        D->regs = copy(L->regs, L->nregs, sizeof *L->regs);
        D->labels = copy(L->labels, L->nlabels, sizeof *L->labels);
        D->roots = copy(L->roots, L->nroots, sizeof *L->roots);
        D->nregs = D->reg_capacity = L->nregs;
        D->nlabels = D->label_capacity = L->nlabels;
        D->nroots = D->root_capacity = L->nroots;
        D->mode          = L->mode;
        D->resolved_mode = L->resolved_mode;
        D->nvslots       = L->nvslots;
        D->pc_param      = L->pc_param;
        D->ty_param      = L->ty_param;
        D->stable_pins   = L->stable_pins;
        D->stack_pins    = L->stack_pins;
        memcpy(D->pins, L->pins, sizeof D->pins);
        if (D->name == NULL
            || (L->sig.nparams != 0 && (D->sig.params == NULL || D->params == NULL))
            || (L->nregs != 0 && D->regs == NULL)
            || (L->nlabels != 0 && D->labels == NULL)
            || (L->nroots != 0 && D->roots == NULL)) {
                goto NoMemory;
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                if (!lir_emit(D, &L->insts[i])) {
                        if (err != NULL) {
                                *err = D->error;
                        }
                        lir_free(D);
                        return NULL;
                }
        }
        D->error = L->error;
        return D;
NoMemory:
        lir_free(D);
        fail(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory cloning LIR");
        return NULL;
}

LirReg
lir_reg(Lir *L, LirClass cls)
{
        u32 r = L->nregs;
        if (L->error.kind != LIR_ERROR_NONE) {
                return LIR_NONE;
        }
        if ((u32)cls >= LIR_CLASS_COUNT) {
                build_fail(L, LIR_ERROR_CLASS, "invalid register class");
                return LIR_NONE;
        }
        if (r == LIR_NONE || !grow(&L->regs, &L->reg_capacity, r + 1, sizeof *L->regs)) {
                build_fail(L, LIR_ERROR_MEMORY, "out of memory allocating register");
                return LIR_NONE;
        }
        L->regs[r] = (LirRegInfo) { .cls = cls, .param = LIR_NONE, .pin = LIR_NONE };
        ++L->nregs;
        return r;
}

LirReg
lir_pinned(Lir *L, LirPin pin)
{
        LirReg r;
        if ((u32)pin >= LIR_MAX_PINS) {
                build_fail(L, LIR_ERROR_OPERAND, "invalid pin");
                return LIR_NONE;
        }
        if (L->pins[pin] != LIR_NONE) {
                return L->pins[pin];
        }
        r = lir_reg(L, LIR_PTR);
        if (r != LIR_NONE) {
                L->pins[pin]    = r;
                L->regs[r].pin = pin;
        }
        return r;
}

bool
lir_pin_param(Lir *L, LirPin pin, u32 param)
{
        LirReg r;
        if (param >= L->sig.nparams) {
                return build_fail(L, LIR_ERROR_SIGNATURE, "pin parameter is out of range");
        }
        r = lir_pinned(L, pin);
        if (r == LIR_NONE) {
                return false;
        }
        if (
                L->regs[r].param != LIR_NONE
             && L->regs[r].param != param
        ) {
                return build_fail(L, LIR_ERROR_SIGNATURE, "pin already has a parameter");
        }
        if (lir_type_class(L->sig.params[param]) >= LIR_F32
            && lir_type_class(L->sig.params[param]) <= LIR_F64) {
                return build_fail(L, LIR_ERROR_CLASS, "pins require a GPR parameter");
        }
        L->regs[r].param = param;
        L->regs[r].cls   = lir_type_class(L->sig.params[param]);
        return true;
}

bool
lir_pc_param(Lir *L, u32 param)
{
        if (param >= L->sig.nparams || L->sig.params[param] != LIR_TYPE_PTR) {
                return build_fail(L, LIR_ERROR_SIGNATURE, "pc slot requires a pointer parameter");
        }
        L->pc_param = param;
        return true;
}

LirLabel
lir_label(Lir *L)
{
        u32 n = L->nlabels;
        if (L->error.kind != LIR_ERROR_NONE) {
                return LIR_NONE;
        }
        if (n == LIR_NONE || !grow(&L->labels, &L->label_capacity, n + 1, sizeof *L->labels)) {
                build_fail(L, LIR_ERROR_MEMORY, "out of memory allocating label");
                return LIR_NONE;
        }
        L->labels[n] = (LirLabelInfo) { .pos = LIR_NONE };
        ++L->nlabels;
        return n;
}

bool
lir_bind(Lir *L, LirLabel label)
{
        if (L->error.kind != LIR_ERROR_NONE) {
                return false;
        }
        if (label >= L->nlabels || L->labels[label].pos != LIR_NONE) {
                return build_fail(L, LIR_ERROR_LABEL, "label is invalid or already bound");
        }
        L->labels[label].pos = L->ninsts;
        return true;
}

bool
lir_entry(Lir *L, LirLabel label)
{
        if (!lir_bind(L, label)) {
                return false;
        }
        L->labels[label].entry = true;
        return lir_emit_to(L, LIR_ENTRY, LIR_NONE, (LirOpnd[]) { lir_l(label) }, 1);
}

LirReg
lir_vslot(Lir *L)
{
        LirReg r = lir_reg(L, LIR_PTR);
        LirOpnd arg = { .kind = LIR_OPERAND_VSLOT, .index = L->nvslots };
        if (r == LIR_NONE || L->nvslots == LIR_NONE) {
                return LIR_NONE;
        }
        ++L->nvslots;
        if (!lir_emit_to(L, LIR_MOV, r, &arg, 1)) {
                return LIR_NONE;
        }
        return r;
}

static LirOpnd
root(Lir *L, Value const *v, LirOperandKind kind)
{
        u32 n = L->nroots;
        if (L->error.kind != LIR_ERROR_NONE) {
                return (LirOpnd) {0};
        }
        if (v == NULL) {
                build_fail(L, LIR_ERROR_OPERAND, "missing rooted value");
                return (LirOpnd) {0};
        }
        if (n == LIR_NONE || !grow(&L->roots, &L->root_capacity, n + 1, sizeof *L->roots)) {
                build_fail(L, LIR_ERROR_MEMORY, "out of memory allocating constant");
                return (LirOpnd) {0};
        }
        L->roots[n] = *v;
        ++L->nroots;
        return (LirOpnd) { .kind = kind, .index = n };
}

LirOpnd
lir_const(Lir *L, Value const *value)
{
        return root(L, value, LIR_OPERAND_CONST);
}

LirOpnd
lir_ref_const(Lir *L, Value const *value)
{
        return root(L, value, LIR_OPERAND_REFCONST);
}

bool
lir_emit(Lir *L, LirInst const *inst)
{
        LirInst *in;
        if (L->error.kind != LIR_ERROR_NONE) {
                return false;
        }
        if (inst == NULL || (u32)inst->op >= LIR_OP_COUNT || inst->nargs > LIR_MAX_OPERANDS) {
                return build_fail(L, LIR_ERROR_OPERAND, "invalid instruction");
        }
        if (
                (inst->sig.nparams != 0 && inst->sig.params == NULL)
             || (inst->ncall_args != 0 && inst->call_args == NULL)
             || (inst->ntargets != 0 && inst->targets == NULL)
             || (inst->raw.narm64 != 0 && inst->raw.arm64 == NULL)
             || (inst->raw.nx64 != 0 && inst->raw.x64 == NULL)
             || (inst->raw.nin != 0 && inst->raw.in == NULL)
             || (inst->raw.nout != 0 && inst->raw.out == NULL)
        ) {
                return build_fail(L, LIR_ERROR_OPERAND, "missing instruction payload");
        }
        if (
                L->ninsts == LIR_NONE
             || !grow(&L->insts, &L->inst_capacity, L->ninsts + 1, sizeof *L->insts)
        ) {
                return build_fail(L, LIR_ERROR_MEMORY, "could not copy instruction payload");
        }
        in = &L->insts[L->ninsts];
        *in = *inst;
        if (
                inst->sig.nparams == 0
             && inst->ncall_args == 0
             && inst->ntargets == 0
             && inst->raw.narm64 == 0
             && inst->raw.nx64 == 0
             && inst->raw.nin == 0
             && inst->raw.nout == 0
        ) {
                in->sig.params = NULL;
                in->call_args  = NULL;
                in->targets    = NULL;
                in->raw.arm64  = NULL;
                in->raw.x64    = NULL;
                in->raw.in     = NULL;
                in->raw.out    = NULL;
                L->ninsts += 1;
                return true;
        }
        in->sig.params = copy(inst->sig.params, inst->sig.nparams, sizeof *inst->sig.params);
        in->call_args  = copy(inst->call_args, inst->ncall_args, sizeof *inst->call_args);
        in->targets    = copy(inst->targets, inst->ntargets, sizeof *inst->targets);
        in->raw.arm64  = copy(inst->raw.arm64, inst->raw.narm64, sizeof *inst->raw.arm64);
        in->raw.x64    = copy(inst->raw.x64, inst->raw.nx64, sizeof *inst->raw.x64);
        in->raw.in     = copy(inst->raw.in, inst->raw.nin, sizeof *inst->raw.in);
        in->raw.out    = copy(inst->raw.out, inst->raw.nout, sizeof *inst->raw.out);
        if (
                (inst->sig.nparams != 0 && in->sig.params == NULL)
             || (inst->ncall_args != 0 && in->call_args == NULL)
             || (inst->ntargets != 0 && in->targets == NULL)
             || (inst->raw.narm64 != 0 && in->raw.arm64 == NULL)
             || (inst->raw.nx64 != 0 && in->raw.x64 == NULL)
             || (inst->raw.nin != 0 && in->raw.in == NULL)
             || (inst->raw.nout != 0 && in->raw.out == NULL)
        ) {
                inst_free(in);
                return build_fail(L, LIR_ERROR_MEMORY, "could not copy instruction payload");
        }
        L->ninsts += 1;
        return true;
}

bool
lir_emit_owned(Lir *L, LirInst const *inst)
{
        if (L->error.kind != LIR_ERROR_NONE) {
                return false;
        }
        if (
                L->ninsts == LIR_NONE
             || !grow(&L->insts, &L->inst_capacity, L->ninsts + 1, sizeof *L->insts)
        ) {
                return build_fail(L, LIR_ERROR_MEMORY, "could not copy instruction payload");
        }
        L->insts[L->ninsts++] = *inst;
        return true;
}

bool
lir_emit_to(Lir *L, LirOp op, LirReg dst, LirOpnd const *args, u32 nargs)
{
        LirInst *in;
        if (L->error.kind != LIR_ERROR_NONE) {
                return false;
        }
        if (nargs > LIR_MAX_OPERANDS || (nargs != 0 && args == NULL) || (u32)op >= LIR_OP_COUNT) {
                return build_fail(L, LIR_ERROR_OPERAND, "invalid operand count");
        }
        if (
                L->ninsts == LIR_NONE
             || !grow(&L->insts, &L->inst_capacity, L->ninsts + 1, sizeof *L->insts)
        ) {
                return build_fail(L, LIR_ERROR_MEMORY, "could not copy instruction payload");
        }
        in = &L->insts[L->ninsts++];
        memset(in, 0, sizeof *in);
        in->op    = op;
        in->dst   = dst;
        in->nargs = nargs;
        if (nargs != 0) {
                memcpy(in->args, args, nargs * sizeof *args);
        }
        return true;
}

static bool
isint(LirClass cls)
{
        return cls == LIR_I32 || cls == LIR_I64;
}

static bool
isfloat(LirClass cls)
{
        return cls == LIR_F32 || cls == LIR_F64;
}

static bool
isptr(LirClass cls)
{
        return cls == LIR_PTR || cls == LIR_REF;
}

static LirClass
opclass(Lir const *L, LirOpnd a)
{
        switch (a.kind) {
        case LIR_OPERAND_REG:
                return a.reg < L->nregs ? L->regs[a.reg].cls : LIR_CLASS_COUNT;
        case LIR_OPERAND_IMM:
        case LIR_HOLE_IMM: return LIR_I64;
        case LIR_OPERAND_FIMM:
        case LIR_HOLE_FIMM: return LIR_F64;
        case LIR_OPERAND_REFCONST: return LIR_REF;
        case LIR_OPERAND_CONST:
        case LIR_OPERAND_VSLOT:
        case LIR_HOLE_PTR:
        case LIR_HOLE_CONST: return LIR_PTR;
        default: return LIR_CLASS_COUNT;
        }
}

static bool
compatible(Lir const *L, LirClass cls, LirOpnd a)
{
        if (a.kind == LIR_OPERAND_IMM || a.kind == LIR_HOLE_IMM) {
                return isint(cls) || cls == LIR_PTR;
        }
        if (a.kind == LIR_OPERAND_FIMM || a.kind == LIR_HOLE_FIMM) {
                return isfloat(cls);
        }
        return opclass(L, a) == cls;
}

static bool
type_matches(Lir const *L, LirType type, LirOpnd a)
{
        LirClass cls = opclass(L, a);
        if (type >= LIR_TYPE_I8 && type <= LIR_TYPE_U32) {
                return isint(cls);
        }
        if (type == LIR_TYPE_BOOL) {
                return isint(cls);
        }
        return compatible(L, lir_type_class(type), a);
}

static bool
label_valid(Lir const *L, LirOpnd a)
{
        return a.kind == LIR_OPERAND_LABEL && a.label < L->nlabels
            && L->labels[a.label].pos <= L->ninsts;
}

static bool
operand_valid(Lir const *L, LirOpnd a)
{
        switch (a.kind) {
        case LIR_OPERAND_REG:
                return a.reg < L->nregs;
        case LIR_OPERAND_MEM:
                return a.mem.base < L->nregs
                    && isptr(L->regs[a.mem.base].cls)
                    && (a.mem.index == LIR_NONE
                        || (a.mem.index < L->nregs && isint(L->regs[a.mem.index].cls)))
                    && (a.mem.scale == 1 || a.mem.scale == 2
                        || a.mem.scale == 4 || a.mem.scale == 8);
        case LIR_OPERAND_LABEL: return label_valid(L, a);
        case LIR_OPERAND_CC: return (u32)a.cc < LIR_CC_COUNT;
        case LIR_OPERAND_CONST:
        case LIR_OPERAND_REFCONST: return a.index < L->nroots;
        case LIR_OPERAND_VSLOT: return a.index < L->nvslots;
        case LIR_OPERAND_CODE: return a.code != NULL;
        case LIR_OPERAND_HELPER: return a.helper != NULL;
        case LIR_OPERAND_IMM:
        case LIR_OPERAND_FIMM:
        case LIR_HOLE_IMM:
        case LIR_HOLE_FIMM:
        case LIR_HOLE_PTR:
        case LIR_HOLE_CONST:
        case LIR_HOLE_CALLEE: return true;
        default: return false;
        }
}

static bool
comparison(Lir const *L, LirOpnd cc, LirOpnd a, LirOpnd b, bool fp)
{
        LirClass cls = opclass(L, a);
        if (cc.kind != LIR_OPERAND_CC || (cc.cc >= LIR_FEQ) != fp) {
                return false;
        }
        if (a.kind != LIR_OPERAND_REG && b.kind == LIR_OPERAND_REG) {
                cls = opclass(L, b);
        }
        return (fp ? isfloat(cls) : isint(cls) || isptr(cls))
            && compatible(L, cls, a) && compatible(L, cls, b);
}

static bool
sig_equal(LirSig const *a, LirSig const *b)
{
        if (
                a->ret != b->ret
             || a->nparams != b->nparams
             || a->variadic != b->variadic
             || (a->variadic && a->nfixed != b->nfixed)
        ) {
                return false;
        }
        for (u32 i = 0; i < a->nparams; ++i) {
                if (a->params[i] != b->params[i]) {
                        return false;
                }
        }
        return true;
}

static bool
call_valid(Lir const *L, LirInst const *in)
{
        LirOpnd target = in->args[0];
        LirClass cls = in->dst == LIR_NONE ? LIR_CLASS_COUNT : L->regs[in->dst].cls;
        u32 flags = LIR_MAY_GC | LIR_MAY_THROW | LIR_RETURNS_TWICE | LIR_NORETURN
                  | LIR_CALL_SITE | LIR_READS_NO_LOCALS | LIR_WRITES_LOCALS;
        if (!sig_valid(&in->sig) || in->ncall_args != in->sig.nparams || (in->flags & ~flags)) {
                return false;
        }
        switch (target.kind) {
        case LIR_OPERAND_REG:
                if (opclass(L, target) != LIR_PTR) {
                        return false;
                }
                break;
        case LIR_OPERAND_IMM:
        case LIR_HOLE_PTR:
        case LIR_HOLE_CALLEE:
                break;
        case LIR_OPERAND_HELPER:
                if (
                        !sig_valid(&target.helper->sig)
                     || !sig_equal(&in->sig, &target.helper->sig)
                     || (in->flags & target.helper->flags) != target.helper->flags
                ) {
                        return false;
                }
                break;
        case LIR_OPERAND_CODE:
                if (!sig_valid(&target.code->sig) || !sig_equal(&in->sig, &target.code->sig)
                    || (target.code->mode == LIR_MODE_ATTACHED && !(in->flags & LIR_MAY_GC))) {
                        return false;
                }
                break;
        default: return false;
        }
        if (in->op == LIR_TAILCALL) {
                if (in->dst != LIR_NONE || in->sig.ret != L->sig.ret) {
                        return false;
                }
        } else if (in->sig.ret == LIR_VOID) {
                if (in->dst != LIR_NONE) {
                        return false;
                }
        } else if (in->dst != LIR_NONE && !type_matches(L, in->sig.ret, lir_r(in->dst))) {
                return false;
        }
        if (in->dst != LIR_NONE && cls == LIR_CLASS_COUNT) {
                return false;
        }
        for (u32 i = 0; i < in->ncall_args; ++i) {
                if (!operand_valid(L, in->call_args[i])
                    || !type_matches(L, in->sig.params[i], in->call_args[i])) {
                        return false;
                }
        }
        return true;
}

static bool
inst_valid(Lir const *L, u32 i, LirError *err)
{
        LirInst const *in = &L->insts[i];
        LirOpnd const *a = in->args;
        LirOpInfo const *info;
        LirClass d;
        bool ok = false;
        bool dst;
        if ((u32)in->op >= LIR_OP_COUNT || in->nargs > LIR_MAX_OPERANDS) {
                return fail(err, LIR_ERROR_OPERAND, i, in->span, "invalid instruction");
        }
        info = &LirOps[in->op];
        if (in->nargs != info->argc && !(in->op == LIR_RET && in->nargs <= 1)
            && !(in->op == LIR_POLL && in->nargs == 4)) {
                return fail(err, LIR_ERROR_OPERAND, i, in->span,
                            "%s has the wrong operand count", info->name);
        }
        if (in->dst != LIR_NONE && in->dst >= L->nregs) {
                return fail(err, LIR_ERROR_OPERAND, i, in->span, "invalid destination register");
        }
        dst = info->signature[0] == 'd';
        if (
                (dst && in->dst == LIR_NONE)
             || (!dst && in->dst != LIR_NONE && in->op != LIR_CALL)
        ) {
                return fail(err, LIR_ERROR_OPERAND, i, in->span,
                            "%s has an invalid destination", info->name);
        }
        for (u32 j = 0; j < in->nargs; ++j) {
                if (!operand_valid(L, a[j])) {
                        return fail(err, LIR_ERROR_OPERAND, i, in->span,
                                    "%s operand %u is invalid", info->name, j);
                }
        }
        if (
                (in->op != LIR_CALL && in->op != LIR_TAILCALL
                    && (in->ncall_args != 0 || in->sig.nparams != 0
                        || in->sig.ret != LIR_VOID || in->sig.nfixed != 0
                        || in->sig.variadic
                        || (in->flags & (in->op == LIR_POLL ? ~LIR_CALL_SITE : UINT32_MAX)) != 0))
             || (in->op != LIR_SWITCH && in->ntargets != 0)
             || (in->op != LIR_RAW && (in->raw.nin != 0 || in->raw.nout != 0
                    || in->raw.narm64 != 0 || in->raw.nx64 != 0
                    || in->raw.gpr_clobber != 0 || in->raw.fpr_clobber != 0))
        ) {
                return fail(err, LIR_ERROR_OPERAND, i, in->span, "unexpected instruction payload");
        }
        d = in->dst == LIR_NONE ? LIR_CLASS_COUNT : L->regs[in->dst].cls;
        switch (info->form) {
        case LIR_FORM_MOV:
                ok = compatible(L, d, a[0]);
                break;
        case LIR_FORM_LI:
                ok = (isint(d) || d == LIR_PTR)
                  && (a[0].kind == LIR_OPERAND_IMM || a[0].kind == LIR_HOLE_IMM
                      || (d == LIR_PTR && a[0].kind == LIR_HOLE_PTR));
                break;
        case LIR_FORM_FLI:
                ok = isfloat(d)
                  && (a[0].kind == LIR_OPERAND_FIMM || a[0].kind == LIR_HOLE_FIMM);
                break;
        case LIR_FORM_LEA:
                ok = d == LIR_PTR && a[0].kind == LIR_OPERAND_MEM;
                break;
        case LIR_FORM_IBINARY:
        case LIR_FORM_CHECKED:
                ok = isint(d) && compatible(L, d, a[0]) && compatible(L, d, a[1]);
                if ((in->op == LIR_ADD || in->op == LIR_SUB) && d == LIR_PTR) {
                        ok = isptr(opclass(L, a[0])) && opclass(L, a[1]) == LIR_I64;
                }
                if (in->op == LIR_SUB && d == LIR_I64
                    && isptr(opclass(L, a[0])) && isptr(opclass(L, a[1]))) {
                        ok = true;
                }
                if (info->form == LIR_FORM_CHECKED) {
                        ok = ok && label_valid(L, a[2]);
                }
                break;
        case LIR_FORM_IUNARY:
                ok = isint(d) && compatible(L, d, a[0]);
                if (in->op >= LIR_SEXT8 && in->op <= LIR_ZEXT32) {
                        ok = isint(d) && isint(opclass(L, a[0]));
                }
                break;
        case LIR_FORM_FBINARY:
        case LIR_FORM_FUNARY:
        case LIR_FORM_FMA:
                ok = isfloat(d);
                for (u32 j = 0; j < in->nargs; ++j) {
                        ok = ok && compatible(L, d, a[j]);
                }
                break;
        case LIR_FORM_I2F:
                ok = isfloat(d) && isint(opclass(L, a[0]));
                break;
        case LIR_FORM_F2I:
                ok = isint(d) && isfloat(opclass(L, a[0]));
                break;
        case LIR_FORM_FEXT:
                ok = d == LIR_F64 && opclass(L, a[0]) == LIR_F32;
                break;
        case LIR_FORM_FTRUNC:
                ok = d == LIR_F32 && opclass(L, a[0]) == LIR_F64;
                break;
        case LIR_FORM_BITCAST:
                ok = a[0].kind == LIR_OPERAND_REG
                  && ((d == LIR_I32 || d == LIR_F32)
                      == (opclass(L, a[0]) == LIR_I32 || opclass(L, a[0]) == LIR_F32));
                break;
        case LIR_FORM_LD:
                ok = a[0].kind == LIR_OPERAND_MEM && type_matches(L, info->type, lir_r(in->dst));
                if (info->type == LIR_TYPE_I64 && isptr(d)) {
                        ok = a[0].kind == LIR_OPERAND_MEM;
                }
                break;
        case LIR_FORM_ST:
                ok = a[0].kind == LIR_OPERAND_MEM && type_matches(L, info->type, a[1]);
                if (info->type == LIR_TYPE_I64 && isptr(opclass(L, a[1]))) {
                        ok = a[0].kind == LIR_OPERAND_MEM;
                }
                break;
        case LIR_FORM_SETCC:
        case LIR_FORM_FSETCC:
                ok = isint(d) && comparison(L, a[0], a[1], a[2], in->op == LIR_FSETCC);
                break;
        case LIR_FORM_SELECT:
        case LIR_FORM_FSELECT:
                ok = comparison(L, a[0], a[1], a[2], in->op == LIR_FSELECT)
                  && compatible(L, d, a[3]) && compatible(L, d, a[4]);
                break;
        case LIR_FORM_BR:
        case LIR_FORM_FBR:
                ok = comparison(L, a[0], a[1], a[2], in->op == LIR_FBR) && label_valid(L, a[3]);
                break;
        case LIR_FORM_BRZ:
                ok = (isint(opclass(L, a[0])) || isptr(opclass(L, a[0]))) && label_valid(L, a[1]);
                break;
        case LIR_FORM_JMP:
                ok = label_valid(L, a[0]);
                break;
        case LIR_FORM_POLL:
                ok = label_valid(L, a[in->nargs - 1]);
                if (in->nargs == 4) {
                        ok = ok && compatible(L, LIR_PTR, a[0])
                                && compatible(L, LIR_PTR, a[1])
                                && compatible(L, LIR_PTR, a[2]);
                }
                break;
        case LIR_FORM_SWITCH:
                if (in->ntargets == 0 || in->ntargets > LIR_MAX_SWITCH) {
                        return fail(err, LIR_ERROR_LABEL, i, in->span, "invalid switch table size");
                }
                ok = isint(opclass(L, a[0])) && label_valid(L, a[1]);
                for (u32 j = 0; j < in->ntargets; ++j) {
                        ok = ok && label_valid(L, lir_l(in->targets[j]));
                }
                break;
        case LIR_FORM_RET:
                ok = L->sig.ret == LIR_VOID ? in->nargs == 0
                   : in->nargs == 1 && type_matches(L, L->sig.ret, a[0]);
                if (!ok) {
                        return fail(err, LIR_ERROR_RETURN, i, in->span, "return does not match signature");
                }
                break;
        case LIR_FORM_CALL:
        case LIR_FORM_TAILCALL:
                ok = call_valid(L, in);
                if (!ok) {
                        return fail(err, LIR_ERROR_SIGNATURE, i, in->span, "call does not match signature or flags");
                }
                break;
        case LIR_FORM_CAS:
        case LIR_FORM_ATOMIC:
                ok = (isint(d) || d == LIR_PTR) && a[0].kind == LIR_OPERAND_MEM;
                for (u32 j = 1; j < in->nargs; ++j) {
                        ok = ok && compatible(L, d, a[j]);
                }
                break;
        case LIR_FORM_FENCE:
                ok = true;
                break;
        case LIR_FORM_COPY:
                ok = a[0].kind == LIR_OPERAND_MEM && a[1].kind == LIR_OPERAND_MEM
                  && a[0].mem.index == LIR_NONE && a[1].mem.index == LIR_NONE;
                break;
        case LIR_FORM_ALLOCA:
                ok = d == LIR_PTR && a[0].kind == LIR_OPERAND_IMM && a[0].imm > 0
                  && a[0].imm <= INT32_MAX && a[1].kind == LIR_OPERAND_IMM
                  && a[1].imm > 0 && a[1].imm <= INT32_MAX
                  && (a[1].imm & (a[1].imm - 1)) == 0;
                break;
        case LIR_FORM_SITE:
                ok = a[0].kind == LIR_OPERAND_IMM && a[0].imm >= 0 && a[0].imm <= UINT32_MAX;
                break;
        case LIR_FORM_ENTRY:
                ok = label_valid(L, a[0]) && L->labels[a[0].label].pos == i
                  && L->labels[a[0].label].entry;
                break;
        case LIR_FORM_RAW:
                ok = in->raw.narm64 != 0 || in->raw.nx64 != 0;
                for (u32 j = 0; j < in->raw.nin; ++j) {
                        ok = ok && in->raw.in[j].reg < L->nregs && in->raw.in[j].phys < LIR_MAX_PHYS;
                }
                for (u32 j = 0; j < in->raw.nout; ++j) {
                        ok = ok && in->raw.out[j].reg < L->nregs && in->raw.out[j].phys < LIR_MAX_PHYS;
                }
                ok = ok && (in->raw.gpr_clobber >> LIR_MAX_PHYS) == 0
                        && (in->raw.fpr_clobber >> LIR_MAX_PHYS) == 0;
                break;
        }
        if (!ok) {
                return fail(err, LIR_ERROR_CLASS, i, in->span, "%s operand classes do not match", info->name);
        }
        return true;
}

static void
bit_set(u64 *bits, u32 r)
{
        bits[r / 64] |= (u64)1 << (r % 64);
}

static bool
bit_has(u64 const *bits, u32 r)
{
        return (bits[r / 64] >> (r % 64)) & 1;
}

static void
use_reg(u64 *use, u64 const *def, u32 const *global, u32 r)
{
        u32 g = global[r];
        if (g != LIR_NONE && !bit_has(def, g)) {
                bit_set(use, g);
        }
}

static void
use_operand(u64 *use, u64 const *def, u32 const *global, LirOpnd a)
{
        if (a.kind == LIR_OPERAND_REG) {
                use_reg(use, def, global, a.reg);
        } else if (a.kind == LIR_OPERAND_MEM) {
                use_reg(use, def, global, a.mem.base);
                if (a.mem.index != LIR_NONE) {
                        use_reg(use, def, global, a.mem.index);
                }
        }
}

static void
inst_uses(LirInst const *in, u64 *use, u64 const *def, u32 const *global)
{
        for (u32 i = 0; i < in->nargs; ++i) {
                use_operand(use, def, global, in->args[i]);
        }
        for (u32 i = 0; i < in->ncall_args; ++i) {
                use_operand(use, def, global, in->call_args[i]);
        }
        for (u32 i = 0; i < in->raw.nin; ++i) {
                use_reg(use, def, global, in->raw.in[i].reg);
        }
}

static void
def_reg(u64 *def, u32 const *global, u32 r)
{
        if (global[r] != LIR_NONE) {
                bit_set(def, global[r]);
        }
}

static void
inst_defs(LirInst const *in, u64 *def, u32 const *global)
{
        if (in->dst != LIR_NONE) {
                def_reg(def, global, in->dst);
        }
        for (u32 i = 0; i < in->raw.nout; ++i) {
                def_reg(def, global, in->raw.out[i].reg);
        }
}

static void
stamp_reg(u32 const *stamp, u32 *global, u32 tag, u32 r)
{
        if (stamp[r] != tag) {
                global[r] = 0;
        }
}

static void
stamp_operand(u32 const *stamp, u32 *global, u32 tag, LirOpnd a)
{
        if (a.kind == LIR_OPERAND_REG) {
                stamp_reg(stamp, global, tag, a.reg);
        } else if (a.kind == LIR_OPERAND_MEM) {
                stamp_reg(stamp, global, tag, a.mem.base);
                if (a.mem.index != LIR_NONE) {
                        stamp_reg(stamp, global, tag, a.mem.index);
                }
        }
}

static bool
find_globals(Lir const *L, LirCFG *cfg)
{
        u32 *stamp = calloc((usize)L->nregs + 1, sizeof *stamp);
        cfg->global = malloc(((usize)L->nregs + 1) * sizeof *cfg->global);
        cfg->globals = malloc(((usize)L->nregs + 1) * sizeof *cfg->globals);
        if (stamp == NULL || cfg->global == NULL || cfg->globals == NULL) {
                free(stamp);
                return false;
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                cfg->global[r] = LIR_NONE;
        }
        for (u32 b = 0; b < cfg->nblocks; ++b) {
                LirBlock const *block = &cfg->blocks[b];
                for (u32 j = block->first; j < block->end; ++j) {
                        LirInst const *in = &L->insts[j];
                        for (u32 i = 0; i < in->nargs; ++i) {
                                stamp_operand(stamp, cfg->global, b + 1, in->args[i]);
                        }
                        for (u32 i = 0; i < in->ncall_args; ++i) {
                                stamp_operand(stamp, cfg->global, b + 1, in->call_args[i]);
                        }
                        for (u32 i = 0; i < in->raw.nin; ++i) {
                                stamp_reg(stamp, cfg->global, b + 1, in->raw.in[i].reg);
                        }
                        if (in->dst != LIR_NONE) {
                                stamp[in->dst] = b + 1;
                        }
                        for (u32 i = 0; i < in->raw.nout; ++i) {
                                stamp[in->raw.out[i].reg] = b + 1;
                        }
                }
        }
        free(stamp);
        cfg->nglobals = 0;
        for (u32 r = 0; r < L->nregs; ++r) {
                if (cfg->global[r] != LIR_NONE) {
                        cfg->global[r] = cfg->nglobals;
                        cfg->globals[cfg->nglobals++] = r;
                }
        }
        return true;
}

static bool
isexit(LirInst const *in)
{
        return in->op == LIR_RET || in->op == LIR_TAILCALL || (in->flags & LIR_NORETURN);
}

static bool
isbranch(LirInst const *in)
{
        LirForm form = LirOps[in->op].form;
        return form == LIR_FORM_CHECKED || form == LIR_FORM_BR || form == LIR_FORM_FBR
            || form == LIR_FORM_BRZ || form == LIR_FORM_JMP || form == LIR_FORM_SWITCH
            || form == LIR_FORM_POLL;
}

static LirLabel
branch_label(LirInst const *in)
{
        return in->args[in->nargs - 1].label;
}

void
lir_cfg_free(LirCFG *cfg)
{
        free(cfg->sets);
        free(cfg->edges);
        free(cfg->blocks);
        free(cfg->block_at);
        free(cfg->global);
        free(cfg->globals);
        *cfg = (LirCFG) {0};
}

bool
lir_cfg(Lir const *L, LirCFG *cfg, LirError *err)
{
        bool *leaders = NULL;
        u32 *queue = NULL;
        u32 *npred = NULL;
        u32 *preds = NULL;
        u32 *fill = NULL;
        bool *inq = NULL;
        u32 pending = 0;
        u32 nb = 0;
        u32 qhead = 0;
        u32 qtail = 0;
        bool changed;
        *cfg = (LirCFG) {0};
        if (L->error.kind != LIR_ERROR_NONE) {
                if (err != NULL) {
                        *err = L->error;
                }
                return false;
        }
        for (u32 i = 0; i < L->nlabels; ++i) {
                if (L->labels[i].pos > L->ninsts) {
                        return fail(err, LIR_ERROR_LABEL, LIR_NONE, (LirSpan) {0},
                                    "label %u is unbound", i);
                }
        }
        for (u32 i = 0; !L->trusted && i < L->ninsts; ++i) {
                if (!inst_valid(L, i, err)) {
                        return false;
                }
        }
        leaders = calloc((usize)L->ninsts + 1, sizeof *leaders);
        cfg->block_at = calloc((usize)L->ninsts + 1, sizeof *cfg->block_at);
        if (leaders == NULL || cfg->block_at == NULL) {
                goto NoMemory;
        }
        leaders[0] = true;
        leaders[L->ninsts] = true;
        for (u32 i = 0; i < L->nlabels; ++i) {
                leaders[L->labels[i].pos] = true;
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                LirInst const *in = &L->insts[i];
                if (isexit(in) || isbranch(in) || (in->flags & LIR_RETURNS_TWICE)) {
                        leaders[i + 1] = true;
                }
                if (in->op == LIR_ENTRY) {
                        leaders[i] = true;
                }
        }
        for (u32 i = 0; i <= L->ninsts; ++i) {
                nb += leaders[i];
        }
        cfg->blocks = calloc(nb, sizeof *cfg->blocks);
        queue = calloc(nb, sizeof *queue);
        if (cfg->blocks == NULL || queue == NULL) {
                goto NoMemory;
        }
        cfg->nblocks = nb;
        nb = 0;
        for (u32 i = 0; i <= L->ninsts; ++i) {
                if (leaders[i]) {
                        if (nb != 0) {
                                cfg->blocks[nb - 1].end = i;
                        }
                        cfg->blocks[nb++].first = i;
                }
                cfg->block_at[i] = nb - 1;
        }
        cfg->blocks[nb - 1].end = L->ninsts;
        for (u32 i = 0; i < L->nlabels; ++i) {
                if (L->labels[i].entry) {
                        u32 b = cfg->block_at[L->labels[i].pos];
                        cfg->blocks[b].entry = true;
                }
        }
        if (!find_globals(L, cfg)) {
                goto NoMemory;
        }
        cfg->nwords = (cfg->nglobals + (usize)63) / 64;
        usize nedges = 0;
        for (u32 i = 0; i < nb; ++i) {
                LirBlock const *b = &cfg->blocks[i];
                if (b->first == b->end) {
                        continue;
                }
                LirInst const *in = &L->insts[b->end - 1];
                nedges += 1;
                if (isbranch(in)) {
                        nedges += in->op == LIR_SWITCH ? in->ntargets + 1 : 1;
                }
        }
        usize words = cfg->nwords == 0 ? 1 : cfg->nwords;
        cfg->sets = calloc(nb * words * 4, sizeof *cfg->sets);
        cfg->edges = malloc((nedges + 1) * sizeof *cfg->edges);
        if (cfg->sets == NULL || cfg->edges == NULL) {
                goto NoMemory;
        }
        nedges = 0;
        for (u32 i = 0; i < nb; ++i) {
                LirBlock *b = &cfg->blocks[i];
                usize nw = words;
                b->use = cfg->sets + i * nw * 4;
                b->def      = b->use + nw;
                b->live_in  = b->def + nw;
                b->live_out = b->live_in + nw;
                for (u32 j = b->first; j < b->end; ++j) {
                        inst_uses(&L->insts[j], b->use, b->def, cfg->global);
                        inst_defs(&L->insts[j], b->def, cfg->global);
                }
                if (b->first == b->end) {
                        continue;
                }
                LirInst const *in = &L->insts[b->end - 1];
                u32 n = 1;
                if (isbranch(in)) {
                        n += in->op == LIR_SWITCH ? in->ntargets + 1 : 1;
                }
                b->succ = cfg->edges + nedges;
                nedges += n;
                if (isbranch(in)) {
                        b->succ[b->nsucc++] = cfg->block_at[L->labels[branch_label(in)].pos];
                        for (u32 j = 0; j < in->ntargets; ++j) {
                                b->succ[b->nsucc++] = cfg->block_at[L->labels[in->targets[j]].pos];
                        }
                }
                if (!isexit(in) && in->op != LIR_JMP && in->op != LIR_SWITCH) {
                        b->succ[b->nsucc++] = cfg->block_at[b->end];
                }
        }
        for (u32 i = 0; i < nb; ++i) {
                if (i == 0 || cfg->blocks[i].entry) {
                        cfg->blocks[i].reachable = true;
                        queue[qtail++] = i;
                }
        }
        while (qhead < qtail) {
                LirBlock const *b = &cfg->blocks[queue[qhead++]];
                for (u32 i = 0; i < b->nsucc; ++i) {
                        LirBlock *next = &cfg->blocks[b->succ[i]];
                        if (!next->reachable) {
                                next->reachable = true;
                                queue[qtail++] = b->succ[i];
                        }
                }
        }
        npred = calloc((usize)nb + 1, sizeof *npred);
        inq = calloc(nb, sizeof *inq);
        if (npred == NULL || inq == NULL) {
                goto NoMemory;
        }
        for (u32 i = 0; i < nb; ++i) {
                LirBlock const *b = &cfg->blocks[i];
                for (u32 j = 0; j < b->nsucc; ++j) {
                        npred[b->succ[j] + 1] += 1;
                }
        }
        for (u32 i = 0; i < nb; ++i) {
                npred[i + 1] += npred[i];
        }
        preds = malloc(((usize)npred[nb] + 1) * sizeof *preds);
        fill = calloc(nb, sizeof *fill);
        if (preds == NULL || fill == NULL) {
                goto NoMemory;
        }
        for (u32 i = 0; i < nb; ++i) {
                LirBlock const *b = &cfg->blocks[i];
                for (u32 j = 0; j < b->nsucc; ++j) {
                        u32 t = b->succ[j];
                        preds[npred[t] + fill[t]++] = i;
                }
        }
        qhead = 0;
        qtail = 0;
        for (u32 i = nb; i-- > 0;) {
                if (cfg->blocks[i].reachable) {
                        queue[qtail++] = i;
                        inq[i] = true;
                }
        }
        pending = qtail;
        qtail = qtail == nb ? 0 : qtail;
        while (pending != 0) {
                u32 bi = queue[qhead];
                qhead = qhead + 1 == nb ? 0 : qhead + 1;
                pending -= 1;
                inq[bi] = false;
                LirBlock *b = &cfg->blocks[bi];
                changed = false;
                for (u32 w = 0; w < cfg->nwords; ++w) {
                        u64 out = 0;
                        u64 in;
                        for (u32 j = 0; j < b->nsucc; ++j) {
                                out |= cfg->blocks[b->succ[j]].live_in[w];
                        }
                        in = b->use[w] | (out & ~b->def[w]);
                        changed = changed || in != b->live_in[w];
                        b->live_in[w]  = in;
                        b->live_out[w] = out;
                }
                if (!changed) {
                        continue;
                }
                for (u32 j = npred[bi]; j < npred[bi + 1]; ++j) {
                        u32 p = preds[j];
                        if (!inq[p] && cfg->blocks[p].reachable) {
                                inq[p] = true;
                                queue[qtail] = p;
                                qtail = qtail + 1 == nb ? 0 : qtail + 1;
                                pending += 1;
                        }
                }
        }
        free(leaders);
        free(queue);
        free(npred);
        free(preds);
        free(fill);
        free(inq);
        return true;
NoMemory:
        fail(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory building CFG");
        free(leaders);
        free(queue);
        free(npred);
        free(preds);
        free(fill);
        free(inq);
        lir_cfg_free(cfg);
        return false;
}

static bool
attached_operand(LirOpnd a)
{
        return a.kind == LIR_OPERAND_CONST || a.kind == LIR_OPERAND_REFCONST
            || a.kind == LIR_OPERAND_VSLOT || a.kind == LIR_HOLE_CONST
            || (a.kind == LIR_OPERAND_CODE && a.code->mode == LIR_MODE_ATTACHED);
}

static bool
resolve_mode(Lir *L, LirError *err);

bool
lir_prepare(Lir *L, LirError *err)
{
        if (err != NULL) {
                *err = (LirError) {0};
        }
        if (L->error.kind != LIR_ERROR_NONE) {
                if (err != NULL) {
                        *err = L->error;
                }
                return false;
        }
        for (u32 i = 0; i < L->nlabels; ++i) {
                if (L->labels[i].pos > L->ninsts) {
                        return fail(err, LIR_ERROR_LABEL, LIR_NONE, (LirSpan) {0},
                                    "label %u is unbound", i);
                }
        }
        L->trusted = getenv("TY_JIT_VALIDATE") == NULL;
        return resolve_mode(L, err);
}

bool
lir_validate(Lir *L, LirError *err)
{
        LirCFG cfg;
        bool ok = false;
        if (err != NULL) {
                *err = (LirError) {0};
        }
        if (L->error.kind != LIR_ERROR_NONE) {
                if (err != NULL) {
                        *err = L->error;
                }
                return false;
        }
        if (!sig_valid(&L->sig) || L->sig.variadic
            || (u32)L->mode > LIR_MODE_ATTACHED
            || L->sig.nparams > L->nregs
            || (L->sig.nparams != 0 && L->params == NULL)) {
                return fail(err, LIR_ERROR_SIGNATURE, LIR_NONE, (LirSpan) {0}, "invalid function signature");
        }
        for (u32 i = 0; i < L->nlabels; ++i) {
                if (L->labels[i].pos > L->ninsts) {
                        return fail(err, LIR_ERROR_LABEL, LIR_NONE, (LirSpan) {0},
                                    "label %u is unbound", i);
                }
        }
        for (u32 i = 0; i < L->nregs; ++i) {
                LirRegInfo const *ri = &L->regs[i];
                if ((u32)ri->cls >= LIR_CLASS_COUNT
                    || (ri->pin != LIR_NONE
                        && (ri->pin >= LIR_MAX_PINS || isfloat(ri->cls)
                            || L->pins[ri->pin] != i))) {
                        return fail(err, LIR_ERROR_CLASS, LIR_NONE, (LirSpan) {0},
                                    "register r%u has invalid class or pin metadata", i);
                }
                if (ri->param != LIR_NONE
                    && (ri->param >= L->sig.nparams
                        || ri->cls != lir_type_class(L->sig.params[ri->param]))) {
                        return fail(err, LIR_ERROR_SIGNATURE, LIR_NONE, (LirSpan) {0},
                                    "register r%u has invalid parameter metadata", i);
                }
        }
        for (u32 i = 0; i < L->sig.nparams; ++i) {
                if (L->params[i] >= L->nregs || L->regs[L->params[i]].param != i) {
                        return fail(err, LIR_ERROR_SIGNATURE, LIR_NONE, (LirSpan) {0},
                                    "invalid parameter register");
                }
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                if (!inst_valid(L, i, err)) {
                        return false;
                }
        }
        if (!resolve_mode(L, err)) {
                return false;
        }
        if (!lir_cfg(L, &cfg, err)) {
                return false;
        }
        for (u32 i = 0; i < cfg.nblocks; ++i) {
                LirBlock const *b = &cfg.blocks[i];
                if (!b->reachable) {
                        continue;
                }
                if (b->first == L->ninsts && L->sig.ret != LIR_VOID) {
                        fail(err, LIR_ERROR_RETURN, L->ninsts, (LirSpan) {0}, "non-void function can fall off the end");
                        goto End;
                }
                if (i == 0 || b->entry) {
                        for (u32 g = 0; g < cfg.nglobals; ++g) {
                                u32 r = cfg.globals[g];
                                bool pin = L->regs[r].pin != LIR_NONE;
                                bool param = L->regs[r].param != LIR_NONE;
                                if (bit_has(b->live_in, g) && !pin && (b->entry || !param)) {
                                        u32 pos = b->first;
                                        LirSpan span = pos < L->ninsts ? L->insts[pos].span : (LirSpan) {0};
                                        fail(err, b->entry ? LIR_ERROR_ENTRY : LIR_ERROR_UNDEFINED,
                                             pos, span, "register r%u is live into %s", r,
                                             b->entry ? "resume entry" : "function before definition");
                                        goto End;
                                }
                        }
                }
                if (b->first == b->end) {
                        continue;
                }
                LirInst const *in = &L->insts[b->end - 1];
                if (in->flags & LIR_RETURNS_TWICE) {
                        for (u32 g = 0; g < cfg.nglobals; ++g) {
                                u32 r = cfg.globals[g];
                                if (r != in->dst && L->regs[r].pin == LIR_NONE && bit_has(b->live_out, g)) {
                                        fail(err, LIR_ERROR_RETURNS_TWICE, b->end - 1, in->span,
                                             "register r%u is live across RETURNS_TWICE", r);
                                        goto End;
                                }
                        }
                }
        }
        ok = true;
End:
        lir_cfg_free(&cfg);
        return ok;
}

static void
dump_operand(LirOpnd a, FILE *out)
{
        switch (a.kind) {
        case LIR_OPERAND_REG: fprintf(out, "r%u", a.reg); break;
        case LIR_OPERAND_IMM: fprintf(out, "%" PRId64, a.imm); break;
        case LIR_OPERAND_FIMM: fprintf(out, "%.17g", a.fimm); break;
        case LIR_OPERAND_LABEL: fprintf(out, "L%u", a.label); break;
        case LIR_OPERAND_CC: fprintf(out, "cc%u", a.cc); break;
        case LIR_OPERAND_MEM:
                fprintf(out, "[r%u", a.mem.base);
                if (a.mem.index != LIR_NONE) {
                        fprintf(out, "+r%u*%u", a.mem.index, a.mem.scale);
                }
                fprintf(out, "%+d]", a.mem.disp);
                break;
        case LIR_OPERAND_CODE: fprintf(out, "code(%s)", a.code->name); break;
        case LIR_OPERAND_HELPER: fprintf(out, "rt.%s", a.helper->name); break;
        default: fprintf(out, "operand%u(%u)", a.kind, a.index); break;
        }
}

void
lir_dump(Lir const *L, FILE *out)
{
        static char const *const names[] = { "i32", "i64", "f32", "f64", "ptr", "ref" };
        fprintf(out, "%s: %u registers, %u vslots\n", L->name, L->nregs, L->nvslots);
        for (u32 r = 0; r < L->nregs; ++r) {
                fprintf(out, "  r%u: %s", r, names[L->regs[r].cls]);
                if (L->regs[r].param != LIR_NONE) {
                        fprintf(out, " param%u", L->regs[r].param);
                }
                if (L->regs[r].pin != LIR_NONE) {
                        fprintf(out, " pin%u", L->regs[r].pin);
                }
                fputc('\n', out);
        }
        for (u32 i = 0; i <= L->ninsts; ++i) {
                for (u32 j = 0; j < L->nlabels; ++j) {
                        if (L->labels[j].pos == i) {
                                fprintf(out, "L%u:\n", j);
                        }
                }
                if (i == L->ninsts) {
                        break;
                }
                LirInst const *in = &L->insts[i];
                fprintf(out, "  %u  %s", i, LirOps[in->op].name);
                if (in->dst != LIR_NONE) {
                        fprintf(out, " r%u%s", in->dst, in->nargs != 0 ? "," : "");
                }
                for (u32 j = 0; j < in->nargs; ++j) {
                        fputs(j == 0 ? " " : ", ", out);
                        dump_operand(in->args[j], out);
                }
                for (u32 j = 0; j < in->ncall_args; ++j) {
                        fputs(j == 0 ? " (" : ", ", out);
                        dump_operand(in->call_args[j], out);
                }
                if (in->ncall_args != 0) {
                        fputc(')', out);
                }
                for (u32 j = 0; j < in->ntargets; ++j) {
                        fprintf(out, " L%u", in->targets[j]);
                }
                fputc('\n', out);
        }
}

typedef struct lir_writer {
        LirBytes *bytes;
        usize capacity;
        bool ok;
} LirWriter;

typedef struct lir_reader {
        u8 const *data;
        usize size;
        usize pos;
        bool ok;
} LirReader;

static void
write_bytes(LirWriter *w, void const *data, usize n)
{
        usize cap = w->capacity;
        usize end;
        void *p;
        if (!w->ok || n > SIZE_MAX - w->bytes->count) {
                w->ok = false;
                return;
        }
        end = w->bytes->count + n;
        if (end > cap) {
                cap = cap == 0 ? 128 : cap;
                while (cap < end) {
                        if (cap > SIZE_MAX / 2) {
                                cap = end;
                                break;
                        }
                        cap *= 2;
                }
                p = realloc(w->bytes->items, cap);
                if (p == NULL) {
                        w->ok = false;
                        return;
                }
                w->bytes->items = p;
                w->capacity = cap;
        }
        if (n != 0) {
                memcpy(w->bytes->items + w->bytes->count, data, n);
        }
        w->bytes->count = end;
}

static void
write_uint(LirWriter *w, u64 n)
{
        u8 buf[10];
        u32 i = 0;
        do {
                buf[i++] = (n & 0x7f) | (n >= 128 ? 0x80 : 0);
                n >>= 7;
        } while (n != 0);
        write_bytes(w, buf, i);
}

static void
write_int(LirWriter *w, i64 n)
{
        write_uint(w, ((u64)n << 1) ^ (u64)-(n < 0));
}

static bool
read_bytes(LirReader *r, void *out, usize n)
{
        if (!r->ok || n > r->size - r->pos) {
                r->ok = false;
                return false;
        }
        if (n != 0 && out != NULL) {
                memcpy(out, r->data + r->pos, n);
        }
        r->pos += n;
        return true;
}

static u64
read_uint(LirReader *r)
{
        u64 n = 0;
        u8 b;
        for (u32 i = 0; i < 10; ++i) {
                if (!read_bytes(r, &b, 1) || (i == 9 && b > 1)) {
                        r->ok = false;
                        return 0;
                }
                n |= (u64)(b & 0x7f) << (7 * i);
                if ((b & 0x80) == 0) {
                        if (i != 0 && b == 0) {
                                r->ok = false;
                        }
                        return n;
                }
        }
        r->ok = false;
        return 0;
}

static u32
read_u32(LirReader *r)
{
        u64 n = read_uint(r);
        if (n > UINT32_MAX) {
                r->ok = false;
                return 0;
        }
        return n;
}

static i64
read_int(LirReader *r)
{
        u64 n = read_uint(r);
        u64 bits = (n >> 1) ^ (u64)-(n & 1);
        i64 result;
        memcpy(&result, &bits, sizeof result);
        return result;
}

static u32
read_count(LirReader *r, usize size)
{
        u32 n = read_u32(r);
        if (n > r->size - r->pos || n > SIZE_MAX / size) {
                r->ok = false;
                return 0;
        }
        return n;
}

static bool
hole_operand(LirOpnd a)
{
        return a.kind >= LIR_HOLE_IMM && a.kind <= LIR_HOLE_CALLEE;
}

static bool
hole_limit(LirOpnd a, u32 *n)
{
        if (hole_operand(a)) {
                if (a.index == UINT32_MAX) {
                        return false;
                }
                if (a.index >= *n) {
                        *n = a.index + 1;
                }
        }
        return true;
}

static bool
capture(LirBytes *bytes, LirOpnd a, u32 *index)
{
        LirBinding *p;
        for (u32 i = bytes->ninputs; i < bytes->nholes; ++i) {
                LirOpnd b = bytes->holes[i].operand;
                if (a.kind == b.kind
                    && ((a.kind == LIR_OPERAND_CODE && a.code == b.code)
                        || (a.kind == LIR_OPERAND_HELPER && a.helper == b.helper)
                        || (a.kind == LIR_OPERAND_IMM && a.imm == b.imm))) {
                        *index = i;
                        return true;
                }
        }
        if (bytes->nholes == UINT32_MAX
            || (usize)bytes->nholes + 1 > SIZE_MAX / sizeof *p) {
                return false;
        }
        p = realloc(bytes->holes, ((usize)bytes->nholes + 1) * sizeof *p);
        if (p == NULL) {
                return false;
        }
        bytes->holes = p;
        *index = bytes->nholes++;
        p[*index] = (LirBinding) { .operand = a };
        return true;
}

static void
write_operand(LirWriter *w, LirOpnd a)
{
        u32 index;
        write_uint(w, a.kind);
        switch (a.kind) {
        case LIR_OPERAND_IMM:
                write_int(w, a.imm);
                break;
        case LIR_OPERAND_FIMM: {
                u64 bits;
                u8 buf[8];
                memcpy(&bits, &a.fimm, sizeof bits);
                for (u32 i = 0; i < 8; ++i) {
                        buf[i] = bits >> (8 * i);
                }
                write_bytes(w, buf, sizeof buf);
                break;
        }
        case LIR_OPERAND_MEM:
                write_uint(w, a.mem.base);
                write_uint(w, a.mem.index);
                write_uint(w, a.mem.scale);
                write_int(w, a.mem.disp);
                break;
        case LIR_OPERAND_REG: write_uint(w, a.reg); break;
        case LIR_OPERAND_LABEL: write_uint(w, a.label); break;
        case LIR_OPERAND_CC: write_uint(w, a.cc); break;
        case LIR_OPERAND_CODE:
        case LIR_OPERAND_HELPER:
                if (!capture(w->bytes, a, &index)) {
                        w->ok = false;
                        return;
                }
                write_uint(w, index);
                break;
        default:
                write_uint(w, a.index);
                break;
        }
}

static void
write_pointer_operand(LirWriter *w, LirOpnd a, bool callee)
{
        if (a.kind == LIR_OPERAND_IMM) {
                u32 index;
                if (!capture(w->bytes, a, &index)) {
                        w->ok = false;
                        return;
                }
                a = lir_hole(callee ? LIR_HOLE_CALLEE : LIR_HOLE_PTR, index);
        }
        write_operand(w, a);
}

static LirOpnd
read_operand(LirReader *r, LirBinding const *holes, u32 nholes)
{
        LirOpnd a = { .kind = read_u32(r) };
        switch (a.kind) {
        case LIR_OPERAND_IMM:
                a.imm = read_int(r);
                break;
        case LIR_OPERAND_FIMM: {
                u8 buf[8];
                u64 bits = 0;
                if (!read_bytes(r, buf, sizeof buf)) {
                        return (LirOpnd) {0};
                }
                for (u32 i = 0; i < 8; ++i) {
                        bits |= (u64)buf[i] << (8 * i);
                }
                memcpy(&a.fimm, &bits, sizeof a.fimm);
                break;
        }
        case LIR_OPERAND_MEM: {
                i64 disp;
                u32 scale;
                a.mem.base  = read_u32(r);
                a.mem.index = read_u32(r);
                scale = read_u32(r);
                disp = read_int(r);
                if (scale > UINT8_MAX || disp < INT32_MIN || disp > INT32_MAX) {
                        r->ok = false;
                }
                a.mem.scale = scale;
                a.mem.disp  = disp;
                break;
        }
        case LIR_OPERAND_REG: a.reg = read_u32(r); break;
        case LIR_OPERAND_LABEL: a.label = read_u32(r); break;
        case LIR_OPERAND_CC: a.cc = read_u32(r); break;
        case LIR_OPERAND_CODE:
        case LIR_OPERAND_HELPER: {
                u32 i = read_u32(r);
                if (i >= nholes || holes[i].operand.kind != a.kind) {
                        r->ok = false;
                } else {
                        a = holes[i].operand;
                }
                break;
        }
        case LIR_OPERAND_CONST:
        case LIR_OPERAND_REFCONST:
        case LIR_OPERAND_VSLOT:
        case LIR_HOLE_IMM:
        case LIR_HOLE_FIMM:
        case LIR_HOLE_PTR:
        case LIR_HOLE_CONST:
        case LIR_HOLE_CALLEE:
                a.index = read_u32(r);
                break;
        default:
                r->ok = false;
                break;
        }
        return a;
}

static void
write_sig(LirWriter *w, LirSig const *sig)
{
        write_uint(w, sig->ret);
        write_uint(w, sig->nparams);
        write_uint(w, sig->variadic);
        write_uint(w, sig->nfixed);
        for (u32 i = 0; i < sig->nparams; ++i) {
                write_uint(w, sig->params[i]);
        }
}

static bool
read_sig(LirReader *r, LirSig *sig)
{
        u32 variadic;
        LirType *params;
        sig->ret     = read_u32(r);
        sig->nparams = read_count(r, sizeof *params);
        variadic     = read_u32(r);
        sig->nfixed  = read_u32(r);
        sig->variadic = variadic;
        if (variadic > 1) {
                r->ok = false;
        }
        params = calloc(sig->nparams, sizeof *params);
        sig->params = params;
        if (sig->nparams != 0 && params == NULL) {
                return false;
        }
        for (u32 i = 0; i < sig->nparams; ++i) {
                params[i] = read_u32(r);
        }
        return r->ok;
}

void
lir_bytes_free(LirBytes *bytes)
{
        for (u32 i = bytes->ninputs; i < bytes->nholes; ++i) {
                free(bytes->holes[i].value);
        }
        free(bytes->holes);
        free(bytes->items);
        *bytes = (LirBytes) {0};
}

bool
lir_serialize(Lir *L, LirBytes *bytes, LirError *err)
{
        LirWriter w = { .bytes = bytes, .ok = true };
        u32 ninputs = 0;
        *bytes = (LirBytes) {0};
        if (!lir_validate(L, err)) {
                return false;
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                LirInst const *in = &L->insts[i];
                for (u32 j = 0; j < in->nargs; ++j) {
                        if (!hole_limit(in->args[j], &ninputs)) {
                                goto BadHole;
                        }
                }
                for (u32 j = 0; j < in->ncall_args; ++j) {
                        if (!hole_limit(in->call_args[j], &ninputs)) {
                                goto BadHole;
                        }
                }
        }
        if (L->nroots > UINT32_MAX - ninputs) {
                goto NoMemory;
        }
        bytes->ninputs = ninputs;
        bytes->nholes = ninputs + L->nroots;
        if ((usize)bytes->nholes > SIZE_MAX / sizeof *bytes->holes) {
                bytes->nholes = 0;
                goto NoMemory;
        }
        bytes->holes = calloc(bytes->nholes, sizeof *bytes->holes);
        if (bytes->nholes != 0 && bytes->holes == NULL) {
                bytes->nholes = 0;
                goto NoMemory;
        }
        for (u32 i = 0; i < L->nroots; ++i) {
                LirBinding *b = &bytes->holes[ninputs + i];
                b->operand.kind = LIR_OPERAND_CONST;
                b->value = copy(&L->roots[i], 1, sizeof *b->value);
                if (b->value == NULL) {
                        goto NoMemory;
                }
        }
        u32 version = 1;
        for (u32 i = 0; i < L->ninsts; ++i) {
                LirInst const *in = &L->insts[i];
                if ((in->op == LIR_POLL && (in->flags != 0 || in->tag != 0))
                    || (in->op == LIR_ENTRY && in->tag != 0)) {
                        version = 2;
                }
        }
        write_bytes(&w, "TYLR", 4);
        write_uint(&w, version);
        write_uint(&w, strlen(L->name));
        write_bytes(&w, L->name, strlen(L->name));
        write_sig(&w, &L->sig);
        write_uint(&w, L->mode);
        write_uint(&w, L->nvslots);
        write_uint(&w, L->pc_param);
        write_uint(&w, L->nregs);
        for (u32 i = 0; i < L->nregs; ++i) {
                write_uint(&w, L->regs[i].cls);
                write_uint(&w, L->regs[i].param);
                write_uint(&w, L->regs[i].pin);
        }
        write_uint(&w, L->nlabels);
        for (u32 i = 0; i < L->nlabels; ++i) {
                write_uint(&w, L->labels[i].pos);
                write_uint(&w, L->labels[i].entry);
        }
        write_uint(&w, L->nroots);
        for (u32 i = 0; i < L->nroots; ++i) {
                write_uint(&w, ninputs + i);
        }
        write_uint(&w, L->ninsts);
        for (u32 i = 0; i < L->ninsts; ++i) {
                LirInst const *in = &L->insts[i];
                write_uint(&w, in->op);
                write_uint(&w, in->dst);
                write_uint(&w, in->nargs);
                write_uint(&w, in->span.source);
                write_uint(&w, in->span.start);
                write_uint(&w, in->span.end);
                for (u32 j = 0; j < in->nargs; ++j) {
                        bool callee = j == 0 && (in->op == LIR_CALL || in->op == LIR_TAILCALL);
                        bool pointer = j == 0 && (((in->op == LIR_LI || in->op == LIR_MOV)
                                                  && L->regs[in->dst].cls == LIR_PTR)
                                                 || (in->op == LIR_RET && L->sig.ret == LIR_TYPE_PTR));
                        if (callee || pointer) {
                                write_pointer_operand(&w, in->args[j], callee);
                        } else {
                                write_operand(&w, in->args[j]);
                        }
                }
                if (in->op == LIR_CALL || in->op == LIR_TAILCALL) {
                        write_sig(&w, &in->sig);
                        write_uint(&w, in->flags);
                        write_uint(&w, in->tag);
                        for (u32 j = 0; j < in->ncall_args; ++j) {
                                if (in->sig.params[j] == LIR_TYPE_PTR) {
                                        write_pointer_operand(&w, in->call_args[j], false);
                                } else {
                                        write_operand(&w, in->call_args[j]);
                                }
                        }
                } else if (in->op == LIR_POLL && version >= 2) {
                        write_uint(&w, in->flags);
                        write_uint(&w, in->tag);
                } else if (in->op == LIR_ENTRY && version >= 2) {
                        write_uint(&w, in->tag);
                } else if (in->op == LIR_SWITCH) {
                        write_uint(&w, in->ntargets);
                        for (u32 j = 0; j < in->ntargets; ++j) {
                                write_uint(&w, in->targets[j]);
                        }
                } else if (in->op == LIR_RAW) {
                        write_uint(&w, in->raw.narm64);
                        for (u32 j = 0; j < in->raw.narm64; ++j) {
                                write_uint(&w, in->raw.arm64[j]);
                        }
                        write_uint(&w, in->raw.nx64);
                        write_bytes(&w, in->raw.x64, in->raw.nx64);
                        write_uint(&w, in->raw.nin);
                        for (u32 j = 0; j < in->raw.nin; ++j) {
                                write_uint(&w, in->raw.in[j].phys);
                                write_uint(&w, in->raw.in[j].reg);
                        }
                        write_uint(&w, in->raw.nout);
                        for (u32 j = 0; j < in->raw.nout; ++j) {
                                write_uint(&w, in->raw.out[j].phys);
                                write_uint(&w, in->raw.out[j].reg);
                        }
                        write_uint(&w, in->raw.gpr_clobber);
                        write_uint(&w, in->raw.fpr_clobber);
                }
        }
        if (!w.ok) {
                goto NoMemory;
        }
        return true;
BadHole:
        lir_bytes_free(bytes);
        return fail(err, LIR_ERROR_ENCODING, LIR_NONE, (LirSpan) {0}, "hole index is too large");
NoMemory:
        lir_bytes_free(bytes);
        return fail(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory serializing LIR");
}

static bool
read_raw(LirReader *r, LirRaw *raw)
{
        u32 *words;
        u8 *bytes;
        LirRawBinding *in;
        LirRawBinding *out;
        raw->narm64 = read_count(r, sizeof *words);
        words = calloc(raw->narm64, sizeof *words);
        raw->arm64 = words;
        if (raw->narm64 != 0 && words == NULL) {
                return false;
        }
        for (u32 i = 0; i < raw->narm64; ++i) {
                words[i] = read_u32(r);
        }
        raw->nx64 = read_count(r, 1);
        bytes = malloc(raw->nx64);
        raw->x64 = bytes;
        if (raw->nx64 != 0 && bytes == NULL) {
                return false;
        }
        read_bytes(r, bytes, raw->nx64);
        raw->nin = read_count(r, sizeof *in);
        in = calloc(raw->nin, sizeof *in);
        raw->in = in;
        if (raw->nin != 0 && in == NULL) {
                return false;
        }
        for (u32 i = 0; i < raw->nin; ++i) {
                u32 phys = read_u32(r);
                if (phys >= LIR_MAX_PHYS) {
                        r->ok = false;
                }
                in[i].phys = phys;
                in[i].reg  = read_u32(r);
        }
        raw->nout = read_count(r, sizeof *out);
        out = calloc(raw->nout, sizeof *out);
        raw->out = out;
        if (raw->nout != 0 && out == NULL) {
                return false;
        }
        for (u32 i = 0; i < raw->nout; ++i) {
                u32 phys = read_u32(r);
                if (phys >= LIR_MAX_PHYS) {
                        r->ok = false;
                }
                out[i].phys = phys;
                out[i].reg  = read_u32(r);
        }
        raw->gpr_clobber = read_uint(r);
        raw->fpr_clobber = read_uint(r);
        return r->ok;
}

static bool
fill_operand(Lir *L, LirOpnd *a, LirBinding const *holes, u32 nholes)
{
        LirOpnd b;
        LirOperandKind kind = a->kind;
        if (!hole_operand(*a)) {
                return true;
        }
        if (a->index >= nholes) {
                return false;
        }
        b = holes[a->index].operand;
        switch (kind) {
        case LIR_HOLE_IMM:
        case LIR_HOLE_PTR:
                if (b.kind != LIR_OPERAND_IMM) {
                        return false;
                }
                break;
        case LIR_HOLE_FIMM:
                if (b.kind != LIR_OPERAND_FIMM) {
                        return false;
                }
                break;
        case LIR_HOLE_CONST:
                if (holes[a->index].value == NULL) {
                        return false;
                }
                b = lir_const(L, holes[a->index].value);
                if (b.kind != LIR_OPERAND_CONST) {
                        return false;
                }
                break;
        case LIR_HOLE_CALLEE:
                if (b.kind != LIR_OPERAND_IMM && b.kind != LIR_OPERAND_CODE
                    && b.kind != LIR_OPERAND_HELPER) {
                        return false;
                }
                break;
        default: return false;
        }
        *a = b;
        return true;
}

static bool
resolve_mode(Lir *L, LirError *err)
{
        bool attached = L->nvslots != 0 || L->sig.ret == LIR_TYPE_VAL
                     || L->sig.ret == LIR_TYPE_REF;
        for (u32 i = 0; i < L->sig.nparams; ++i) {
                attached = attached || L->sig.params[i] == LIR_TYPE_VAL
                                    || L->sig.params[i] == LIR_TYPE_REF;
        }
        for (u32 i = 0; i < L->nregs; ++i) {
                attached = attached || L->regs[i].cls == LIR_REF;
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                LirInst const *in = &L->insts[i];
                bool vm = in->op == LIR_POLL || (in->flags & LIR_MAY_GC);
                if (in->op == LIR_CALL || in->op == LIR_TAILCALL) {
                        vm = vm || in->sig.ret == LIR_TYPE_VAL || in->sig.ret == LIR_TYPE_REF;
                        for (u32 j = 0; j < in->sig.nparams; ++j) {
                                vm = vm || in->sig.params[j] == LIR_TYPE_VAL
                                        || in->sig.params[j] == LIR_TYPE_REF;
                        }
                }
                for (u32 j = 0; j < in->nargs; ++j) {
                        vm = vm || attached_operand(in->args[j]);
                }
                for (u32 j = 0; j < in->ncall_args; ++j) {
                        vm = vm || attached_operand(in->call_args[j]);
                }
                if (vm && L->mode == LIR_MODE_DETACHED) {
                        return fail(err, LIR_ERROR_MODE, i, in->span,
                                    "VM values or safepoints in detached function");
                }
                attached = attached || vm;
        }
        if (attached && L->mode == LIR_MODE_DETACHED) {
                return fail(err, LIR_ERROR_MODE, LIR_NONE, (LirSpan) {0},
                            "REF registers or value slots in detached function");
        }
        L->resolved_mode = L->mode == LIR_MODE_AUTO
                        ? (attached ? LIR_MODE_ATTACHED : LIR_MODE_DETACHED) : L->mode;
        return true;
}

Lir *
lir_deserialize(void const *bytes, usize size, LirBinding const *holes, u32 nholes, LirError *err)
{
        LirReader r = { .data = bytes, .size = size, .ok = true };
        LirSig sig = {0};
        Lir *L = NULL;
        LirInst in = { .dst = LIR_NONE };
        char magic[4];
        char *name = NULL;
        u32 n;
        u32 mode;
        u32 version;
        if (bytes == NULL || (nholes != 0 && holes == NULL)
            || !read_bytes(&r, magic, sizeof magic) || memcmp(magic, "TYLR", 4) != 0
            || ((version = read_u32(&r)) != 1 && version != 2)) {
                goto BadEncoding;
        }
        n = read_count(&r, 1);
        name = malloc((usize)n + 1);
        if (name == NULL) {
                goto NoMemory;
        }
        read_bytes(&r, name, n);
        name[n] = '\0';
        if (!r.ok || memchr(name, '\0', n) != NULL || !read_sig(&r, &sig)) {
                goto BadEncoding;
        }
        mode = read_u32(&r);
        L = lir_new(name, &sig, mode, err);
        if (L == NULL) {
                goto Error;
        }
        free(name);
        name = NULL;
        free((void *)sig.params);
        sig.params = NULL;
        L->nvslots = read_u32(&r);
        L->pc_param = read_u32(&r);
        if (L->pc_param != LIR_NONE
            && (L->pc_param >= L->sig.nparams || L->sig.params[L->pc_param] != LIR_TYPE_PTR)) {
                goto BadEncoding;
        }
        n = read_count(&r, sizeof *L->regs);
        if (n < L->sig.nparams || !grow(&L->regs, &L->reg_capacity, n, sizeof *L->regs)) {
                goto BadEncoding;
        }
        L->nregs = n;
        for (u32 i = 0; i < n; ++i) {
                LirRegInfo *ri = &L->regs[i];
                ri->cls   = read_u32(&r);
                ri->param = read_u32(&r);
                ri->pin   = read_u32(&r);
                if (ri->cls >= LIR_CLASS_COUNT
                    || (ri->param != LIR_NONE
                        && (ri->param >= L->sig.nparams
                            || ri->cls != lir_type_class(L->sig.params[ri->param])))
                    || (i < L->sig.nparams && ri->param != i)) {
                        goto BadEncoding;
                }
                if (ri->pin != LIR_NONE) {
                        if (ri->pin >= LIR_MAX_PINS || L->pins[ri->pin] != LIR_NONE
                            || isfloat(ri->cls)) {
                                goto BadEncoding;
                        }
                        L->pins[ri->pin] = i;
                }
        }
        n = read_count(&r, sizeof *L->labels);
        if (!grow(&L->labels, &L->label_capacity, n, sizeof *L->labels)) {
                goto NoMemory;
        }
        L->nlabels = n;
        for (u32 i = 0; i < n; ++i) {
                u32 entry;
                L->labels[i].pos = read_u32(&r);
                entry = read_u32(&r);
                if (entry > 1) {
                        goto BadEncoding;
                }
                L->labels[i].entry = entry;
        }
        n = read_count(&r, sizeof *L->roots);
        for (u32 i = 0; i < n; ++i) {
                u32 index = read_u32(&r);
                if (index >= nholes || holes[index].value == NULL) {
                        goto BadEncoding;
                }
                if (lir_const(L, holes[index].value).kind != LIR_OPERAND_CONST) {
                        goto NoMemory;
                }
        }
        n = read_count(&r, sizeof *L->insts);
        if (!grow(&L->insts, &L->inst_capacity, n, sizeof *L->insts)) {
                goto NoMemory;
        }
        for (u32 i = 0; i < n && r.ok; ++i) {
                u32 nargs;
                in.op = read_u32(&r);
                in.dst = read_u32(&r);
                nargs = read_u32(&r);
                in.span.source = read_u32(&r);
                in.span.start  = read_u32(&r);
                in.span.end    = read_u32(&r);
                if (in.op >= LIR_OP_COUNT || nargs > LIR_MAX_OPERANDS) {
                        goto BadEncoding;
                }
                in.nargs = nargs;
                for (u32 j = 0; j < in.nargs; ++j) {
                        in.args[j] = read_operand(&r, holes, nholes);
                }
                if (in.op == LIR_CALL || in.op == LIR_TAILCALL) {
                        if (!read_sig(&r, &in.sig)) {
                                goto BadEncoding;
                        }
                        in.flags = read_u32(&r);
                        in.tag = read_u32(&r);
                        in.ncall_args = in.sig.nparams;
                        in.call_args = calloc(in.ncall_args, sizeof *in.call_args);
                        if (in.ncall_args != 0 && in.call_args == NULL) {
                                goto NoMemory;
                        }
                        for (u32 j = 0; j < in.ncall_args; ++j) {
                                in.call_args[j] = read_operand(&r, holes, nholes);
                        }
                } else if (in.op == LIR_POLL && version >= 2) {
                        in.flags = read_u32(&r);
                        in.tag = read_u32(&r);
                } else if (in.op == LIR_ENTRY && version >= 2) {
                        in.tag = read_u32(&r);
                } else if (in.op == LIR_SWITCH) {
                        in.ntargets = read_count(&r, sizeof *in.targets);
                        in.targets = calloc(in.ntargets, sizeof *in.targets);
                        if (in.ntargets != 0 && in.targets == NULL) {
                                goto NoMemory;
                        }
                        for (u32 j = 0; j < in.ntargets; ++j) {
                                in.targets[j] = read_u32(&r);
                        }
                } else if (in.op == LIR_RAW && !read_raw(&r, &in.raw)) {
                        goto BadEncoding;
                }
                L->insts[L->ninsts++] = in;
                in = (LirInst) { .dst = LIR_NONE };
        }
        if (!r.ok || r.pos != r.size || !lir_validate(L, err)) {
                if (r.ok && r.pos == r.size) {
                        goto Error;
                }
                goto BadEncoding;
        }
        for (u32 i = 0; i < L->ninsts; ++i) {
                LirInst *inst = &L->insts[i];
                bool changed = false;
                if ((inst->op == LIR_CALL || inst->op == LIR_TAILCALL)
                    && inst->args[0].kind == LIR_HOLE_CALLEE && inst->args[0].index < nholes) {
                        LirBinding const *b = &holes[inst->args[0].index];
                        if (b->signature != NULL && !sig_equal(&inst->sig, b->signature)) {
                                fail(err, LIR_ERROR_SIGNATURE, i, inst->span, "callee hole signature does not match call");
                                goto Error;
                        }
                        inst->flags |= b->flags;
                }
                for (u32 j = 0; j < inst->nargs; ++j) {
                        changed = changed || hole_operand(inst->args[j]);
                        if (!fill_operand(L, &inst->args[j], holes, nholes)) {
                                fail(err, LIR_ERROR_ENCODING, i, inst->span, "missing or mismatched hole binding");
                                goto Error;
                        }
                }
                for (u32 j = 0; j < inst->ncall_args; ++j) {
                        changed = changed || hole_operand(inst->call_args[j]);
                        if (!fill_operand(L, &inst->call_args[j], holes, nholes)) {
                                fail(err, LIR_ERROR_ENCODING, i, inst->span, "missing or mismatched hole binding");
                                goto Error;
                        }
                }
                if (changed && !inst_valid(L, i, err)) {
                        goto Error;
                }
        }
        if (!resolve_mode(L, err)) {
                goto Error;
        }
        return L;
NoMemory:
        fail(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory decoding LIR");
        goto Error;
BadEncoding:
        fail(err, LIR_ERROR_ENCODING, LIR_NONE, (LirSpan) {0}, "invalid or truncated LIR encoding");
Error:
        free(name);
        free((void *)sig.params);
        inst_free(&in);
        lir_free(L);
        return NULL;
}

typedef struct lir_entry_build {
        Lir *L;
        LirRuntime const *rt;
        LirReg ty;
        LirReg out;
        LirReg frame;
} LirEntryBuild;

static LirReg
entry_load(Lir *L, LirOp op, LirReg base, i32 disp, LirClass cls)
{
        LirReg r = lir_reg(L, cls);
        LirOpnd arg = lir_m(base, LIR_NONE, 1, disp);
        lir_emit_to(L, op, r, &arg, 1);
        return r;
}

static void
entry_store(Lir *L, LirOp op, LirReg base, i32 disp, LirOpnd value)
{
        LirOpnd args[] = { lir_m(base, LIR_NONE, 1, disp), value };
        lir_emit_to(L, op, LIR_NONE, args, countof(args));
}

static LirReg
entry_call(Lir *L, void *target, LirType ret, LirType const *types,
           LirOpnd *args, u32 n, u32 flags)
{
        LirReg r = ret == LIR_VOID ? LIR_NONE : lir_reg(L, lir_type_class(ret));
        LirInst in = {
                .op = LIR_CALL, .dst = r, .args = { lir_i((uptr)target) }, .nargs = 1,
                .sig = { .ret = ret, .params = types, .nparams = n, .nfixed = n },
                .flags = flags, .call_args = args, .ncall_args = n
        };
        lir_emit(L, &in);
        return r;
}

static void
entry_branch(Lir *L, LirCC cc, LirOpnd a, LirOpnd b, LirLabel label)
{
        LirOpnd args[] = { lir_cc(cc), a, b, lir_l(label) };
        lir_emit_to(L, LIR_BR, LIR_NONE, args, countof(args));
}

static void
entry_jump(Lir *L, LirLabel label)
{
        LirOpnd arg = lir_l(label);
        lir_emit_to(L, LIR_JMP, LIR_NONE, &arg, 1);
}

static void
entry_move(Lir *L, LirReg d, LirReg a)
{
        LirOpnd arg = lir_r(a);
        lir_emit_to(L, LIR_MOV, d, &arg, 1);
}

static void
entry_type_error(LirEntryBuild *e, u32 i, LirType type, LirReg value)
{
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_I32, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(e->ty), lir_i(i), lir_i(type), lir_r(value) };
        entry_call(e->L, (void *)e->rt->arg_type_error, LIR_VOID,
                   types, args, countof(args), LIR_MAY_THROW | LIR_NORETURN);
}

static LirReg
entry_pointer(LirEntryBuild *e, LirReg value, LirReg tag, u32 i)
{
        Lir *L = e->L;
        LirReg r = lir_reg(L, LIR_PTR);
        LirLabel fast = lir_label(L);
        LirLabel blob = lir_label(L);
        LirLabel done = lir_label(L);
        entry_branch(L, LIR_EQ, lir_r(tag), lir_i(VALUE_PTR), fast);
        entry_branch(L, LIR_EQ, lir_r(tag), lir_i(VALUE_BLOB), blob);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(e->ty), lir_r(e->frame), lir_i(i) };
        LirReg slow = entry_call(L, (void *)e->rt->ptr_from, LIR_TYPE_PTR,
                                types, args, countof(args), LIR_MAY_GC | LIR_MAY_THROW);
        entry_move(L, r, slow);
        entry_jump(L, done);
        lir_bind(L, fast);
        LirReg p = entry_load(L, LIR_LD_I64, value, offsetof(Value, ptr), LIR_PTR);
        entry_move(L, r, p);
        entry_jump(L, done);
        lir_bind(L, blob);
        LirReg b = entry_load(L, LIR_LD_I64, value, offsetof(Value, blob), LIR_PTR);
        LirReg data = entry_load(L, LIR_LD_I64, b, offsetof(Blob, items), LIR_PTR);
        entry_move(L, r, data);
        lir_bind(L, done);
        return r;
}

static LirReg
entry_float(LirEntryBuild *e, LirReg value, LirReg tag, LirType type, LirLabel error)
{
        Lir *L = e->L;
        LirReg r = lir_reg(L, lir_type_class(type));
        LirLabel real = lir_label(L);
        LirLabel done = lir_label(L);
        entry_branch(L, LIR_EQ, lir_r(tag), lir_i(VALUE_REAL), real);
        entry_branch(L, LIR_NE, lir_r(tag), lir_i(VALUE_INTEGER), error);
        LirReg z = entry_load(L, LIR_LD_I64, value, offsetof(Value, z), LIR_I64);
        LirOpnd arg = lir_r(z);
        lir_emit_to(L, LIR_I2F, r, &arg, 1);
        entry_jump(L, done);
        lir_bind(L, real);
        LirReg f = entry_load(L, LIR_LD_F64, value, offsetof(Value, real), LIR_F64);
        arg = lir_r(f);
        lir_emit_to(L, type == LIR_TYPE_F32 ? LIR_FTRUNC : LIR_MOV, r, &arg, 1);
        lir_bind(L, done);
        return r;
}

static LirReg
entry_arg(LirEntryBuild *e, LirType type, u32 i)
{
        Lir *L = e->L;
        LirReg args = entry_load(L, LIR_LD_I64, e->frame, offsetof(LirEntryFrame, args), LIR_PTR);
        LirReg value = lir_reg(L, LIR_PTR);
        LirOpnd address[] = { lir_r(args), lir_i((u64)i * sizeof (Value)) };
        lir_emit_to(L, LIR_ADD, value, address, countof(address));
        if (type == LIR_TYPE_VAL) {
                return value;
        }
        if (type == LIR_TYPE_REF) {
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
                LirOpnd xs[] = { lir_r(e->ty), lir_r(value), lir_i(i) };
                return entry_call(L, (void *)e->rt->ref_from, LIR_TYPE_REF,
                                  types, xs, countof(xs), LIR_MAY_GC | LIR_MAY_THROW);
        }
        LirReg tag = entry_load(L, LIR_LD_U8, value, offsetof(Value, type), LIR_I64);
        LirOpnd mask[] = { lir_r(tag), lir_i(~VALUE_TAGGED & 255) };
        lir_emit_to(L, LIR_AND, tag, mask, countof(mask));
        if (type == LIR_TYPE_PTR) {
                return entry_pointer(e, value, tag, i);
        }
        LirLabel error = lir_label(L);
        LirLabel done = lir_label(L);
        LirReg r;
        if (type == LIR_TYPE_F32 || type == LIR_TYPE_F64) {
                r = entry_float(e, value, tag, type, error);
        } else {
                bool boolean = type == LIR_TYPE_BOOL;
                entry_branch(L, LIR_NE, lir_r(tag), lir_i(boolean ? VALUE_BOOLEAN : VALUE_INTEGER), error);
                r = entry_load(L, boolean ? LIR_LD_U8 : LIR_LD_I64, value,
                               boolean ? offsetof(Value, boolean) : offsetof(Value, z), LIR_I64);
        }
        entry_jump(L, done);
        lir_bind(L, error);
        entry_type_error(e, i, type, value);
        lir_bind(L, done);
        return r;
}

static void
entry_box(LirEntryBuild *e, LirReg value, LirType type)
{
        Lir *L = e->L;
        if (type == LIR_TYPE_VAL) {
                for (u32 i = 0; i < sizeof (Value); i += 8) {
                        LirReg part = entry_load(L, LIR_LD_I64, value, i, LIR_I64);
                        entry_store(L, LIR_ST64, e->out, i, lir_r(part));
                }
                return;
        }
        for (u32 i = 0; i < sizeof (Value); i += 8) {
                entry_store(L, LIR_ST64, e->out, i, lir_i(0));
        }
        u8 tag = VALUE_INTEGER;
        LirOp op = LIR_ST64;
        u32 off = offsetof(Value, z);
        if (type == LIR_VOID) {
                entry_store(L, LIR_ST8, e->out, offsetof(Value, type), lir_i(VALUE_NIL));
                return;
        }
        if (type == LIR_TYPE_F32 || type == LIR_TYPE_F64) {
                tag = VALUE_REAL;
                op = LIR_ST_F64;
                off = offsetof(Value, real);
                if (type == LIR_TYPE_F32) {
                        LirReg f = lir_reg(L, LIR_F64);
                        LirOpnd arg = lir_r(value);
                        lir_emit_to(L, LIR_FEXT, f, &arg, 1);
                        value = f;
                }
        } else if (type == LIR_TYPE_BOOL) {
                tag = VALUE_BOOLEAN;
                op = LIR_ST8;
                off = offsetof(Value, boolean);
        } else if (type == LIR_TYPE_PTR || type == LIR_TYPE_REF) {
                tag = VALUE_PTR;
                off = offsetof(Value, ptr);
                if (type == LIR_TYPE_REF) {
                        entry_store(L, LIR_ST64, e->out, offsetof(Value, gcptr), lir_r(value));
                }
        }
        entry_store(L, op, e->out, off, lir_r(value));
        entry_store(L, LIR_ST8, e->out, offsetof(Value, type), lir_i(tag));
}

Lir *
lir_build_entry(LirCode *code, LirError *err)
{
        LirRuntime const *rt = lir_runtime();
        LirType params[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirSig sig = { .ret = LIR_VOID, .params = params, .nparams = countof(params), .nfixed = countof(params) };
        Lir *L = NULL;
        LirOpnd *args = NULL;
        bool lean = code->nvslots == 0 && code->mode == LIR_MODE_DETACHED;
        bool pointers = false;
        if (rt == NULL || rt->arity_error == NULL || rt->arg_type_error == NULL
            || rt->reserve == NULL || rt->restore == NULL
            || (code->release && (rt->unlock == NULL || rt->lock == NULL))) {
                fail(err, LIR_ERROR_MODE, LIR_NONE, (LirSpan) {0}, "entry thunk requires a VM runtime");
                return NULL;
        }
        for (u32 i = 0; i < code->sig.nparams; ++i) {
                LirType type = code->sig.params[i];
                if ((type == LIR_TYPE_PTR && rt->ptr_from == NULL)
                    || (type == LIR_TYPE_REF && rt->ref_from == NULL)) {
                        fail(err, LIR_ERROR_MODE, LIR_NONE, (LirSpan) {0}, "entry conversion requires a VM runtime");
                        return NULL;
                }
                pointers = pointers || type == LIR_TYPE_PTR;
        }
        L = lir_new(code->name, &sig, LIR_MODE_ATTACHED, err);
        args = malloc(((usize)code->sig.nparams + 1) * sizeof *args);
        if (L == NULL || args == NULL) {
                goto Error;
        }
        lir_pin_param(L, LIR_PIN_0, 0);
        lir_pin_param(L, LIR_PIN_1, 1);
        LirEntryBuild e = { .L = L, .rt = rt,
                            .ty = lir_pinned(L, LIR_PIN_0),
                            .out = lir_pinned(L, LIR_PIN_1),
                            .frame = lir_reg(L, LIR_PTR) };
        LirLabel error = lir_label(L);
        entry_branch(L, LIR_NE, lir_r(L->params[3]), lir_i(code->sig.nparams), error);
        LirOpnd allocation[] = { lir_i(sizeof (LirEntryFrame)), lir_i(alignof (LirEntryFrame)) };
        lir_emit_to(L, LIR_ALLOCA, e.frame, allocation, countof(allocation));
        entry_store(L, LIR_ST64, e.frame, offsetof(LirEntryFrame, out), lir_r(e.out));
        entry_store(L, LIR_ST64, e.frame, offsetof(LirEntryFrame, args), lir_r(L->params[2]));
        if (lean) {
                entry_store(L, LIR_ST64, e.frame, offsetof(LirEntryFrame, base), lir_i(0));
        } else {
                LirType reserve_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_U32 };
                LirOpnd reserve_args[] = { lir_r(e.ty), lir_r(e.frame), lir_i(code->nvslots) };
                entry_call(L, (void *)rt->reserve, LIR_VOID, reserve_types, reserve_args,
                           countof(reserve_args), LIR_MAY_GC);
        }
        for (u32 pass = 0; pass < 2; ++pass) {
                for (u32 i = 0; i < code->sig.nparams; ++i) {
                        if ((code->sig.params[i] == LIR_TYPE_PTR) == (pass == 0)) {
                                args[i] = lir_r(entry_arg(&e, code->sig.params[i], i));
                        }
                }
        }
        LirType ty_type = LIR_TYPE_PTR;
        LirOpnd ty_arg = lir_r(e.ty);
        if (code->release) {
                entry_call(L, (void *)rt->unlock, LIR_VOID, &ty_type, &ty_arg, 1, 0);
        }
        LirReg result = entry_call(L, code->body, code->sig.ret, code->sig.params, args,
                                  code->sig.nparams, code->mode == LIR_MODE_ATTACHED
                                  ? LIR_MAY_GC | LIR_MAY_THROW : 0);
        if (code->release) {
                entry_call(L, (void *)rt->lock, LIR_VOID, &ty_type, &ty_arg, 1, 0);
        }
        if (!lean) {
                LirType restore_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
                LirOpnd restore_args[] = { lir_r(e.ty), lir_r(e.frame) };
                LirReg out = entry_call(L, (void *)rt->restore, LIR_TYPE_PTR,
                                       restore_types, restore_args, countof(restore_args), 0);
                entry_move(L, e.out, out);
        } else if (pointers) {
                LirReg out = entry_load(L, LIR_LD_I64, e.frame, offsetof(LirEntryFrame, out), LIR_PTR);
                entry_move(L, e.out, out);
        }
        entry_box(&e, result, code->sig.ret);
        lir_emit_to(L, LIR_RET, LIR_NONE, NULL, 0);
        lir_bind(L, error);
        LirType arity_types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_I32 };
        LirOpnd arity_args[] = { lir_r(e.ty), lir_i(code->sig.nparams), lir_r(L->params[3]) };
        entry_call(L, (void *)rt->arity_error, LIR_VOID, arity_types, arity_args,
                   countof(arity_args), LIR_MAY_THROW | LIR_NORETURN);
        free(args);
        if (!lir_validate(L, err)) {
                lir_free(L);
                return NULL;
        }
        return L;
Error:
        free(args);
        lir_free(L);
        if (err != NULL && err->kind == LIR_ERROR_NONE) {
                fail(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory building entry thunk");
        }
        return NULL;
}
