#include "impl.h"

static u32 const CallFlags = LIR_MAY_GC
                           | LIR_MAY_THROW
                           | LIR_RETURNS_TWICE
                           | LIR_NORETURN
                           | LIR_CALL_SITE
                           | LIR_READS_NO_LOCALS
                           | LIR_WRITES_LOCALS
                           | LIR_FAST_PATH;

static char const *const Why[] = {
        [LE_RETURN]    = "return does not match signature",
        [LE_SIGNATURE] = "call does not match signature or flags",
        [LE_CLASS]     = "%s operand classes do not match"
};

inline static bool
isimm(LirOpnd a)
{
        return (a.kind == LO_IMM) || (a.kind == LO_HOLE_IMM);
}

inline static bool
isfimm(LirOpnd a)
{
        return (a.kind == LO_FIMM) || (a.kind == LO_HOLE_FIMM);
}

inline static bool
ismem(LirOpnd a)
{
        return a.kind == LO_MEM;
}

inline static bool
is32(LirClass cls)
{
        return (cls == LIR_I32) || (cls == LIR_F32);
}

inline static bool
isext(LirOp op)
{
        return (op >= LIR_SEXT8) && (op <= LIR_ZEXT32);
}

inline static bool
positive32(LirOpnd a)
{
        return (a.kind == LO_IMM) && (a.imm > 0) && (a.imm <= INT32_MAX);
}

static LirClass
opclass(Lir const *L, LirOpnd a)
{
        switch (a.kind) {
        case LO_REG:        return rcls(L, a.reg);
        case LO_IMM:
        case LO_HOLE_IMM:   return LIR_I64;
        case LO_FIMM:
        case LO_HOLE_FIMM:  return LIR_F64;
        case LO_REFCONST:   return LIR_REF;
        case LO_CONST:
        case LO_VSLOT:
        case LO_HOLE_PTR:
        case LO_HOLE_CONST: return LIR_PTR;
        default:            return LIR_CLASS_COUNT;
        }
}

static bool
compatible(Lir const *L, LirClass cls, LirOpnd a)
{
        if (isimm(a)) {
                return isint(cls) || (cls == LIR_PTR);
        }

        if (isfimm(a)) {
                return isfloat(cls);
        }

        return opclass(L, a) == cls;
}

static bool
all_compatible(Lir const *L, LirClass cls, LirOpnd const *xs, u32 n)
{
        for (u32 i = 0; i < n; ++i) {
                if (!compatible(L, cls, xs[i])) {
                        return false;
                }
        }

        return true;
}

static bool
type_matches(Lir const *L, LirType type, LirOpnd a)
{
        if ((type >= LT_I8 && type <= LT_U32) || type == LT_BOOL) {
                return isint(opclass(L, a));
        }

        return compatible(L, lir_type_class(type), a);
}

static bool
label_valid(Lir const *L, LirOpnd a)
{
        return (a.kind == LO_LABEL)
            && (a.label < vN(L->labels))
            && (v__(L->labels, a.label).pos <= vN(L->insts));
}

static bool
mem_valid(Lir const *L, LirMem m)
{
        bool index = (m.index == LIR_NONE) || isint(rcls(L, m.index));
        return isptr(rcls(L, m.base)) && index && pow2(m.scale) && (m.scale <= 8);
}

static bool
operand_valid(Lir const *L, LirOpnd a)
{
        switch (a.kind) {
        case LO_REG:         return a.reg < vN(L->regs);
        case LO_MEM:         return mem_valid(L, a.mem);
        case LO_LABEL:       return label_valid(L, a);
        case LO_CC:          return (u32)a.cc < LIR_CC_COUNT;
        case LO_CONST:
        case LO_REFCONST:    return a.index < vN(L->roots);
        case LO_VSLOT:       return a.index < L->nvslots;
        case LO_CODE:        return a.code != NULL;
        case LO_HELPER:      return a.helper != NULL;
        case LO_IMM:
        case LO_FIMM:
        case LO_HOLE_IMM:
        case LO_HOLE_FIMM:
        case LO_HOLE_PTR:
        case LO_HOLE_CONST:
        case LO_HOLE_CALLEE: return true;
        default:             return false;
        }
}

static bool
cmp_valid(Lir const *L, LirOpnd const *a, bool fp)
{
        LirOpnd cc = a[0];
        LirOpnd x  = a[1];
        LirOpnd y  = a[2];

        if (cc.kind != LO_CC || (cc.cc >= LIR_FEQ) != fp) {
                return false;
        }

        LirClass cls  = opclass(L, (x.kind != LO_REG && y.kind == LO_REG) ? y : x);
        bool     kind = fp ? isfloat(cls) : (isint(cls) || isptr(cls));

        return kind && compatible(L, cls, x) && compatible(L, cls, y);
}

static bool
target_valid(Lir const *L, LirInst const *in)
{
        LirOpnd t = in->args[0];

        switch (t.kind) {
        case LO_REG:
                return opclass(L, t) == LIR_PTR;

        case LO_IMM:
        case LO_HOLE_PTR:
        case LO_HOLE_CALLEE:
                return true;

        case LO_HELPER:
                return sig_valid(&t.helper->sig)
                    && sig_equal(&in->sig, &t.helper->sig)
                    && ((in->flags & t.helper->flags) == t.helper->flags);

        case LO_CODE:
                return sig_valid(&t.code->sig)
                    && sig_equal(&in->sig, &t.code->sig)
                    && ((t.code->mode != LIR_MODE_ATTACHED) || (in->flags & LIR_MAY_GC));

        default:
                return false;
        }
}

static bool
result_valid(Lir const *L, LirInst const *in)
{
        if (in->op == LIR_TAILCALL) {
                return (in->dst == LIR_NONE) && (in->sig.ret == L->sig.ret);
        }

        if (in->dst == LIR_NONE) {
                return true;
        }

        return (in->sig.ret != LT_VOID) && type_matches(L, in->sig.ret, lir_r(in->dst));
}

static bool
args_valid(Lir const *L, LirInst const *in)
{
        for (u32 i = 0; i < in->ncall_args; ++i) {
                LirOpnd a = in->call_args[i];
                if (!operand_valid(L, a) || !type_matches(L, in->sig.params[i], a)) {
                        return false;
                }
        }

        return true;
}

static bool
call_valid(Lir const *L, LirInst const *in)
{
        return sig_valid(&in->sig)
            && (in->ncall_args == in->sig.nparams)
            && ((in->flags & ~CallFlags) == 0)
            && target_valid(L, in)
            && result_valid(L, in)
            && args_valid(L, in);
}

static bool
ret_valid(Lir const *L, LirInst const *in)
{
        if (L->sig.ret == LT_VOID) {
                return in->nargs == 0;
        }

        return (in->nargs == 1) && type_matches(L, L->sig.ret, in->args[0]);
}

static bool
arith_valid(Lir const *L, LirInst const *in, LirClass d)
{
        LirClass x = opclass(L, in->args[0]);
        LirClass y = opclass(L, in->args[1]);

        if ((in->op == LIR_ADD || in->op == LIR_SUB) && d == LIR_PTR) {
                return isptr(x) && (y == LIR_I64);
        }

        if (in->op == LIR_SUB && d == LIR_I64 && isptr(x) && isptr(y)) {
                return true;
        }

        return isint(d) && all_compatible(L, d, in->args, 2);
}

static bool
memop_valid(Lir const *L, LirInst const *in, LirOpnd value)
{
        LirType type = LirOps[in->op].type;

        if (!ismem(in->args[0])) {
                return false;
        }

        return (type == LT_I64 && isptr(opclass(L, value)))
            || type_matches(L, type, value);
}

static bool
targets_valid(Lir const *L, LirInst const *in)
{
        for (u32 i = 0; i < in->ntargets; ++i) {
                if (!label_valid(L, lir_l(in->targets[i]))) {
                        return false;
                }
        }

        return true;
}

static bool
bound(Lir const *L, LirRawBinding const *bs, u32 n)
{
        for (u32 i = 0; i < n; ++i) {
                if (bs[i].reg >= vN(L->regs) || bs[i].phys >= LIR_MAX_PHYS) {
                        return false;
                }
        }

        return true;
}

static bool
raw_valid(Lir const *L, LirRaw const *raw)
{
        return (raw->narm64 != 0 || raw->nx64 != 0)
            && bound(L, raw->in, raw->nin)
            && bound(L, raw->out, raw->nout)
            && (((raw->gpr_clobber | raw->fpr_clobber) >> LIR_MAX_PHYS) == 0);
}

static bool
form_valid(Lir const *L, LirInst const *in, u32 pc)
{
        LirOpnd const *a = in->args;
        LirClass       d = (in->dst == LIR_NONE) ? LIR_CLASS_COUNT : rcls(L, in->dst);
        LirClass       x = opclass(L, a[0]);

        switch (LirOps[in->op].form) {
        case LF_MOV:      return compatible(L, d, a[0]);
        case LF_FLI:      return isfloat(d) && isfimm(a[0]);
        case LF_LEA:      return (d == LIR_PTR) && ismem(a[0]);
        case LF_I2F:      return isfloat(d) && isint(x);
        case LF_F2I:      return isint(d) && isfloat(x);
        case LF_FEXT:     return (d == LIR_F64) && (x == LIR_F32);
        case LF_FTRUNC:   return (d == LIR_F32) && (x == LIR_F64);
        case LF_BITCAST:  return (a[0].kind == LO_REG) && (is32(d) == is32(x));
        case LF_SETCC:    return isint(d) && cmp_valid(L, a, false);
        case LF_FSETCC:   return isint(d) && cmp_valid(L, a, true);
        case LF_BR:       return cmp_valid(L, a, false) && label_valid(L, a[3]);
        case LF_FBR:      return cmp_valid(L, a, true) && label_valid(L, a[3]);
        case LF_BRZ:      return (isint(x) || isptr(x)) && label_valid(L, a[1]);
        case LF_JMP:      return label_valid(L, a[0]);
        case LF_RET:      return ret_valid(L, in);
        case LF_CALL:
        case LF_TAILCALL: return call_valid(L, in);
        case LF_FENCE:    return true;
        case LF_RAW:      return raw_valid(L, &in->raw);
        case LF_LD:       return memop_valid(L, in, lir_r(in->dst));
        case LF_ST:
        case LF_RMW:      return memop_valid(L, in, a[1]);

        case LF_LI:
                return (isint(d) || d == LIR_PTR)
                    && (isimm(a[0]) || (d == LIR_PTR && a[0].kind == LO_HOLE_PTR));

        case LF_IBINARY:
                return arith_valid(L, in, d);

        case LF_CHECKED:
                return arith_valid(L, in, d) && label_valid(L, a[2]);

        case LF_IUNARY:
                return isint(d) && (isext(in->op) ? isint(x) : compatible(L, d, a[0]));

        case LF_FBINARY:
        case LF_FUNARY:
        case LF_FMA:
                return isfloat(d) && all_compatible(L, d, a, in->nargs);

        case LF_SELECT:
        case LF_FSELECT:
                return cmp_valid(L, a, in->op == LIR_FSELECT)
                    && compatible(L, d, a[3])
                    && compatible(L, d, a[4]);

        case LF_POLL:
                return label_valid(L, a[in->nargs - 1])
                    && ((in->nargs != 4) || all_compatible(L, LIR_PTR, a, 3));

        case LF_SWITCH:
                return isint(x) && label_valid(L, a[1]) && targets_valid(L, in);

        case LF_CAS:
        case LF_ATOMIC:
                return (isint(d) || d == LIR_PTR)
                    && ismem(a[0])
                    && all_compatible(L, d, a + 1, in->nargs - 1);

        case LF_COPY:
                return ismem(a[0])
                    && ismem(a[1])
                    && (a[0].mem.index == LIR_NONE)
                    && (a[1].mem.index == LIR_NONE);

        case LF_ALLOCA:
                return (d == LIR_PTR)
                    && positive32(a[0])
                    && positive32(a[1])
                    && pow2(a[1].imm);

        case LF_SITE:
                return (a[0].kind == LO_IMM) && (a[0].imm >= 0) && (a[0].imm <= UINT32_MAX);

        case LF_ENTRY:
                return label_valid(L, a[0])
                    && (v__(L->labels, a[0].label).pos == pc)
                    && v__(L->labels, a[0].label).entry;
        }

        return false;
}

static LirErrorKind
mismatch(LirForm form)
{
        switch (form) {
        case LF_RET:      return LE_RETURN;
        case LF_CALL:
        case LF_TAILCALL: return LE_SIGNATURE;
        default:          return LE_CLASS;
        }
}

static bool
arity_valid(LirInst const *in)
{
        switch (in->op) {
        case LIR_RET:  return in->nargs <= 1;
        case LIR_POLL: return (in->nargs == 1) || (in->nargs == 4);
        default:       return in->nargs == LirOps[in->op].argc;
        }
}

static bool
stray_payload(LirInst const *in)
{
        u32 flags = (in->op == LIR_POLL) ? (in->flags & ~LIR_CALL_SITE) : in->flags;

        if (LirOps[in->op].form == LF_LD) {
                flags &= ~LIR_REFRESH;
        }

        bool sig = ((in->ncall_args | in->sig.nparams | in->sig.nfixed) != 0)
                || (in->sig.ret != LT_VOID)
                || in->sig.variadic
                || (flags != 0);

        bool raw = ((in->raw.nin | in->raw.nout | in->raw.narm64 | in->raw.nx64) != 0)
                || ((in->raw.gpr_clobber | in->raw.fpr_clobber) != 0);

        return (!iscall(in) && sig)
            || (in->op != LIR_SWITCH && in->ntargets != 0)
            || (in->op != LIR_RAW && raw);
}

bool
lir_check_inst(Lir const *L, u32 pc, LirError *err)
{
        LirInst const *in = v_(L->insts, pc);

        if ((u32)in->op >= LIR_OP_COUNT || in->nargs > LIR_MAX_OPERANDS) {
                return lir_fail(err, LE_OPERAND, pc, in->span, "invalid instruction");
        }

        LirOpInfo const *info  = &LirOps[in->op];
        bool             wants = (info->signature[0] == 'd');
        bool             has   = (in->dst != LIR_NONE);

#define BAD(kind, ...) lir_fail(err, (kind), pc, in->span, __VA_ARGS__)
        if (!arity_valid(in)) {
                return BAD(LE_OPERAND, "%s has the wrong operand count", info->name);
        }

        if (has && in->dst >= vN(L->regs)) {
                return BAD(LE_OPERAND, "invalid destination register");
        }

        if (has != wants && in->op != LIR_CALL) {
                return BAD(LE_OPERAND, "%s has an invalid destination", info->name);
        }

        for (u32 j = 0; j < in->nargs; ++j) {
                if (!operand_valid(L, in->args[j])) {
                        return BAD(LE_OPERAND, "%s operand %u is invalid", info->name, j);
                }
        }

        if (stray_payload(in)) {
                return BAD(LE_OPERAND, "unexpected instruction payload");
        }

        if (
                (info->form == LF_SWITCH)
             && (in->ntargets == 0 || in->ntargets > LIR_MAX_SWITCH)
        ) {
                return BAD(LE_LABEL, "invalid switch table size");
        }

        if (!form_valid(L, in, pc)) {
                LirErrorKind kind = mismatch(info->form);
                return BAD(kind, Why[kind], info->name);
        }
#undef BAD

        return true;
}

bool
lir_check_labels(Lir const *L, LirError *err)
{
        for (u32 l = 0; l < vN(L->labels); ++l) {
                if (v__(L->labels, l).pos > vN(L->insts)) {
                        return lir_fail(err, LE_LABEL, LIR_NOWHERE, "label %u is unbound", l);
                }
        }

        return true;
}

inline static bool
vmtype(LirType type)
{
        return (type == LT_VAL) || (type == LT_REF);
}

static bool
vmsig(LirSig const *sig)
{
        if (vmtype(sig->ret)) {
                return true;
        }

        for (u32 i = 0; i < sig->nparams; ++i) {
                if (vmtype(sig->params[i])) {
                        return true;
                }
        }

        return false;
}

static bool
attached_operand(LirOpnd const *a)
{
        switch (a->kind) {
        case LO_CONST:
        case LO_REFCONST:
        case LO_VSLOT:
        case LO_HOLE_CONST: return true;
        case LO_CODE:       return a->code->mode == LIR_MODE_ATTACHED;
        default:            return false;
        }
}

static bool
touches_vm(LirInst const *in)
{
        if (in->op == LIR_POLL || (in->flags & LIR_MAY_GC)) {
                return true;
        }

        if (iscall(in) && vmsig(&in->sig)) {
                return true;
        }

        for (u32 j = 0; j < nopnd(in); ++j) {
                if (attached_operand(opnd(in, j))) {
                        return true;
                }
        }

        return false;
}

bool
lir_resolve_mode(Lir *L, LirError *err)
{
        bool detached = (L->mode == LIR_MODE_DETACHED);
        bool attached = (L->nvslots != 0) || vmsig(&L->sig);

        for (u32 r = 0; r < vN(L->regs); ++r) {
                attached = attached || (v__(L->regs, r).cls == LIR_REF);
        }

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (!touches_vm(in)) {
                        continue;
                }
                if (detached) {
                        return lir_fail(
                                err,
                                LE_MODE,
                                pc,
                                in->span,
                                "VM values or safepoints in detached function"
                        );
                }
                attached = true;
        }

        if (attached && detached) {
                return lir_fail(
                        err,
                        LE_MODE,
                        LIR_NOWHERE,
                        "REF registers or value slots in detached function"
                );
        }

        if (L->mode == LIR_MODE_AUTO) {
                L->resolved_mode = attached ? LIR_MODE_ATTACHED : LIR_MODE_DETACHED;
        } else {
                L->resolved_mode = L->mode;
        }

        return true;
}

bool
lir_prepare(Ty *ty, Lir *L, LirError *err)
{
        clear(err);

        if (relay(L, err) || !lir_check_labels(L, err)) {
                return false;
        }

        L->trusted = (getenv("TY_JIT_VALIDATE") == NULL);

        return lir_resolve_mode(L, err);
}

static bool
pin_valid(Lir const *L, u32 r)
{
        LirRegInfo ri = v__(L->regs, r);

        if ((u32)ri.cls >= LIR_CLASS_COUNT) {
                return false;
        }

        return (ri.pin == LIR_NONE)
            || ((ri.pin < LIR_MAX_PINS) && !isfloat(ri.cls) && (L->pins[ri.pin] == r));
}

static bool
shape_valid(Lir const *L, LirError *err)
{
        if (
                !sig_valid(&L->sig)
             || L->sig.variadic
             || ((u32)L->mode > LIR_MODE_ATTACHED)
             || (L->sig.nparams > vN(L->regs))
             || (L->sig.nparams != 0 && L->params == NULL)
        ) {
                return lir_fail(
                        err,
                        LE_SIGNATURE,
                        LIR_NOWHERE,
                        "invalid function signature"
                );
        }

        if (!lir_check_labels(L, err)) {
                return false;
        }

        for (u32 r = 0; r < vN(L->regs); ++r) {
                if (!pin_valid(L, r)) {
                        return lir_fail(
                                err,
                                LE_CLASS,
                                LIR_NOWHERE,
                                "register r%u has invalid class or pin metadata",
                                r
                        );
                }
                if (!param_ok(L, v__(L->regs, r))) {
                        return lir_fail(
                                err,
                                LE_SIGNATURE,
                                LIR_NOWHERE,
                                "register r%u has invalid parameter metadata",
                                r
                        );
                }
        }

        for (u32 i = 0; i < L->sig.nparams; ++i) {
                LirReg r = L->params[i];
                if (r >= vN(L->regs) || v__(L->regs, r).param != i) {
                        return lir_fail(
                                err,
                                LE_SIGNATURE,
                                LIR_NOWHERE,
                                "invalid parameter register"
                        );
                }
        }

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                if (!lir_check_inst(L, pc, err)) {
                        return false;
                }
        }

        return true;
}

static bool
entry_valid(Lir const *L, LirCFG const *cfg, LirBlock const *b, LirError *err)
{
        for (u32 g = 0; g < cfg->nglobals; ++g) {
                LirReg     r      = cfg->globals[g];
                LirRegInfo ri     = v__(L->regs, r);
                bool       pinned = (ri.pin != LIR_NONE);
                bool       seeded = pinned || (!b->entry && ri.param != LIR_NONE);

                if (!bhas(b->live_in, g) || seeded) {
                        continue;
                }

                u32     pc   = b->first;
                LirSpan span = (pc < vN(L->insts)) ? v__(L->insts, pc).span : (LirSpan) {0};

                return lir_fail(
                        err,
                        b->entry ? LE_ENTRY : LE_UNDEFINED,
                        pc,
                        span,
                        "register r%u is live into %s",
                        r,
                        b->entry ? "resume entry" : "function before definition"
                );
        }

        return true;
}

static bool
twice_valid(Lir const *L, LirCFG const *cfg, LirBlock const *b, LirError *err)
{
        LirInst const *in = v_(L->insts, b->end - 1);

        if (!(in->flags & LIR_RETURNS_TWICE)) {
                return true;
        }

        for (u32 g = 0; g < cfg->nglobals; ++g) {
                LirReg r = cfg->globals[g];
                if (
                        (r != in->dst)
                     && (v__(L->regs, r).pin == LIR_NONE)
                     && bhas(b->live_out, g)
                ) {
                        return lir_fail(
                                err,
                                LE_RETURNS_TWICE,
                                b->end - 1,
                                in->span,
                                "register r%u is live across RETURNS_TWICE",
                                r
                        );
                }
        }

        return true;
}

static bool
flow_valid(Lir const *L, LirCFG const *cfg, LirError *err)
{
        for (u32 i = 0; i < cfg->nblocks; ++i) {
                LirBlock const *b = &cfg->blocks[i];

                if (!b->reachable) {
                        continue;
                }

                if (b->first == vN(L->insts) && L->sig.ret != LT_VOID) {
                        return lir_fail(
                                err,
                                LE_RETURN,
                                vN(L->insts),
                                (LirSpan) {0},
                                "non-void function can fall off the end"
                        );
                }

                if ((i == 0 || b->entry) && !entry_valid(L, cfg, b, err)) {
                        return false;
                }

                if (b->first != b->end && !twice_valid(L, cfg, b, err)) {
                        return false;
                }
        }

        return true;
}

bool
lir_validate(Ty *ty, Lir *L, LirError *err)
{
        ty = lir_scratch(ty);

        clear(err);

        if (relay(L, err) || !shape_valid(L, err) || !lir_resolve_mode(L, err)) {
                return false;
        }

        LirCFG cfg;
        bool   ok = lir_cfg(ty, L, &cfg, err) && flow_valid(L, &cfg, err);

        return ok;
}
