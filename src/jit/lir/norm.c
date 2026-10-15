#include "impl.h"

#define put(L, op, dst, ...) lir_emit_to(                       \
        (L),                                                    \
        (op),                                                   \
        (dst),                                                  \
        (LirOpnd[]) { __VA_ARGS__ },                            \
        countof(((LirOpnd[]) { __VA_ARGS__ }))                  \
)

typedef struct {
        LirReg frame;
        LirReg ctx;
        LirReg slot;
} Callee;

inline static LirOpnd
at(LirReg base, i32 disp)
{
        return lir_m(base, LIR_NONE, 1, disp);
}

static bool
one(Lir *L, LirOp op, LirReg dst, LirOpnd a, LirSpan span)
{
        LirInst in = {
                .op    = op,
                .dst   = dst,
                .args  = { a },
                .nargs = 1,
                .span  = span
        };

        return lir_emit(L, &in);
}

inline static bool
intact(Lir const *L)
{
        return L->error.kind == LE_NONE;
}

static LirClass
classof(Lir const *L, LirOpnd a, LirClass fallback)
{
        switch (a.kind) {
        case LO_REG:      return v__(L->regs, a.reg).cls;
        case LO_REFCONST: return LIR_REF;
        case LO_CONST:
        case LO_VSLOT:    return LIR_PTR;
        default:          return fallback;
        }
}

static bool
imm12(LirInst *in)
{
        LirOpnd *b = &in->args[1];

        if (
                (in->op != LIR_ADD && in->op != LIR_SUB)
             || (b->kind != LO_IMM)
             || (b->imm == INT64_MIN)
        ) {
                return false;
        }

        u64 n = (b->imm < 0) ? -b->imm : b->imm;

        if (
                (n > 4095)
             && (((n & 4095) != 0) || ((n >> 12) > 4095))
        ) {
                return false;
        }

        if (b->imm < 0) {
                in->op = (in->op == LIR_ADD) ? LIR_SUB : LIR_ADD;
                b->imm = n;
        }

        return true;
}

#if defined(__x86_64__)
inline static bool
imm32(LirOpnd a)
{
        return (a.kind == LO_IMM) && (a.imm >= INT32_MIN) && (a.imm <= INT32_MAX);
}

static bool
foldbin(LirInst const *in, LirClass cls)
{
        i64 n = in->args[1].imm;

        if (!imm32(in->args[1]) || in->args[0].kind != LO_REG) {
                return false;
        }

        switch (in->op) {
        case LIR_ADD:
        case LIR_SUB:
        case LIR_AND:
        case LIR_OR:
        case LIR_XOR:
        case LIR_MUL:
                return true;

        case LIR_SHL:
        case LIR_SHR:
        case LIR_SAR:
        case LIR_ROTR:
                return (n >= 0) && (n < ((cls == LIR_I32) ? 32 : 64));

        default:
                return false;
        }
}

static bool
foldcmp(LirInst const *in, bool fp)
{
        return !fp && (in->args[1].kind == LO_REG) && imm32(in->args[2]);
}

static bool
foldst(LirInst const *in)
{
        LirClass cls = lir_type_class(LirOps[in->op].type);
        return imm32(in->args[1]) && cls != LIR_F32 && cls != LIR_F64;
}
#else
static bool
foldbin(LirInst const *in, LirClass cls)
{
        return false;
}

static bool
foldcmp(LirInst const *in, bool fp)
{
        return false;
}

static bool
foldst(LirInst const *in)
{
        return false;
}
#endif

inline static bool
behind(Lir const *L, LirLabel label, u32 pc)
{
        return v__(L->labels, label).pos <= pc;
}

static bool
backedge(Lir const *L, LirInst const *in, u32 pc)
{
        switch (LirOps[in->op].form) {
        case LF_BR:
        case LF_FBR:
        case LF_BRZ:
        case LF_JMP:
        case LF_SWITCH:
                break;

        default:
                return false;
        }

        for (u32 i = 0; i < in->nargs; ++i) {
                if (
                        (in->args[i].kind == LO_LABEL)
                     && behind(L, in->args[i].label, pc)
                ) {
                        return true;
                }
        }

        for (u32 i = 0; i < in->ntargets; ++i) {
                if (behind(L, in->targets[i], pc)) {
                        return true;
                }
        }

        return false;
}

static bool
call(
        Lir *L,
        LirReg dst,
        uptr fn,
        LirType ret,
        LirType const *types,
        LirOpnd *args,
        u32 n,
        u32 flags,
        LirSpan span
)
{
        return lir_emit(L, &(LirInst) {
                .op         = LIR_CALL,
                .dst        = dst,
                .args       = { lir_i(fn) },
                .nargs      = 1,
                .sig        = { .ret = ret, .params = types, .nparams = n, .nfixed = n },
                .call_args  = args,
                .ncall_args = n,
                .flags      = flags,
                .span       = span
        });
}

static bool
materialize(Lir *L, LirOpnd *a, LirClass cls, LirSpan span)
{
        LirOp op;

        switch (a->kind) {
        case LO_REG:      return true;
        case LO_IMM:      op = LIR_LI;  break;
        case LO_FIMM:     op = LIR_FLI; break;
        case LO_CONST:
        case LO_REFCONST:
        case LO_VSLOT:    op = LIR_MOV; break;
        default:          return false;
        }

        LirReg r = lir_reg(L, cls);

        if (!one(L, op, r, *a, span)) {
                return false;
        }

        *a = lir_r(r);

        return true;
}

static bool
promote(Lir *L, LirInst *in)
{
        bool changed = false;

        if (!in->sig.variadic) {
                return true;
        }

        for (u32 i = in->sig.nfixed; i < in->sig.nparams; ++i) {
                LirType *type = (LirType *)&in->sig.params[i];
                LirType  to   = LT_I32;
                LirOp    op;

                switch (*type) {
                case LT_I8:   op = LIR_SEXT8;               break;
                case LT_U8:   op = LIR_ZEXT8;               break;
                case LT_I16:  op = LIR_SEXT16;              break;
                case LT_U16:  op = LIR_ZEXT16;              break;
                case LT_BOOL: op = LIR_SETCC;               break;
                case LT_F32:  op = LIR_FEXT; to = LT_F64;   break;
                default:      continue;
                }

                LirOpnd *arg = &in->call_args[i];
                LirReg   d   = lir_reg(L, lir_type_class(to));
                LirInst  x   = {
                        .op    = op,
                        .dst   = d,
                        .args  = { *arg },
                        .nargs = 1,
                        .span  = in->span
                };

                if (*type == LT_BOOL) {
                        LirReg zero = lir_reg(L, LIR_I64);
                        put(L, LIR_LI, zero, lir_i(0));
                        x.args[0] = lir_cc(LIR_NE);
                        x.args[1] = *arg;
                        x.args[2] = lir_r(zero);
                        x.nargs   = 3;
                }

                if (!lir_emit(L, &x)) {
                        return false;
                }

                *arg    = lir_r(d);
                *type   = to;
                changed = true;
        }

        if (changed && in->args[0].kind == LO_HELPER) {
                in->args[0] = lir_i((uptr)in->args[0].helper->address);
        } else if (changed && in->args[0].kind == LO_CODE) {
                in->args[0] = lir_i((uptr)in->args[0].code->body);
        }

        return true;
}

static bool
reserve(Lir *L, LirInst const *in, Callee *cf, LirError *err)
{
        LirRuntime const *rt = lir_runtime();
        LirOpnd           fn = in->args[0];

        *cf = (Callee) { .frame = LIR_NONE, .ctx = LIR_NONE, .slot = LIR_NONE };

        if (fn.kind != LO_CODE) {
                return true;
        }

        if (
                (in->sig.ret == LT_VAL)
             && ((in->dst != LIR_NONE) || (in->op == LIR_TAILCALL))
        ) {
                cf->slot = lir_vslot(L);
                if (cf->slot == LIR_NONE) {
                        return false;
                }
        }

        if (fn.code->nvslots == 0 || fn.code->interp_state != NULL) {
                return true;
        }

        if (
                (rt == NULL)
             || (rt->current_ty == NULL)
             || (rt->reserve == NULL)
             || (rt->restore == NULL)
        ) {
                return lir_fail(
                        err,
                        LE_MODE,
                        vN(L->insts),
                        in->span,
                        "callee value slots require a VM runtime"
                );
        }

        cf->frame = lir_reg(L, LIR_PTR);
        cf->ctx   = lir_reg(L, LIR_PTR);

        put(
                L,
                LIR_ALLOCA,
                cf->frame,
                lir_i(sizeof (LirEntryFrame)),
                lir_i(alignof (LirEntryFrame))
        );

        LirOpnd zero  = lir_i(0);
        LirOpnd count = lir_i(fn.code->nvslots);

        materialize(L, &zero, LIR_I64, in->span);

        for (u32 i = 0; i < 2; ++i) {
                put(L, LIR_ST64, LIR_NONE, at(cf->frame, i * sizeof (void *)), zero);
        }

        call(L, cf->ctx, (uptr)rt->current_ty, LT_PTR, NULL, NULL, 0, 0, in->span);
        materialize(L, &count, LIR_I64, in->span);

        return call(
                L,
                LIR_NONE,
                (uptr)rt->reserve,
                LT_VOID,
                (LirType[]) { LT_PTR, LT_PTR, LT_U32 },
                (LirOpnd[]) { lir_r(cf->ctx), lir_r(cf->frame), count },
                3,
                LIR_MAY_GC | LIR_MAY_THROW,
                in->span
        );
}

static bool
restore(Lir *L, LirInst const *in, Callee const *cf, LirReg dst, bool tail)
{
        LirReg result = in->dst;

        if (cf->slot != LIR_NONE) {
                for (u32 i = 0; i < sizeof (Value); i += 8) {
                        LirReg r = lir_reg(L, LIR_I64);
                        put(L, LIR_LD_I64, r, at(result, i));
                        put(L, LIR_ST64, LIR_NONE, at(cf->slot, i), lir_r(r));
                }
                result = cf->slot;
        }

        if (cf->frame != LIR_NONE) {
                call(
                        L,
                        LIR_NONE,
                        (uptr)lir_runtime()->restore,
                        LT_PTR,
                        (LirType[]) { LT_PTR, LT_PTR },
                        (LirOpnd[]) { lir_r(cf->ctx), lir_r(cf->frame) },
                        2,
                        0,
                        in->span
                );
        }

        if (tail) {
                LirOpnd value = lir_r(result);
                lir_emit_to(L, LIR_RET, LIR_NONE, &value, result != LIR_NONE);
        } else if (cf->slot != LIR_NONE) {
                put(L, LIR_MOV, dst, lir_r(cf->slot));
        }

        return intact(L);
}

static bool
shape(Lir *L, LirInst *in, u8 *use, LirClass *cls)
{
        LirForm  form = LirOps[in->op].form;
        LirOpnd *a    = in->args;
        LirClass d    = cls[0];

        switch (form) {
        case LF_MOV:
                if (a[0].kind == LO_IMM) {
                        in->op = LIR_LI;
                } else if (a[0].kind == LO_FIMM) {
                        in->op = LIR_FLI;
                }
                break;

        case LF_IBINARY:
        case LF_CHECKED:
                *use   = 0b11;
                cls[0] = classof(L, a[0], d);
                cls[1] = classof(L, a[1], (d == LIR_PTR) ? LIR_I64 : d);
                if (
                        ((form == LF_IBINARY) && foldbin(in, d))
                     || imm12(in)
                ) {
                        *use = 0b01;
                }
                break;

        case LF_IUNARY:
        case LF_I2F:
        case LF_BRZ:
        case LF_SWITCH:
                *use   = 0b1;
                cls[0] = classof(L, a[0], LIR_I64);
                break;

        case LF_F2I:
                *use   = 0b1;
                cls[0] = classof(L, a[0], LIR_F64);
                break;

        case LF_FBINARY:
        case LF_FUNARY:
        case LF_FMA:
                *use = (1 << in->nargs) - 1;
                break;

        case LF_ST:
                *use   = foldst(in) ? 0 : 0b10;
                cls[1] = classof(L, a[1], lir_type_class(LirOps[in->op].type));
                break;

        case LF_SETCC:
        case LF_FSETCC:
        case LF_SELECT:
        case LF_FSELECT:
        case LF_BR:
        case LF_FBR: {
                bool fp = (form == LF_FSETCC) || (form == LF_FSELECT) || (form == LF_FBR);

                *use   = foldcmp(in, fp) ? 0b010 : 0b110;
                cls[1] = classof(L, a[2], classof(L, a[1], fp ? LIR_F64 : LIR_I64));
                cls[2] = cls[1];

                if (form == LF_SELECT || form == LF_FSELECT) {
                        *use |= 0b11000;
                }
                break;
        }

        case LF_RET:
                if (in->nargs != 0) {
                        *use   = 0b1;
                        cls[0] = classof(L, a[0], lir_type_class(L->sig.ret));
                }
                break;

        case LF_CALL:
        case LF_TAILCALL:
                for (u32 i = 0; i < in->ncall_args; ++i) {
                        LirOpnd *arg = &in->call_args[i];
                        LirClass c   = classof(L, *arg, lir_type_class(in->sig.params[i]));
                        if (!materialize(L, arg, c, in->span)) {
                                return false;
                        }
                }
                return promote(L, in);

        case LF_CAS:
        case LF_ATOMIC: {
                LirReg p = lir_reg(L, LIR_PTR);

                if (!one(L, LIR_LEA, p, a[0], in->span)) {
                        return false;
                }

                a[0] = at(p, 0);
                *use = ((1 << in->nargs) - 1) & ~1;
                break;
        }

        case LF_POLL:
                if (in->nargs == 4) {
                        *use   = 0b111;
                        cls[0] = LIR_PTR;
                        cls[1] = LIR_PTR;
                        cls[2] = LIR_PTR;
                }
                break;
        }

        return true;
}

static bool
rewrite(Lir *L, LirInst *src, u32 pc, LirError *err)
{
        LirInst  in  = *src;
        LirClass d   = (in.dst == LIR_NONE) ? LIR_I64 : v__(L->regs, in.dst).cls;
        u8       use = 0;
        LirClass cls[LIR_MAX_OPERANDS];

        if (
                (L->resolved_mode == LIR_MODE_ATTACHED)
             && backedge(L, &in, pc)
        ) {
                LirLabel next = lir_label(L);
                bool     ok   = one(L, LIR_POLL, LIR_NONE, lir_l(next), in.span);
                if (!ok || !lir_bind(L, next)) {
                        return false;
                }
        }

        for (u32 i = 0; i < LIR_MAX_OPERANDS; ++i) {
                cls[i] = d;
        }

        if (!shape(L, &in, &use, cls)) {
                return false;
        }

        for (u32 i = 0; i < in.nargs; ++i) {
                if (
                        ((use >> i) & 1)
                     && !materialize(L, &in.args[i], cls[i], in.span)
                ) {
                        return false;
                }
        }

        Callee cf   = { .frame = LIR_NONE, .ctx = LIR_NONE, .slot = LIR_NONE };
        LirReg dst  = in.dst;
        bool   tail = (in.op == LIR_TAILCALL);

        if (
                ((in.op == LIR_CALL) || tail)
             && !reserve(L, &in, &cf, err)
        ) {
                return false;
        }

        bool framed = (cf.frame != LIR_NONE) || (cf.slot != LIR_NONE);

        if (framed) {
                if (cf.frame != LIR_NONE) {
                        in.flags |= LIR_MAY_GC | LIR_MAY_THROW;
                }
                in.op = LIR_CALL;
                if (tail && in.sig.ret != LT_VOID) {
                        in.dst = lir_reg(L, lir_type_class(in.sig.ret));
                } else if (cf.slot != LIR_NONE) {
                        in.dst = lir_reg(L, LIR_PTR);
                }
        }

        if (!lir_emit_owned(L, &in)) {
                return false;
        }

        *src = (LirInst) {0};

        return !framed || restore(L, &in, &cf, dst, tail);
}

bool
lir_normalize(Ty *ty, Lir *L, LirError *err)
{
        LirInst *old     = vv(L->insts);
        u32      n       = vN(L->insts);
        u32      nlabels = vN(L->labels);
        bool     ok      = true;

        SCRATCH_SAVE();

        u32 *at = smA((n + 1) * sizeof *at);

        v00(L->insts);

        for (u32 pc = 0; ok && pc < n; ++pc) {
                at[pc] = vN(L->insts);
                ok = rewrite(L, &old[pc], pc, err);
        }

        if (ok) {
                at[n] = vN(L->insts);
                for (u32 i = 0; i < nlabels; ++i) {
                        v_(L->labels, i)->pos = at[v__(L->labels, i).pos];
                }
        } else if (err == NULL || err->kind == LE_NONE) {
                lir_fail(
                        err,
                        LE_ENCODING,
                        vN(L->insts),
                        (LirSpan) {0},
                        "could not materialize LIR operand"
                );
        }

        for (u32 i = 0; i < n; ++i) {
                inst_free(&old[i]);
        }

        xmF(old);

        SCRATCH_RESTORE();

        return ok;
}

bool
lir_legalize(
        Ty *ty,
        Lir *L,
        LirTarget const *target,
        LirConstraint **constraints,
        u32 *nconstraints,
        LirError *err
)
{
        *constraints  = NULL;
        *nconstraints = 0;

        if (target == NULL || target->legalize == NULL) {
                return lir_fail(err, LE_TARGET, LIR_NOWHERE, "no native LIR target");
        }

        return lir_normalize(ty, L, err)
            && target->legalize(ty, L, constraints, nconstraints, err);
}
