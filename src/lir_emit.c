#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <regex.h>

#include "ty.h"
#include "lir.h"

static bool
emit_error(LirError *err, LirErrorKind kind, u32 op, LirSpan span, char const *message)
{
        if (err != NULL) {
                *err = (LirError) { .kind = kind, .op = op, .span = span };
                snprintf(err->message, sizeof err->message, "%s", message);
        }
        return false;
}

static LirClass
value_class(Lir const *L, LirOpnd a, LirClass fallback)
{
        if (a.kind == LIR_OPERAND_REG) {
                return L->regs[a.reg].cls;
        }
        if (a.kind == LIR_OPERAND_REFCONST) {
                return LIR_REF;
        }
        if (a.kind == LIR_OPERAND_CONST || a.kind == LIR_OPERAND_VSLOT) {
                return LIR_PTR;
        }
        return fallback;
}

static bool
fold_imm(LirInst *in)
{
        if ((in->op != LIR_ADD && in->op != LIR_SUB)
            || in->args[1].kind != LIR_OPERAND_IMM) {
                return false;
        }
        i64 n = in->args[1].imm;
        if (n == INT64_MIN) {
                return false;
        }
        u64 magnitude = n < 0 ? -n : n;
        if (magnitude > 4095 && ((magnitude & 4095) != 0 || (magnitude >> 12) > 4095)) {
                return false;
        }
        if (n < 0) {
                in->op = in->op == LIR_ADD ? LIR_SUB : LIR_ADD;
                in->args[1].imm = magnitude;
        }
        return true;
}

static bool
backward(Lir const *L, LirInst const *in, u32 pc)
{
        LirForm form = LirOps[in->op].form;
        if (form != LIR_FORM_BR && form != LIR_FORM_FBR && form != LIR_FORM_BRZ
            && form != LIR_FORM_JMP && form != LIR_FORM_SWITCH) {
                return false;
        }
        for (u32 i = 0; i < in->nargs; ++i) {
                if (in->args[i].kind == LIR_OPERAND_LABEL
                    && L->labels[in->args[i].label].pos <= pc) {
                        return true;
                }
        }
        for (u32 i = 0; i < in->ntargets; ++i) {
                if (L->labels[in->targets[i]].pos <= pc) {
                        return true;
                }
        }
        return false;
}

static bool
promote_call(Lir *L, LirInst *in)
{
        bool changed = false;
        if (!in->sig.variadic) {
                return true;
        }
        for (u32 i = in->sig.nfixed; i < in->sig.nparams; ++i) {
                LirType type = in->sig.params[i];
                LirType promoted = LIR_TYPE_I32;
                LirOp op;
                switch (type) {
                case LIR_TYPE_I8:   op = LIR_SEXT8; break;
                case LIR_TYPE_U8:   op = LIR_ZEXT8; break;
                case LIR_TYPE_I16:  op = LIR_SEXT16; break;
                case LIR_TYPE_U16:  op = LIR_ZEXT16; break;
                case LIR_TYPE_BOOL: op = LIR_SETCC; break;
                case LIR_TYPE_F32:  op = LIR_FEXT; promoted = LIR_TYPE_F64; break;
                default: continue;
                }
                LirReg d = lir_reg(L, lir_type_class(promoted));
                LirInst convert = {
                        .op = op, .dst = d, .args = { in->call_args[i] },
                        .nargs = 1, .span = in->span
                };
                if (type == LIR_TYPE_BOOL) {
                        LirReg zero = lir_reg(L, LIR_I64);
                        LirOpnd arg = lir_i(0);
                        if (zero == LIR_NONE || !lir_emit_to(L, LIR_LI, zero, &arg, 1)) {
                                return false;
                        }
                        convert.args[0] = lir_cc(LIR_NE);
                        convert.args[1] = in->call_args[i];
                        convert.args[2] = lir_r(zero);
                        convert.nargs = 3;
                }
                if (d == LIR_NONE || !lir_emit(L, &convert)) {
                        return false;
                }
                in->call_args[i] = lir_r(d);
                ((LirType *)in->sig.params)[i] = promoted;
                changed = true;
        }
        if (changed && in->args[0].kind == LIR_OPERAND_HELPER) {
                in->args[0] = lir_i((uptr)in->args[0].helper->address);
        } else if (changed && in->args[0].kind == LIR_OPERAND_CODE) {
                in->args[0] = lir_i((uptr)in->args[0].code->body);
        }
        return true;
}

static bool
materialize(Lir *L, LirOpnd *a, LirClass cls, LirSpan span)
{
        LirReg r;
        LirOp op;
        if (a->kind == LIR_OPERAND_REG) {
                return true;
        }
        if (a->kind >= LIR_HOLE_IMM && a->kind <= LIR_HOLE_CALLEE) {
                return false;
        }
        if (a->kind != LIR_OPERAND_IMM && a->kind != LIR_OPERAND_FIMM
            && a->kind != LIR_OPERAND_CONST && a->kind != LIR_OPERAND_REFCONST
            && a->kind != LIR_OPERAND_VSLOT) {
                return false;
        }
        op = LIR_MOV;
        if (a->kind == LIR_OPERAND_IMM) {
                op = LIR_LI;
        } else if (a->kind == LIR_OPERAND_FIMM) {
                op = LIR_FLI;
        }
        r = lir_reg(L, cls);
        if (r == LIR_NONE) {
                return false;
        }
        LirInst in = { .op = op, .dst = r, .args = { *a }, .nargs = 1, .span = span };
        if (!lir_emit(L, &in)) {
                return false;
        }
        *a = lir_r(r);
        return true;
}

static bool
call_frame(Lir *L, LirInst *in, LirReg *frame, LirReg *ty, LirReg *slot, LirError *err)
{
        LirRuntime const *rt = lir_runtime();
        LirOpnd target = in->args[0];
        *frame = *ty = *slot = LIR_NONE;
        if (target.kind != LIR_OPERAND_CODE) {
                return true;
        }
        if (in->sig.ret == LIR_TYPE_VAL && (in->dst != LIR_NONE || in->op == LIR_TAILCALL)) {
                *slot = lir_vslot(L);
                if (*slot == LIR_NONE) {
                        return false;
                }
        }
        if (target.code->nvslots == 0 || target.code->interp_state != NULL) {
                return true;
        }
        if (rt == NULL || rt->current_ty == NULL || rt->reserve == NULL || rt->restore == NULL) {
                return emit_error(err, LIR_ERROR_MODE, L->ninsts, in->span, "callee value slots require a VM runtime");
        }
        *frame = lir_reg(L, LIR_PTR);
        *ty = lir_reg(L, LIR_PTR);
        LirOpnd args[] = { lir_i(sizeof (LirEntryFrame)), lir_i(alignof (LirEntryFrame)) };
        if (*frame == LIR_NONE || *ty == LIR_NONE
            || !lir_emit_to(L, LIR_ALLOCA, *frame, args, countof(args))) {
                return false;
        }
        LirOpnd zero = lir_i(0);
        if (!materialize(L, &zero, LIR_I64, in->span)) {
                return false;
        }
        for (u32 i = 0; i < 2; ++i) {
                LirOpnd store[] = { lir_m(*frame, LIR_NONE, 1, i * sizeof (void *)), zero };
                if (!lir_emit_to(L, LIR_ST64, LIR_NONE, store, countof(store))) {
                        return false;
                }
        }
        LirInst context = { .op = LIR_CALL, .dst = *ty, .nargs = 1,
                            .args = { lir_i((uptr)rt->current_ty) },
                            .sig = { .ret = LIR_TYPE_PTR }, .span = in->span };
        if (!lir_emit(L, &context)) {
                return false;
        }
        LirOpnd count = lir_i(target.code->nvslots);
        if (!materialize(L, &count, LIR_I64, in->span)) {
                return false;
        }
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_U32 };
        LirOpnd reserve_args[] = { lir_r(*ty), lir_r(*frame), count };
        LirInst reserve = { .op = LIR_CALL, .dst = LIR_NONE, .nargs = 1,
                            .args = { lir_i((uptr)rt->reserve) }, .span = in->span,
                            .sig = { .ret = LIR_VOID, .params = types, .nparams = 3, .nfixed = 3 },
                            .call_args = reserve_args, .ncall_args = 3,
                            .flags = LIR_MAY_GC | LIR_MAY_THROW };
        return lir_emit(L, &reserve);
}

static bool
restore_call_frame(Lir *L, LirInst const *in, LirReg frame, LirReg ty,
                   LirReg slot, LirReg dst, bool tail)
{
        LirReg result = in->dst;
        if (slot != LIR_NONE) {
                for (u32 i = 0; i < sizeof (Value); i += 8) {
                        LirReg r = lir_reg(L, LIR_I64);
                        LirOpnd mem = lir_m(result, LIR_NONE, 1, i);
                        LirOpnd store[] = { lir_m(slot, LIR_NONE, 1, i), lir_r(r) };
                        if (r == LIR_NONE || !lir_emit_to(L, LIR_LD_I64, r, &mem, 1)
                            || !lir_emit_to(L, LIR_ST64, LIR_NONE, store, countof(store))) {
                                return false;
                        }
                }
                result = slot;
        }
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(ty), lir_r(frame) };
        LirInst restore = { .op = LIR_CALL, .dst = LIR_NONE, .nargs = 1,
                            .args = { lir_i(frame == LIR_NONE ? 0 : (uptr)lir_runtime()->restore) }, .span = in->span,
                            .sig = { .ret = LIR_TYPE_PTR, .params = types, .nparams = 2, .nfixed = 2 },
                            .call_args = args, .ncall_args = 2 };
        if (frame != LIR_NONE && !lir_emit(L, &restore)) {
                return false;
        }
        if (tail) {
                LirOpnd value = lir_r(result);
                return lir_emit_to(L, LIR_RET, LIR_NONE, &value, result == LIR_NONE ? 0 : 1);
        }
        if (slot != LIR_NONE) {
                LirOpnd value = lir_r(slot);
                return lir_emit_to(L, LIR_MOV, dst, &value, 1);
        }
        return true;
}

bool
lir_normalize(Lir *L, LirError *err)
{
        LirInst *old = L->insts;
        u32 nold = L->ninsts;
        u32 nlabels = L->nlabels;
        u32 *positions = calloc((usize)nold + 1, sizeof *positions);
        bool ok = false;
        if (positions == NULL) {
                return emit_error(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory legalizing LIR");
        }
        L->insts = NULL;
        L->ninsts = 0;
        L->inst_capacity = 0;
        for (u32 pc = 0; pc < nold; ++pc) {
                LirInst in = old[pc];
                LirForm form = LirOps[in.op].form;
                LirClass d = in.dst == LIR_NONE ? LIR_I64 : L->regs[in.dst].cls;
                LirClass classes[LIR_MAX_OPERANDS];
                bool use[LIR_MAX_OPERANDS] = {0};
                positions[pc] = L->ninsts;
                if (L->resolved_mode == LIR_MODE_ATTACHED && backward(L, &in, pc)) {
                        LirLabel next = lir_label(L);
                        LirInst poll = {
                                .op = LIR_POLL, .dst = LIR_NONE,
                                .args = { lir_l(next) }, .nargs = 1, .span = in.span
                        };
                        if (next == LIR_NONE || !lir_emit(L, &poll) || !lir_bind(L, next)) {
                                goto Error;
                        }
                }
                for (u32 i = 0; i < LIR_MAX_OPERANDS; ++i) {
                        classes[i] = d;
                }
                switch (form) {
                case LIR_FORM_MOV:
                        if (in.args[0].kind == LIR_OPERAND_IMM) {
                                in.op = LIR_LI;
                        } else if (in.args[0].kind == LIR_OPERAND_FIMM) {
                                in.op = LIR_FLI;
                        }
                        break;
                case LIR_FORM_IBINARY:
                case LIR_FORM_CHECKED:
                        use[0] = use[1] = true;
                        classes[0] = value_class(L, in.args[0], d);
                        classes[1] = value_class(L, in.args[1], d == LIR_PTR ? LIR_I64 : d);
                        if (fold_imm(&in)) {
                                use[1] = false;
                        }
                        break;
                case LIR_FORM_IUNARY:
                        use[0] = true;
                        classes[0] = value_class(L, in.args[0], LIR_I64);
                        break;
                case LIR_FORM_FBINARY:
                case LIR_FORM_FUNARY:
                case LIR_FORM_FMA:
                        for (u32 i = 0; i < in.nargs; ++i) {
                                use[i] = true;
                        }
                        break;
                case LIR_FORM_I2F:
                        use[0] = true;
                        classes[0] = value_class(L, in.args[0], LIR_I64);
                        break;
                case LIR_FORM_F2I:
                        use[0] = true;
                        classes[0] = value_class(L, in.args[0], LIR_F64);
                        break;
                case LIR_FORM_FEXT:
                case LIR_FORM_FTRUNC:
                case LIR_FORM_BITCAST:
                        break;
                case LIR_FORM_ST:
                        use[1] = true;
                        classes[1] = value_class(L, in.args[1], lir_type_class(LirOps[in.op].type));
                        break;
                case LIR_FORM_SETCC:
                case LIR_FORM_FSETCC:
                case LIR_FORM_SELECT:
                case LIR_FORM_FSELECT:
                case LIR_FORM_BR:
                case LIR_FORM_FBR: {
                        bool f = form == LIR_FORM_FSETCC || form == LIR_FORM_FSELECT || form == LIR_FORM_FBR;
                        LirClass cls = value_class(L, in.args[1], f ? LIR_F64 : LIR_I64);
                        cls = value_class(L, in.args[2], cls);
                        use[1] = use[2] = true;
                        classes[1] = classes[2] = cls;
                        if (form == LIR_FORM_SELECT || form == LIR_FORM_FSELECT) {
                                use[3] = use[4] = true;
                        }
                        break;
                }
                case LIR_FORM_BRZ:
                case LIR_FORM_SWITCH:
                        use[0] = true;
                        classes[0] = value_class(L, in.args[0], LIR_I64);
                        break;
                case LIR_FORM_RET:
                        if (in.nargs != 0) {
                                use[0] = true;
                                classes[0] = value_class(L, in.args[0], lir_type_class(L->sig.ret));
                        }
                        break;
                case LIR_FORM_CALL:
                case LIR_FORM_TAILCALL:
                        for (u32 i = 0; i < in.ncall_args; ++i) {
                                LirClass cls = value_class(L, in.call_args[i], lir_type_class(in.sig.params[i]));
                                if (!materialize(L, &in.call_args[i], cls, in.span)) {
                                        goto Error;
                                }
                        }
                        if (!promote_call(L, &in)) {
                                goto Error;
                        }
                        break;
                case LIR_FORM_CAS:
                case LIR_FORM_ATOMIC: {
                        LirReg address = lir_reg(L, LIR_PTR);
                        LirInst lea = { .op = LIR_LEA, .dst = address,
                                        .args = { in.args[0] }, .nargs = 1, .span = in.span };
                        if (address == LIR_NONE || !lir_emit(L, &lea)) {
                                goto Error;
                        }
                        in.args[0] = lir_m(address, LIR_NONE, 1, 0);
                        for (u32 i = 1; i < in.nargs; ++i) {
                                use[i] = true;
                        }
                        break;
                }
                case LIR_FORM_POLL:
                        if (in.nargs == 4) {
                                for (u32 i = 0; i < 3; ++i) {
                                        use[i] = true;
                                        classes[i] = LIR_PTR;
                                }
                        }
                        break;
                default:
                        break;
                }
                for (u32 i = 0; i < in.nargs; ++i) {
                        if (use[i] && !materialize(L, &in.args[i], classes[i], in.span)) {
                                goto Error;
                        }
                }
                LirReg frame = LIR_NONE;
                LirReg ty = LIR_NONE;
                LirReg slot = LIR_NONE;
                LirReg dst = in.dst;
                bool tail = in.op == LIR_TAILCALL;
                if ((in.op == LIR_CALL || tail) && !call_frame(L, &in, &frame, &ty, &slot, err)) {
                        goto Error;
                }
                if (frame != LIR_NONE || slot != LIR_NONE) {
                        if (frame != LIR_NONE) {
                                in.flags |= LIR_MAY_GC | LIR_MAY_THROW;
                        }
                        in.op = LIR_CALL;
                        if (tail && in.sig.ret != LIR_VOID) {
                                in.dst = lir_reg(L, lir_type_class(in.sig.ret));
                        } else if (slot != LIR_NONE) {
                                in.dst = lir_reg(L, LIR_PTR);
                        }
                }
                if (!lir_emit(L, &in)) {
                        goto Error;
                }
                if ((frame != LIR_NONE || slot != LIR_NONE)
                    && !restore_call_frame(L, &in, frame, ty, slot, dst, tail)) {
                        goto Error;
                }
        }
        positions[nold] = L->ninsts;
        for (u32 i = 0; i < nlabels; ++i) {
                L->labels[i].pos = positions[L->labels[i].pos];
        }
        ok = true;
        goto End;
Error:
        if (err == NULL || err->kind == LIR_ERROR_NONE) {
                emit_error(err, LIR_ERROR_ENCODING, L->ninsts, (LirSpan) {0}, "could not materialize LIR operand");
        }
End:
        for (u32 i = 0; i < nold; ++i) {
                free((void *)old[i].sig.params);
                free(old[i].call_args);
                free(old[i].targets);
                free((void *)old[i].raw.arm64);
                free((void *)old[i].raw.x64);
                free((void *)old[i].raw.in);
                free((void *)old[i].raw.out);
        }
        free(old);
        free(positions);
        return ok;
}

#if defined(__aarch64__) || defined(__x86_64__)
#define DASM_FDEF static
#define DASM_CHECKS
#include "../dynasm/dasm_proto.h"
#if defined(__aarch64__)
#include "../dynasm/dasm_arm64.h"
#include "lir_arm64.h"
enum { LIR_TMP0 = 16, LIR_TMP1 = 17, LIR_FRAME = 29, LIR_TAIL_BASE = 9, LIR_TAIL_COPY = 10 };
#else
#define DASM_ALIGNED_WRITES
#include "../dynasm/dasm_x86.h"
#include "lir_x64.h"
enum { LIR_TMP0 = 10, LIR_TMP1 = 11, LIR_FRAME = 5, LIR_TAIL_BASE = 11, LIR_TAIL_COPY = 0 };
#endif

typedef struct lir_arg_location {
        u8 phys;
        bool fpr;
        u32 stack;
        LirType type;
} LirArgLocation;

typedef struct lir_native_context {
        dasm_State *dasm;
        Lir const *L;
        LirAlloc const *alloc;
        LirCode *code;
        LirTarget const *target;
        LirError *err;
        u32 outgoing;
        u32 incoming;
        u32 save_gp;
        u32 save_fp;
        u32 params;
        u32 origin;
        u32 pc_slot;
        u32 result;
        u32 ty_slot;
        u32 top_slot;
        u32 stack_base;
        u32 stack_end;
        bool context;
        bool islands;
        u32 frame;
        u32 epilogue;
        u32 thunk;
        u32 literals;
        u32 sites;
        u32 rebased;
        LirArgLocation *arguments;
        u32 *pointers;
        u32 npointers;
        u32 *phase_at;
        u32 *phase_next;
        u32 *constraint_at;
        u32 *constraint_next;
} LirEmitContext;

static bool
native_emit(Lir const *L, LirAlloc const *alloc, LirCode *code, LirError *err);

static void
native_save_registers(LirEmitContext *c, bool write);

#if defined(__aarch64__)
static bool
native_legalize(Lir *L, LirConstraint **out, u32 *nout, LirError *err)
{
        u32 capacity = L->ninsts * 5 + 1;
        LirConstraint *constraints = calloc(capacity, sizeof *constraints);
        u32 n = 0;
        if (constraints == NULL) {
                return emit_error(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "out of memory legalizing arm64");
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (in->op == LIR_POPCNT) {
                        constraints[n++] = (LirConstraint) {
                                .op = pc, .reg = LIR_NONE, .phys = 31,
                                .output = true, .fpr = true, .tied = LIR_NONE
                        };
                }
                if (in->op == LIR_CAS || in->op == LIR_XADD || in->op == LIR_XCHG) {
                        constraints[n++] = (LirConstraint) {
                                .op = pc, .reg = in->args[0].mem.base, .phys = LIR_TMP0, .tied = LIR_NONE
                        };
                        constraints[n++] = (LirConstraint) {
                                .op = pc, .reg = in->args[1].reg, .phys = 14, .tied = LIR_NONE
                        };
                        constraints[n++] = (LirConstraint) {
                                .op = pc, .reg = in->dst, .phys = 13, .output = true, .tied = LIR_NONE
                        };
                        constraints[n++] = (LirConstraint) {
                                .op = pc, .reg = LIR_NONE, .phys = 15, .output = true, .tied = LIR_NONE
                        };
                        if (in->op == LIR_CAS) {
                                constraints[n++] = (LirConstraint) {
                                        .op = pc, .reg = in->args[2].reg, .phys = 12, .tied = LIR_NONE
                                };
                        }
                }
        }
        *out = constraints;
        *nout = n;
        return true;
}

static LirTarget const NativeTarget = {
        .arch = LIR_ARCH_ARM64,
#ifdef __APPLE__
        .abi = LIR_ABI_APPLE_ARM64,
#else
        .abi = LIR_ABI_AAPCS64,
#endif
        .name = "arm64",
        .gpr = { .available = 0x1ff8ffff, .callee_saved = 0x1ff80000,
                 .args = {0, 1, 2, 3, 4, 5, 6, 7}, .nargs = 8, .ret = 0,
                 .scratch = {LIR_TMP0, LIR_TMP1}, .nscratch = 2 },
        .fpr = { .available = UINT32_MAX, .callee_saved = 0xff00,
                 .args = {0, 1, 2, 3, 4, 5, 6, 7}, .nargs = 8, .ret = 0 },
        .pins = {19, 20, 21, 22, 23, 24, 25, 26}, .npins = 8, .stack_align = 16,
        .legalize = native_legalize, .emit = native_emit
};

#else
#include "lir_x64_target.h"
#endif

static bool
native_fp(LirClass cls)
{
        return cls == LIR_F32 || cls == LIR_F64;
}

static u32
arg_locations(LirTarget const *target, LirSig const *sig, LirArgLocation *args)
{
        u32 gp = 0;
        u32 fr = 0;
        u32 stack = 0;
        for (u32 i = 0; i < sig->nparams; ++i) {
                LirType type = sig->params[i];
                bool f = type == LIR_TYPE_F32 || type == LIR_TYPE_F64;
                u32 reg = f ? fr : gp;
                LirRegPool const *pool = f ? &target->fpr : &target->gpr;
                bool anonymous = sig->variadic && i >= sig->nfixed;
                bool memory = reg >= pool->nargs
                           || (target->abi == LIR_ABI_APPLE_ARM64 && anonymous);
                args[i] = (LirArgLocation) { .phys = LIR_PHYS_NONE, .fpr = f,
                                            .stack = LIR_NONE, .type = type };
                if (!memory) {
                        args[i].phys = pool->args[reg];
                        if (f) {
                                ++fr;
                        } else {
                                ++gp;
                        }
                } else {
                        u32 size = type == LIR_TYPE_VAL ? 8 : lir_type_size(type);
                        u32 align = size;
                        if (target->abi != LIR_ABI_APPLE_ARM64 || anonymous) {
                                align = 8;
                                size = 8;
                        }
                        stack = (stack + align - 1) & ~(align - 1);
                        args[i].stack = stack;
                        stack += size;
                }
        }
        return (stack + 15) & ~(u32)15;
}

static u8
physical(LirEmitContext const *c, LirReg r, u32 pc, bool output)
{
        for (u32 i = c->constraint_at[pc]; i != LIR_NONE; i = c->constraint_next[i]) {
                LirConstraint const *constraint = &c->alloc->constraints[i];
                if (constraint->reg == r && constraint->output == output
                    && constraint->phys != LIR_PHYS_NONE) {
                        return constraint->phys;
                }
        }
        return c->alloc->intervals[r].phys;
}

static void
native_frame_move(LirEmitContext *c, LirMove const *m)
{
        dasm_State **Dst = &c->dasm;
        bool f = native_fp(m->cls);
        u32 size = m->cls == LIR_I32 || m->cls == LIR_F32 ? 4 : 8;
        if (m->from_slot != LIR_NONE) {
                native_memory(Dst, false, m->to_phys, LIR_FRAME, c->outgoing + m->from_slot,
                           size, false, f && !m->to_gpr);
        } else if (m->to_slot != LIR_NONE) {
                native_memory(Dst, true, m->from_phys, LIR_FRAME, c->outgoing + m->to_slot,
                           size, false, f && !m->from_gpr);
        } else {
                native_mov(Dst, m->to_phys, m->from_phys, m->cls, m->from_gpr, m->to_gpr);
        }
}

static bool
native_root_move(LirEmitContext *c, LirMove const *m)
{
        dasm_State **Dst = &c->dasm;
        native_memory(Dst, false, LIR_TMP1, LIR_FRAME, c->ty_slot, 8, false, false);
        native_vm_slots(Dst, LIR_TMP0, LIR_TMP1, c->top_slot);
        native_addr(Dst, LIR_TMP0, LIR_TMP0, ((i64)m->to_slot - c->code->nvslots) * sizeof (Value));
        u8 source = m->from_phys;
        if (m->from_slot != LIR_NONE) {
                native_memory(Dst, false, LIR_TMP1, LIR_FRAME, c->outgoing + m->from_slot, 8, false, false);
                source = LIR_TMP1;
        }
        native_zero_store(Dst, LIR_TMP0);
        native_memory(Dst, true, source, LIR_TMP0, offsetof(Value, ptr), 8, false, false);
        native_memory(Dst, true, source, LIR_TMP0, offsetof(Value, gcptr), 8, false, false);
        native_li(Dst, LIR_TMP1, (uptr)&LirRefRoot);
        native_memory(Dst, true, LIR_TMP1, LIR_TMP0, offsetof(Value, extra), 8, false, false);
        native_li(Dst, LIR_TMP1, VALUE_PTR);
        native_memory(Dst, true, LIR_TMP1, LIR_TMP0, offsetof(Value, type), 1, false, false);
        return true;
}

static bool
native_phase(LirEmitContext *c, u32 pc, LirMovePhase phase)
{
        LirMove *moves;
        LirMove *ordered;
        u32 n = 0;
        u32 count;
        u32 first = c->phase_at[2 * pc + phase];
        for (u32 i = first; i != LIR_NONE; i = c->phase_next[i]) {
                ++n;
        }
        if (n == 0) {
                return true;
        }
        moves = malloc(n * sizeof *moves);
        if (moves == NULL) {
                return false;
        }
        n = 0;
        for (u32 i = first; i != LIR_NONE; i = c->phase_next[i]) {
                LirMove const *m = &c->alloc->moves[i];
                if (m->kind == LIR_MOVE_ROOT) {
                        native_root_move(c, m);
                        continue;
                }
                moves[n++] = *m;
        }
        bool ok = lir_parallel_moves(moves, n, &c->target->gpr, &ordered, &count, c->err);
        free(moves);
        if (!ok) {
                return false;
        }
        for (u32 i = 0; i < count; ++i) {
                native_frame_move(c, &ordered[i]);
        }
        free(ordered);
        return true;
}

static void
native_home_to(LirEmitContext *c, LirReg r, u8 dest, LirType type)
{
        LirInterval const *i = &c->alloc->intervals[r];
        LirClass cls = c->L->regs[r].cls;
        if (i->spilled) {
                native_memory(&c->dasm, false, dest, LIR_FRAME, c->outgoing + i->spill,
                           cls == LIR_F32 || cls == LIR_I32 ? 4 : 8, false, native_fp(cls));
        } else {
                native_mov(&c->dasm, dest, i->phys, cls, false, false);
        }
        if (!native_fp(cls)) {
                native_narrow(&c->dasm, dest, type);
        }
}

static bool
native_arguments(LirEmitContext *c, LirInst const *in)
{
        LirArgLocation *args = malloc(((usize)in->ncall_args + 1) * sizeof *args);
        LirMove *moves = malloc(((usize)in->ncall_args + 1) * sizeof *moves);
        LirMove *ordered = NULL;
        u32 count = 0;
        u32 n;
        bool ok = false;
        if (args == NULL || moves == NULL) {
                goto End;
        }
        arg_locations(c->target, &in->sig, args);
        for (u32 p = 0; p < in->ncall_args; ++p) {
                LirReg r = in->call_args[p].reg;
                LirInterval const *i = &c->alloc->intervals[r];
                LirClass cls = c->L->regs[r].cls;
                if (args[p].phys == LIR_PHYS_NONE) {
                        u8 source = i->phys;
                        if (i->spilled) {
                                source = LIR_TMP0;
                                if (native_fp(cls)) {
                                        native_memory(&c->dasm, false, LIR_TMP0, LIR_FRAME, c->outgoing + i->spill,
                                                   cls == LIR_F32 ? 4 : 8, false, false);
                                } else {
                                        native_home_to(c, r, LIR_TMP0, in->sig.params[p]);
                                }
                        } else if (in->sig.params[p] == LIR_TYPE_BOOL) {
                                native_mov(&c->dasm, LIR_TMP0, source, cls, false, false);
                                native_narrow(&c->dasm, LIR_TMP0, LIR_TYPE_BOOL);
                                source = LIR_TMP0;
                        }
                        u32 size = in->sig.params[p] == LIR_TYPE_VAL ? 8 : lir_type_size(in->sig.params[p]);
                        native_memory(&c->dasm, true, source, LIR_FRAME, args[p].stack, size,
                                   false, native_fp(cls) && !i->spilled);
                } else {
                        moves[count++] = (LirMove) {
                                .from = r, .to = r, .cls = cls,
                                .from_slot = i->spilled ? i->spill : LIR_NONE,
                                .to_slot = LIR_NONE,
                                .from_phys = i->phys, .to_phys = args[p].phys
                        };
                }
        }
        if (!lir_parallel_moves(moves, count, &c->target->gpr, &ordered, &n, c->err)) {
                goto End;
        }
        for (u32 i = 0; i < n; ++i) {
                native_frame_move(c, &ordered[i]);
        }
        for (u32 p = 0; p < in->ncall_args; ++p) {
                if (args[p].phys != LIR_PHYS_NONE && !args[p].fpr) {
                        native_narrow(&c->dasm, args[p].phys, in->sig.params[p]);
                }
        }
        ok = true;
End:
        free(args);
        free(moves);
        free(ordered);
        return ok;
}

static bool
native_live_pointer(LirEmitContext const *c, u32 r, u32 pc)
{
        LirInterval const *i = &c->alloc->intervals[r];
        u32 pos = 2 * pc + 1;
        if (c->L->regs[r].cls != LIR_PTR
            || (c->L->insts[pc].op == LIR_CALL && c->L->insts[pc].dst == r)) {
                return false;
        }
        if (i->nranges == 0 || pos < i->ranges[0].start
            || pos >= i->ranges[i->nranges - 1].end) {
                return false;
        }
        u32 lo = 0;
        u32 hi = i->nranges;
        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (i->ranges[mid].start <= pos) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }
        return pos < i->ranges[lo - 1].end;
}

static bool
native_rebases(LirEmitContext const *c, u32 pc)
{
        LirInst const *in = &c->L->insts[pc];
        if (c->L->resolved_mode != LIR_MODE_ATTACHED
            || (in->op != LIR_CALL && in->op != LIR_POLL)
            || (in->op == LIR_CALL
                && !(in->flags & (LIR_MAY_GC | LIR_MAY_THROW | LIR_RETURNS_TWICE)))) {
                return false;
        }
        for (u32 k = 0; k < c->npointers; ++k) {
                u32 r = c->pointers[k];
                if (native_live_pointer(c, r, pc)) {
                        return true;
                }
        }
        return false;
}

static void
native_rebase_live(LirEmitContext *c, u32 pc)
{
        if (!native_rebases(c, pc)) {
                return;
        }
        dasm_State **Dst = &c->dasm;
        native_rebase_begin(Dst, c->ty_slot, c->stack_base, c->rebased + pc);
        for (u32 k = 0; k < c->npointers; ++k) {
                u32 r = c->pointers[k];
                if (!native_live_pointer(c, r, pc)) {
                        continue;
                }
                LirInterval const *i = &c->alloc->intervals[r];
                u8 p = i->spilled ? LIR_TMP1 : i->phys;
                if (i->spilled) {
                        native_memory(Dst, false, p, LIR_FRAME, c->outgoing + i->spill, 8, false, false);
                }
                native_rebase_pointer(Dst, p, c->ty_slot, c->stack_base, c->stack_end);
                if (i->spilled) {
                        native_mov(Dst, LIR_TMP0, p, LIR_PTR, false, false);
                        native_memory(Dst, true, LIR_TMP0, LIR_FRAME, c->outgoing + i->spill, 8, false, false);
                }
        }
        native_label(Dst, c->rebased + pc);
}

static bool
native_call_inst(LirEmitContext *c, LirInst const *in, u32 pc)
{
        LirOpnd target = in->args[0];
        if (native_rebases(c, pc)) {
                native_stack_bounds(&c->dasm, c->ty_slot, c->stack_base, c->stack_end);
        }
        u64 address = 0;
        if (target.kind == LIR_OPERAND_REG) {
                native_home_to(c, target.reg, LIR_TMP0, LIR_TYPE_PTR);
                native_memory(&c->dasm, true, LIR_TMP0, LIR_FRAME, c->result, 8, false, false);
        } else if (target.kind == LIR_OPERAND_IMM) {
                address = target.imm;
        } else if (target.kind == LIR_OPERAND_CODE) {
                address = (uptr)target.code->body;
        } else if (target.kind == LIR_OPERAND_HELPER) {
                address = (uptr)target.helper->address;
        }
        if (!native_arguments(c, in)) {
                return false;
        }
        if (in->sig.variadic) {
                u32 nf = 0;
                for (u32 i = 0; i < in->sig.nparams; ++i) {
                        nf += in->sig.params[i] == LIR_TYPE_F32 || in->sig.params[i] == LIR_TYPE_F64;
                }
                native_varargs(&c->dasm, nf < c->target->fpr.nargs ? nf : c->target->fpr.nargs);
        }
        if (target.kind == LIR_OPERAND_REG) {
                native_memory(&c->dasm, false, LIR_TMP0, LIR_FRAME, c->result, 8, false, false);
        } else {
                native_li(&c->dasm, LIR_TMP0, address);
        }
        if (in->op == LIR_TAILCALL && !(in->flags & LIR_CALL_SITE)) {
                LirArgLocation *args = malloc(((usize)in->sig.nparams + 1) * sizeof *args);
                if (args == NULL) {
                        return false;
                }
                u32 outgoing = arg_locations(c->target, &in->sig, args);
                free(args);
                if (outgoing <= c->incoming) {
                        if (outgoing != 0) {
                                native_memory(&c->dasm, false, LIR_TAIL_BASE, LIR_FRAME, c->origin, 8, false, false);
                                for (u32 i = 0; i < outgoing; i += 8) {
                                        native_memory(&c->dasm, false, LIR_TAIL_COPY, LIR_FRAME, i, 8, false, false);
                                        native_memory(&c->dasm, true, LIR_TAIL_COPY, LIR_TAIL_BASE, 16 + i, 8, false, false);
                                }
                                if (in->sig.variadic) {
                                        u32 nf = 0;
                                        for (u32 i = 0; i < in->sig.nparams; ++i) {
                                                nf += in->sig.params[i] == LIR_TYPE_F32 || in->sig.params[i] == LIR_TYPE_F64;
                                        }
                                        native_varargs(&c->dasm, nf < c->target->fpr.nargs ? nf : c->target->fpr.nargs);
                                }
                        }
                        native_save_registers(c, false);
                        native_epilogue(&c->dasm, c->origin, true);
                        return true;
                }
        }
        if ((in->flags & (LIR_RETURNS_TWICE | LIR_CALL_SITE)) == (LIR_RETURNS_TWICE | LIR_CALL_SITE)) {
                native_twice_call(&c->dasm, c->pc_slot, c->sites + pc);
        } else {
                native_call(&c->dasm, (in->flags & LIR_CALL_SITE) != 0, c->thunk);
        }
        if (in->flags & LIR_CALL_SITE) {
                native_label(&c->dasm, c->sites + pc);
        }
        if (in->sig.ret != LIR_VOID && !native_fp(lir_type_class(in->sig.ret))) {
                native_narrow(&c->dasm, 0, in->sig.ret);
        }
        if (in->dst != LIR_NONE) {
                LirInterval const *d = &c->alloc->intervals[in->dst];
                LirClass cls = c->L->regs[in->dst].cls;
                if (d->spilled) {
                        native_memory(&c->dasm, true, 0, LIR_FRAME, c->outgoing + d->spill,
                                   cls == LIR_F32 || cls == LIR_I32 ? 4 : 8, false, native_fp(cls));
                } else {
                        native_mov(&c->dasm, d->phys, 0, cls, false, false);
                }
        }
        if (c->code->entry_thunk && target.kind == LIR_OPERAND_IMM
            && (uptr)target.imm == (uptr)lir_runtime()->reserve) {
                native_memory(&c->dasm, false, LIR_TMP0, LIR_FRAME, c->ty_slot, 8, false, false);
                native_memory(&c->dasm, false, LIR_TMP0, LIR_TMP0, offsetof(Ty, stack.count), 8, false, false);
                native_addr(&c->dasm, LIR_TMP0, LIR_TMP0, -(i64)c->code->entry_body_slots);
                native_memory(&c->dasm, true, LIR_TMP0, LIR_FRAME, c->top_slot, 8, false, false);
        }
        if (in->op == LIR_TAILCALL) {
                native_jump(&c->dasm, c->epilogue);
        }
        return true;
}

static void
native_save_registers(LirEmitContext *c, bool write)
{
        u32 offset = c->save_gp;
        for (u32 r = 0; r < 32; ++r) {
                if ((c->alloc->saved_gpr >> r) & 1) {
                        native_memory(&c->dasm, write, r, LIR_FRAME, offset, 8, false, false);
                        offset += 8;
                }
        }
        offset = c->save_fp;
        for (u32 r = 0; r < 32; ++r) {
                if ((c->alloc->saved_fpr >> r) & 1) {
                        native_memory(&c->dasm, write, r, LIR_FRAME, offset, 8, false, true);
                        offset += 8;
                }
        }
}

static void
native_parameters(LirEmitContext *c)
{
        Lir const *L = c->L;
        for (u32 p = 0; p < L->sig.nparams; ++p) {
                LirArgLocation a = c->arguments[p];
                LirClass cls = lir_type_class(L->sig.params[p]);
                if (a.phys != LIR_PHYS_NONE) {
                        native_memory(&c->dasm, true, a.phys, LIR_FRAME, c->params + p * 8,
                                   cls == LIR_F32 ? 4 : 8, false, a.fpr);
                }
        }
        for (u32 p = 0; p < L->sig.nparams; ++p) {
                LirArgLocation a = c->arguments[p];
                if (a.phys == LIR_PHYS_NONE) {
                        native_memory(&c->dasm, false, LIR_TMP0, LIR_FRAME, c->origin, 8, false, false);
                        u32 size = L->sig.params[p] == LIR_TYPE_VAL ? 8 : lir_type_size(L->sig.params[p]);
                        native_memory(&c->dasm, false, LIR_TMP0, LIR_TMP0, 16 + a.stack, size, false, false);
                        native_memory(&c->dasm, true, LIR_TMP0, LIR_FRAME, c->params + p * 8, 8, false, false);
                }
        }
        if (c->context) {
                native_li(&c->dasm, LIR_TMP0, (uptr)lir_runtime()->current_ty);
                native_call(&c->dasm, false, c->thunk);
                native_memory(&c->dasm, true, 0, LIR_FRAME, c->ty_slot, 8, false, false);
                native_memory(&c->dasm, false, LIR_TMP0, 0, offsetof(Ty, stack.count), 8, false, false);
                native_memory(&c->dasm, true, LIR_TMP0, LIR_FRAME, c->top_slot, 8, false, false);
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                LirRegInfo const *ri = &L->regs[r];
                LirInterval const *i = &c->alloc->intervals[r];
                if (ri->param == LIR_NONE
                    || (ri->pin == LIR_NONE
                        && (i->nranges == 0 || i->ranges[0].start != 0))) {
                        continue;
                }
                u8 d = i->spilled ? LIR_TMP0 : i->phys;
                LirClass cls = ri->cls;
                bool f = native_fp(cls);
                native_memory(&c->dasm, false, d, LIR_FRAME, c->params + ri->param * 8,
                           cls == LIR_F32 ? 4 : 8, false, f && !i->spilled);
                if (!f) {
                        native_narrow(&c->dasm, d, L->sig.params[ri->param]);
                }
                if (i->spilled) {
                        native_memory(&c->dasm, true, d, LIR_FRAME, c->outgoing + i->spill,
                                   cls == LIR_F32 ? 4 : 8, false, false);
                }
        }
        if (L->pc_param != LIR_NONE) {
                native_memory(&c->dasm, false, LIR_TMP0, LIR_FRAME, c->params + L->pc_param * 8, 8, false, false);
                native_addr(&c->dasm, LIR_TMP1, LIR_FRAME, c->pc_slot);
                native_memory(&c->dasm, true, LIR_TMP1, LIR_TMP0, 0, 8, false, false);
        }
}

static bool
native_poll(LirEmitContext *c, LirInst const *in, u32 pc, u32 fast, u32 end)
{
        LirRuntime const *rt = lir_runtime();
        dasm_State **Dst = &c->dasm;
        if (rt == NULL || rt->interrupt == NULL || rt->poll == NULL) {
                return emit_error(c->err, LIR_ERROR_MODE, pc, in->span, "POLL requires a VM runtime");
        }
        if (native_rebases(c, pc)) {
                native_stack_bounds(Dst, c->ty_slot, c->stack_base, c->stack_end);
        }
        native_li(Dst, LIR_TMP0, (uptr)rt->interrupt);
        native_memory(Dst, false, LIR_TMP0, LIR_TMP0, 0, 4, false, false);
        native_zero_branch(Dst, LIR_TMP0, false, true, fast);
        if (in->nargs == 4) {
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
                LirInst call = {
                        .sig = { .ret = LIR_TYPE_I32, .params = types, .nparams = 3, .nfixed = 3 },
                        .call_args = (LirOpnd *)in->args, .ncall_args = 3
                };
                if (!native_arguments(c, &call)) {
                        return false;
                }
        } else {
                native_memory(Dst, false, c->target->gpr.args[0], LIR_FRAME, c->ty_slot, 8, false, false);
                native_vm_top(Dst, c->target->gpr.args[1], c->target->gpr.args[0]);
                native_li(Dst, c->target->gpr.args[2], 0);
        }
        native_li(Dst, LIR_TMP0, (uptr)rt->poll);
        native_call(Dst, (in->flags & LIR_CALL_SITE) != 0, c->thunk);
        if (in->flags & LIR_CALL_SITE) {
                native_label(Dst, c->sites + pc);
        }
        native_mov(Dst, LIR_TMP0, 0, LIR_I32, false, false);
        native_jump(Dst, end);
        native_label(Dst, fast);
        native_li(Dst, LIR_TMP0, 0);
        native_label(Dst, end);
        native_memory(Dst, true, LIR_TMP0, LIR_FRAME, c->result, 8, false, false);
        if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                return false;
        }
        native_rebase_live(c, pc);
        native_memory(Dst, false, LIR_TMP0, LIR_FRAME, c->result, 8, false, false);
        native_zero_branch(Dst, LIR_TMP0, true, true, in->args[in->nargs - 1].label);
        return true;
}

static u64
native_fbits(Lir const *L, LirInst const *in)
{
        u64 bits;
        if (L->regs[in->dst].cls == LIR_F32) {
                float f = in->args[0].fimm;
                u32 u;
                memcpy(&u, &f, sizeof u);
                bits = u;
        } else {
                memcpy(&bits, &in->args[0].fimm, sizeof bits);
        }
        return bits;
}

static bool
native_instruction(LirEmitContext *c, u32 pc)
{
        Lir const *L = c->L;
        LirInst const *in = &L->insts[pc];
        LirForm form = LirOps[in->op].form;
        LirClass cls = in->dst == LIR_NONE ? LIR_I64 : L->regs[in->dst].cls;
        u8 d = in->dst == LIR_NONE ? LIR_PHYS_NONE : physical(c, in->dst, pc, true);
        u8 a[6] = {0};
        u32 yes = L->nlabels + 2 * pc;
        u32 end = yes + 1;
        dasm_State **Dst = &c->dasm;
        for (u32 p = 0; p < in->nargs; ++p) {
                if (in->args[p].kind == LIR_OPERAND_REG) {
                        a[p] = physical(c, in->args[p].reg, pc, false);
                }
        }
        switch (form) {
        case LIR_FORM_MOV:
                if (in->args[0].kind == LIR_OPERAND_REG) {
                        native_mov(Dst, d, a[0], cls, false, false);
                } else if (in->args[0].kind == LIR_OPERAND_CONST) {
                        native_li(Dst, d, (uptr)&c->code->roots[in->args[0].index]);
                } else if (in->args[0].kind == LIR_OPERAND_REFCONST) {
                        Value const *v = &c->code->roots[in->args[0].index];
                        void *ptr = v->ptr;
                        if ((v->type & ~VALUE_TAGGED) == VALUE_OBJECT) {
                                ptr = v->object;
                        } else if ((v->type & ~VALUE_TAGGED) == VALUE_TUPLE) {
                                ptr = v->items;
                        } else if ((v->type & ~VALUE_TAGGED) == VALUE_STRING) {
                                ptr = v->str0 == NULL ? (void *)v->str : v->str0;
                        }
                        native_li(Dst, d, (uptr)ptr);
                } else if (in->args[0].kind == LIR_OPERAND_VSLOT) {
                        native_memory(Dst, false, LIR_TMP0, LIR_FRAME, c->ty_slot, 8, false, false);
                        native_vm_slots(Dst, d, LIR_TMP0, c->top_slot);
                        native_addr(Dst, d, d,
                                 ((i64)in->args[0].index - c->code->nvslots) * sizeof (Value));
                } else {
                        return emit_error(c->err, LIR_ERROR_TARGET, pc, in->span, "unsupported native move");
                }
                break;
        case LIR_FORM_LI:
                native_li(Dst, d, cls == LIR_I32 ? (u32)in->args[0].imm : (u64)in->args[0].imm);
                break;
        case LIR_FORM_FLI:
                native_fli(Dst, d, cls, c->literals + pc);
                if (c->islands) {
                        native_jump(Dst, end);
                        native_literal(Dst, c->literals + pc, native_fbits(L, in));
                        native_label(Dst, end);
                }
                break;
        case LIR_FORM_IBINARY:
                if (in->args[1].kind == LIR_OPERAND_IMM) {
                        native_integer_imm(Dst, in->op, d, a[0], in->args[1].imm, cls == LIR_I32);
                } else {
                        native_integer(Dst, in->op, d, a[0], a[1], cls == LIR_I32);
                }
                break;
        case LIR_FORM_IUNARY:
                if (in->op == LIR_POPCNT) {
                        native_popcnt(Dst, d, a[0], cls == LIR_I32);
                } else {
                        native_unary(Dst, in->op, d, a[0], cls == LIR_I32);
                }
                break;
        case LIR_FORM_CHECKED:
                native_checked(Dst, in->op, d, a[0], a[1], cls == LIR_I32);
                if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                        return false;
                }
                native_checked_branch(Dst, in->op, in->args[2].label);
                return true;
        case LIR_FORM_FBINARY:
        case LIR_FORM_FUNARY:
        case LIR_FORM_FMA:
                native_float(Dst, in->op, d, a[0], a[1], a[2], cls == LIR_F32);
                break;
        case LIR_FORM_I2F:
        case LIR_FORM_F2I:
        case LIR_FORM_FEXT:
        case LIR_FORM_FTRUNC:
        case LIR_FORM_BITCAST:
                native_convert(Dst, in->op, d, a[0], cls, L->regs[in->args[0].reg].cls);
                break;
        case LIR_FORM_LEA:
        case LIR_FORM_LD:
        case LIR_FORM_ST: {
                LirMem mem = in->args[0].mem;
                u8 base = physical(c, mem.base, pc, false);
                u8 index = mem.index == LIR_NONE ? LIR_PHYS_NONE : physical(c, mem.index, pc, false);
                if (form == LIR_FORM_LEA) {
                        native_lea(Dst, d, base, index, mem.scale, mem.disp,
                                mem.index != LIR_NONE && L->regs[mem.index].cls == LIR_I32);
                } else {
                        LirType type = LirOps[in->op].type;
                        u32 size = lir_type_size(type);
                        bool direct = index == LIR_PHYS_NONE;
#if defined(__aarch64__)
                        direct = direct && mem.disp >= 0 && (u32)mem.disp <= 4095 * size
                                        && mem.disp % size == 0;
#endif
                        i32 disp = mem.disp;
                        if (!direct) {
                                native_lea(Dst, LIR_TMP0, base, index, mem.scale, mem.disp,
                                        mem.index != LIR_NONE && L->regs[mem.index].cls == LIR_I32);
                                base = LIR_TMP0;
                                disp = 0;
                        }
                        bool sign = type == LIR_TYPE_I8 || type == LIR_TYPE_I16 || type == LIR_TYPE_I32;
                        native_memory(Dst, form == LIR_FORM_ST, form == LIR_FORM_ST ? a[1] : d,
                                   base, disp, size, sign, native_fp(lir_type_class(type)));
                }
                break;
        }
        case LIR_FORM_SETCC:
        case LIR_FORM_FSETCC:
        case LIR_FORM_SELECT:
        case LIR_FORM_FSELECT:
        case LIR_FORM_BR:
        case LIR_FORM_FBR: {
                LirClass source = L->regs[in->args[1].reg].cls;
                native_compare(Dst, a[1], a[2], source);
                if (form == LIR_FORM_BR || form == LIR_FORM_FBR) {
                        if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                                return false;
                        }
                        native_branch(Dst, in->args[0].cc, in->args[3].label);
                        return true;
                }
                if (form == LIR_FORM_SELECT || form == LIR_FORM_FSELECT) {
                        native_branch(Dst, in->args[0].cc, yes);
                        native_select(Dst, d, a[3], a[4], cls, yes, end);
                } else {
                        native_setcc(Dst, d, in->args[0].cc);
                }
                break;
        }
        case LIR_FORM_BRZ:
                native_zero_compare(Dst, a[0], L->regs[in->args[0].reg].cls);
                if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                        return false;
                }
                native_branch(Dst, in->op == LIR_BRNZ ? LIR_NE : LIR_EQ, in->args[1].label);
                return true;
        case LIR_FORM_JMP:
                if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                        return false;
                }
                native_jump(Dst, in->args[0].label);
                return true;
        case LIR_FORM_SWITCH:
                native_memory(Dst, true, a[0], LIR_FRAME, c->result, 8, false, false);
                if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                        return false;
                }
                native_memory(Dst, false, LIR_TMP0, LIR_FRAME, c->result, 8, false, false);
                if (L->regs[in->args[0].reg].cls == LIR_I32) {
                        native_narrow(Dst, LIR_TMP0, LIR_TYPE_U32);
                }
                native_switch(Dst, LIR_TMP0, in->ntargets, in->args[1].label, c->literals + pc);
                if (c->islands) {
                        native_table(Dst, c->literals + pc, in->targets, in->ntargets);
                }
                return true;
        case LIR_FORM_RET:
                if (in->nargs != 0) {
                        native_home_to(c, in->args[0].reg, 0, L->sig.ret);
                }
                native_jump(Dst, c->epilogue);
                return true;
        case LIR_FORM_CALL:
        case LIR_FORM_TAILCALL:
                if (!native_call_inst(c, in, pc)) {
                        return false;
                }
                if (form == LIR_FORM_TAILCALL) {
                        return true;
                }
                if (!native_phase(c, pc, LIR_MOVE_AFTER)) {
                        return false;
                }
                native_rebase_live(c, pc);
                return true;
        case LIR_FORM_CAS:
        case LIR_FORM_ATOMIC:
                native_atomic(Dst, in->op, d, physical(c, in->args[0].mem.base, pc, false),
                           a[1], a[2], cls == LIR_I32, yes, end);
                break;
        case LIR_FORM_FENCE:
                native_fence(Dst);
                break;
        case LIR_FORM_ALLOCA:
                native_addr(Dst, d, LIR_FRAME, c->outgoing + c->alloc->alloca_offsets[pc]);
                break;
        case LIR_FORM_SITE:
                native_label(Dst, c->sites + pc);
                break;
        case LIR_FORM_ENTRY:
                break;
        case LIR_FORM_RAW:
#if defined(__aarch64__)
                if (in->raw.narm64 == 0) {
                        return emit_error(c->err, LIR_ERROR_TARGET, pc, in->span, "RAW has no arm64 instructions");
                }
                for (u32 i = 0; i < in->raw.narm64; ++i) {
                        native_word(Dst, in->raw.arm64[i]);
                }
#else
                if (in->raw.nx64 == 0) {
                        return emit_error(c->err, LIR_ERROR_TARGET, pc, in->span, "RAW has no x64 instructions");
                }
                for (u32 i = 0; i < in->raw.nx64; ++i) {
                        native_byte(Dst, in->raw.x64[i]);
                }
#endif
                break;
        case LIR_FORM_POLL:
                return native_poll(c, in, pc, yes, end);
        }
        return native_phase(c, pc, LIR_MOVE_AFTER);
}

static bool
native_emit(Lir const *L, LirAlloc const *alloc, LirCode *code, LirError *err)
{
        LirEmitContext c = { .L = L, .alloc = alloc, .code = code, .target = &NativeTarget,
                           .err = err, .context = alloc->nvslots > L->nvslots };
        JitMapping mapping = {0};
        u32 *labels = NULL;
        u32 *next = NULL;
        u32 nlabels = L->nlabels + 5 * L->ninsts + 4;
        u32 ns = 0;
        u32 ne = 0;
        usize size;
        usize table_offset;
        usize mapping_size;
        bool ok = false;
        int status;
        void *globals[1] = {0};
        labels = malloc(((usize)L->ninsts + 1) * sizeof *labels);
        next = malloc(((usize)L->nlabels + 1) * sizeof *next);
        c.phase_at = malloc(((usize)L->ninsts * 2 + 2) * sizeof *c.phase_at);
        c.phase_next = malloc(((usize)alloc->nmoves + 1) * sizeof *c.phase_next);
        c.constraint_at = malloc(((usize)L->ninsts + 1) * sizeof *c.constraint_at);
        c.constraint_next = malloc(((usize)alloc->nconstraints + 1) * sizeof *c.constraint_next);
        if (labels == NULL || next == NULL || c.phase_at == NULL || c.phase_next == NULL
            || c.constraint_at == NULL || c.constraint_next == NULL) {
                goto End;
        }
        for (u32 pc = 0; pc <= L->ninsts; ++pc) {
                labels[pc] = LIR_NONE;
                c.phase_at[2 * pc] = LIR_NONE;
                c.phase_at[2 * pc + 1] = LIR_NONE;
                c.constraint_at[pc] = LIR_NONE;
        }
        for (u32 i = alloc->nmoves; i-- > 0;) {
                LirMove const *move = &alloc->moves[i];
                if (move->op >= L->ninsts) {
                        continue;
                }
                u32 pc = 2 * move->op + move->phase;
                c.phase_next[i] = c.phase_at[pc];
                c.phase_at[pc] = i;
        }
        for (u32 i = alloc->nconstraints; i-- > 0;) {
                LirConstraint const *constraint = &alloc->constraints[i];
                if (constraint->op >= L->ninsts) {
                        continue;
                }
                c.constraint_next[i] = c.constraint_at[constraint->op];
                c.constraint_at[constraint->op] = i;
        }
        for (u32 l = L->nlabels; l-- > 0;) {
                u32 pc = L->labels[l].pos;
                next[l] = labels[pc];
                labels[pc] = l;
        }
        c.arguments = malloc(((usize)L->sig.nparams + 1) * sizeof *c.arguments);
        c.pointers = malloc(((usize)L->nregs + 1) * sizeof *c.pointers);
        if (c.arguments == NULL || c.pointers == NULL) {
                goto End;
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                if (L->regs[r].cls == LIR_PTR && alloc->intervals[r].crosses_call) {
                        c.pointers[c.npointers++] = r;
                }
        }
        c.incoming = arg_locations(c.target, &L->sig, c.arguments);
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (in->op == LIR_CALL || in->op == LIR_TAILCALL) {
                        LirArgLocation *args = malloc(((usize)in->sig.nparams + 1) * sizeof *args);
                        if (args == NULL) {
                                goto End;
                        }
                        u32 outgoing = arg_locations(c.target, &in->sig, args);
                        free(args);
                        if (outgoing > c.outgoing) {
                                c.outgoing = outgoing;
                        }
                }
                ns += in->op == LIR_SITE || (in->flags & LIR_CALL_SITE);
                ne += in->op == LIR_ENTRY;
                c.context = c.context || (in->op == LIR_POLL && in->nargs == 1)
                                     || native_rebases(&c, pc);
                for (u32 i = 0; i < in->nargs; ++i) {
                        c.context = c.context || in->args[i].kind == LIR_OPERAND_VSLOT;
                }
        }
        if (c.context && (lir_runtime() == NULL || lir_runtime()->current_ty == NULL)) {
                emit_error(err, LIR_ERROR_MODE, LIR_NONE, (LirSpan) {0}, "attached calls, value slots and implicit polls require a Ty context");
                goto End;
        }
        c.outgoing = (c.outgoing + alloc->frame_align - 1) & ~(alloc->frame_align - 1);
        c.save_gp = c.outgoing + alloc->frame_size;
        c.save_fp = c.save_gp + __builtin_popcountll(alloc->saved_gpr) * 8;
        c.params = c.save_fp + __builtin_popcountll(alloc->saved_fpr) * 8;
        c.origin = c.params + L->sig.nparams * 8;
        c.pc_slot = c.origin + 8;
        c.result = c.pc_slot + 8;
        c.ty_slot = c.result + 8;
        c.top_slot = c.ty_slot + 8;
        c.stack_base = c.top_slot + 8;
        c.stack_end = c.stack_base + 8;
        c.frame = (c.stack_end + 8 + 15) & ~(u32)15;
        c.epilogue = L->nlabels + 2 * L->ninsts;
        c.thunk = c.epilogue + 1;
        c.literals = c.thunk + 1;
        c.sites = c.literals + L->ninsts;
        c.rebased = c.sites + L->ninsts;
#if defined(__aarch64__)
Emit:
#endif
        dasm_init(&c.dasm, 1);
        dasm_setupglobal(&c.dasm, globals, 0);
        dasm_growpc(&c.dasm, nlabels);
        dasm_setup(&c.dasm, lir_actions);
        native_prologue(&c.dasm, c.frame, alloc->frame_align, c.origin);
        native_save_registers(&c, true);
        native_parameters(&c);
        for (u32 pc = 0; pc <= L->ninsts; ++pc) {
                for (u32 l = labels[pc]; l != LIR_NONE; l = next[l]) {
                        native_label(&c.dasm, l);
                }
                if (pc == L->ninsts) {
                        break;
                }
                if (!native_phase(&c, pc, LIR_MOVE_BEFORE) || !native_instruction(&c, pc)) {
                        goto End;
                }
        }
        native_label(&c.dasm, c.epilogue);
        native_save_registers(&c, false);
        native_epilogue(&c.dasm, c.origin, false);
        native_runtime_call(&c.dasm, c.thunk, c.pc_slot);
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (c.islands) {
                        continue;
                }
                if (in->op == LIR_FLI) {
                        native_literal(&c.dasm, c.literals + pc, native_fbits(L, in));
                } else if (in->op == LIR_SWITCH) {
                        native_table(&c.dasm, c.literals + pc, in->targets, in->ntargets);
                }
        }
        status = dasm_link(&c.dasm, &size);
        if (status != DASM_S_OK) {
                char message[96];
                snprintf(message, sizeof message, "%s DynASM link failed: 0x%x", c.target->name, status);
                emit_error(err, LIR_ERROR_TARGET, LIR_NONE, (LirSpan) {0}, message);
                goto End;
        }
#if defined(__aarch64__)
        if (!c.islands && size > (1u << 19)) {
                dasm_free(&c.dasm);
                c.islands = true;
                goto Emit;
        }
#endif
        table_offset = (size + alignof (LirSite) - 1) & ~(usize)(alignof (LirSite) - 1);
        mapping_size = sizeof (LirImage) + table_offset + ns * sizeof (LirSite) + ne * sizeof (u32);
        if (table_offset > UINT32_MAX || mapping_size < table_offset) {
                emit_error(err, LIR_ERROR_TARGET, LIR_NONE, (LirSpan) {0}, "native code image is too large");
                goto End;
        }
        mapping = jm_alloc(mapping_size);
        if (mapping.rx == NULL) {
                goto End;
        }
        LirImage *header = mapping.rw;
        u8 *rw = (u8 *)(header + 1);
        u8 *rx = (u8 *)mapping.rx + sizeof *header;
        LirSite *sites = (void *)(rw + table_offset);
        u32 *resumes = (void *)(sites + ns);
        u32 si = 0;
        u32 ei = 0;
        jm_write_begin();
        *header = (LirImage) { .size = size, .table = table_offset, .nsites = ns, .nresume = ne };
        status = dasm_encode(&c.dasm, rw);
        for (u32 pc = 0; pc < L->ninsts && status == DASM_S_OK; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (in->op == LIR_SWITCH) {
                        u32 off = dasm_getpclabel(&c.dasm, c.literals + pc);
                        uptr *table = (void *)(rw + off);
                        for (u32 i = 0; i < in->ntargets; ++i) {
                                table[i] = (uptr)rx + dasm_getpclabel(&c.dasm, in->targets[i]);
                        }
                }
                if (in->op == LIR_SITE || (in->flags & LIR_CALL_SITE)) {
                        sites[si++] = (LirSite) {
                                .pc = dasm_getpclabel(&c.dasm, c.sites + pc),
                                .tag = in->op == LIR_SITE ? in->args[0].imm : in->tag
                        };
                }
                if (in->op == LIR_ENTRY) {
                        resumes[ei++] = in->tag;
                }
        }
        bool sealed = jm_write_end(mapping.rx, mapping_size);
        if (status != DASM_S_OK || !sealed) {
                emit_error(err, LIR_ERROR_TARGET, LIR_NONE, (LirSpan) {0}, "native code publication failed");
                goto End;
        }
        code->sites = calloc((usize)ns + 1, sizeof *code->sites);
        code->entries = calloc((usize)ne + 1, sizeof *code->entries);
        if (code->sites == NULL || code->entries == NULL) {
                goto End;
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (in->op == LIR_SITE || (in->flags & LIR_CALL_SITE)) {
                        code->sites[code->nsites++] = (LirSite) {
                                .pc = dasm_getpclabel(&c.dasm, c.sites + pc),
                                .tag = in->op == LIR_SITE ? in->args[0].imm : in->tag
                        };
                }
                if (in->op == LIR_ENTRY) {
                        code->entries[code->nentries++] = (LirEntryInfo) {
                                .label = in->args[0].label,
                                .offset = dasm_getpclabel(&c.dasm, in->args[0].label)
                        };
                }
        }
        code->allocation = mapping.rx;
        code->body = rx;
        code->size = size;
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                if (L->insts[pc].op == LIR_FLI || L->insts[pc].op == LIR_SWITCH) {
                        u32 offset = dasm_getpclabel(&c.dasm, c.literals + pc);
                        code->literal_pool = rx + offset;
                        code->literal_size = size - offset;
                        break;
                }
        }
        jm_perf(code->body, code->size, code->name);
        ok = true;
End:
        if (!ok && mapping.rx != NULL) {
                jm_free(mapping.rx);
        }
        if (c.dasm != NULL) {
                dasm_free(&c.dasm);
        }
        free(c.arguments);
        free(c.pointers);
        free(c.phase_at);
        free(c.phase_next);
        free(c.constraint_at);
        free(c.constraint_next);
        free(labels);
        free(next);
        if (!ok && err != NULL && err->kind == LIR_ERROR_NONE) {
                emit_error(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "could not emit native function");
        }
        return ok;
}
#endif

LirTarget const *
lir_target(void)
{
#if defined(__aarch64__) || defined(__x86_64__)
        return &NativeTarget;
#else
        return NULL;
#endif
}

bool
lir_legalize(Lir *L, LirTarget const *target, LirConstraint **constraints,
             u32 *nconstraints, LirError *err)
{
        *constraints = NULL;
        *nconstraints = 0;
        if (target == NULL || target->legalize == NULL) {
                return emit_error(err, LIR_ERROR_TARGET, LIR_NONE, (LirSpan) {0}, "no native LIR target");
        }
        if (!lir_normalize(L, err)) {
                return false;
        }
        return target->legalize(L, constraints, nconstraints, err);
}

void
lir_code_destroy(LirCode *code)
{
        if (code == NULL) {
                return;
        }
        jm_free(code->allocation);
        lir_interp_destroy(code);
        lir_code_free(code->entry_code);
        lir_free(code->lir);
        free(code->roots);
        free(code->sites);
        free(code->entries);
        free(code->name);
}

void
lir_code_free(LirCode *code)
{
        if (code == NULL) {
                return;
        }
        lir_code_destroy(code);
        free(code);
}

static void
debug_dump(Lir const *L, LirAlloc const *alloc, char const *stage)
{
        char const *pattern = getenv("TY_JIT_DUMP");
        if (pattern == NULL || *pattern == '\0') {
                return;
        }
        regex_t regex;
        if (regcomp(&regex, pattern, REG_EXTENDED | REG_NOSUB) != 0) {
                return;
        }
        bool matches = regexec(&regex, L->name, 0, NULL, 0) == 0;
        regfree(&regex);
        if (!matches) {
                return;
        }
        flockfile(stderr);
        fprintf(stderr, "jit-dump: %s stage=%s\n", L->name, stage);
        lir_dump(L, stderr);
        if (alloc != NULL) {
                fprintf(stderr, "frame: %u bytes, %u vslots\n",
                        alloc->frame_size, alloc->nvslots);
                for (u32 r = 0; r < alloc->nintervals; ++r) {
                        LirInterval const *interval = &alloc->intervals[r];
                        if (interval->spilled) {
                                fprintf(stderr, "  r%u: spill+%u\n", r, interval->spill);
                        } else {
                                LirClass cls = L->regs[r].cls;
                                char bank = cls == LIR_F32 || cls == LIR_F64 ? 'f' : 'g';
                                fprintf(stderr, "  r%u: %c%u\n", r, bank, interval->phys);
                        }
                }
        }
        funlockfile(stderr);
}

static LirCode *
finish(Lir *L, bool entry, bool interpreted, bool entry_thunk, u32 body_slots, LirError *err)
{
        LirCode *code = NULL;
        Lir *legal = NULL;
        LirCFG cfg = {0};
        LirAlloc alloc = {0};
        LirConstraint *constraints = NULL;
        u32 nconstraints = 0;
        LirTarget const *target = lir_target();
        if (err != NULL) {
                *err = (LirError) {0};
        }
        if (!entry_thunk && !lir_validate(L, err)) {
                return NULL;
        }
        debug_dump(L, NULL, "lir");
        code = calloc(1, sizeof *code);
        if (code == NULL) {
                goto Error;
        }
        code->entry_thunk = entry_thunk;
        code->entry_body_slots = body_slots;
        code->name = malloc(strlen(L->name) + 1);
        if (code->name == NULL) {
                goto Error;
        }
        strcpy(code->name, L->name);
        code->lir = lir_clone(L, err);
        if (code->lir == NULL) {
                goto Error;
        }
        code->sig = code->lir->sig;
        code->mode = L->resolved_mode;
        code->nroots = L->nroots;
        code->roots = calloc((usize)L->nroots + 1, sizeof *code->roots);
        if (code->roots == NULL) {
                goto Error;
        }
        if (L->nroots != 0) {
                memcpy(code->roots, L->roots, L->nroots * sizeof *code->roots);
        }
        if (interpreted || target == NULL) {
                if (!lir_interp_emit(code, err)) {
                        goto Error;
                }
                code->nvslots = L->nvslots;
        } else {
                legal = lir_clone(L, err);
                if (legal == NULL || !lir_legalize(legal, target, &constraints, &nconstraints, err)
                    || !lir_cfg(legal, &cfg, err)
                    || !lir_allocate(legal, &cfg, target, constraints, nconstraints, &alloc, err)
                    || !lir_allocate_workspaces(legal, target, &alloc, err)) {
                        goto Error;
                }
                code->nvslots = alloc.nvslots;
                debug_dump(legal, NULL, "legal");
                debug_dump(legal, &alloc, "alloc");
                if (!target->emit(legal, &alloc, code, err)) {
                        goto Error;
                }
        }
        if (entry) {
                LirCode entry_code = *code;
                if (interpreted || target == NULL) {
                        entry_code.nvslots = 0;
                }
                Lir *thunk = lir_build_entry(&entry_code, err);
                if (thunk == NULL) {
                        goto Error;
                }
                code->entry_code = finish(thunk, false, interpreted, true, code->nvslots, err);
                if (code->entry_code == NULL) {
                        lir_free(thunk);
                        goto Error;
                }
                if (code->entry_code->nvslots != 0) {
                        for (u32 pc = 0; pc < thunk->ninsts; ++pc) {
                                LirInst *in = &thunk->insts[pc];
                                if (in->op == LIR_CALL && in->args[0].kind == LIR_OPERAND_IMM
                                    && (uptr)in->args[0].imm == (uptr)lir_runtime()->reserve) {
                                        in->call_args[2] = lir_i((u64)code->nvslots + code->entry_code->nvslots);
                                        break;
                                }
                        }
                        lir_code_free(code->entry_code);
                        code->entry_code = finish(thunk, false, interpreted, true, code->nvslots, err);
                        if (code->entry_code == NULL) {
                                lir_free(thunk);
                                goto Error;
                        }
                }
                lir_free(thunk);
                code->entry = code->entry_code->body;
        }
        free(constraints);
        lir_free(legal);
        lir_alloc_free(&alloc);
        lir_cfg_free(&cfg);
        return code;
Error:
        free(constraints);
        lir_free(legal);
        lir_alloc_free(&alloc);
        lir_cfg_free(&cfg);
        lir_code_free(code);
        if (err != NULL && err->kind == LIR_ERROR_NONE) {
                emit_error(err, LIR_ERROR_MEMORY, LIR_NONE, (LirSpan) {0}, "could not compile LIR");
        }
        return NULL;
}

LirCode *
lir_finish(Lir *L, bool entry, LirError *err)
{
        return finish(L, entry, false, false, 0, err);
}

LirCode *
lir_finish_interpreted(Lir *L, bool entry, LirError *err)
{
        return finish(L, entry, true, false, 0, err);
}
