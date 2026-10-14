#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ty.h"
#include "lir.h"

static u32 checks;
static u32 failures;

#define CHECK(expr) do { \
        ++checks; \
        if (!(expr)) { \
                fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #expr); \
                ++failures; \
        } \
} while (0)

static Lir *
function(LirType ret, LirType const *params, u32 n, LirMode mode)
{
        LirError err;
        LirSig sig = { .ret = ret, .params = params, .nparams = n, .nfixed = n };
        Lir *L = lir_new("test", &sig, mode, &err);
        CHECK(L != NULL);
        if (L == NULL) {
                fprintf(stderr, "%s\n", err.message);
                exit(1);
        }
        return L;
}

static void
emit(Lir *L, LirOp op, LirReg dst, LirOpnd const *args, u32 n)
{
        CHECK(lir_emit_to(L, op, dst, args, n));
}

static void
ret(Lir *L, LirReg r)
{
        if (r == LIR_NONE) {
                emit(L, LIR_RET, LIR_NONE, NULL, 0);
        } else {
                emit(L, LIR_RET, LIR_NONE, (LirOpnd[]) { lir_r(r) }, 1);
        }
}

static void
valid(Lir *L)
{
        LirError err;
        bool ok = lir_validate(L, &err);
        CHECK(ok);
        if (!ok) {
                fprintf(stderr, "op %u: %s\n", err.op, err.message);
                lir_dump(L, stderr);
        }
}

static void
invalid(Lir *L, LirErrorKind kind)
{
        LirError err;
        CHECK(!lir_validate(L, &err));
        CHECK(err.kind == kind);
        CHECK(err.message[0] != '\0');
}

static void
check_ops(void)
{
        LirType params[] = {
                LIR_TYPE_I64, LIR_TYPE_I64, LIR_TYPE_I64,
                LIR_TYPE_F64, LIR_TYPE_F64, LIR_TYPE_F64,
                LIR_TYPE_F32, LIR_TYPE_PTR
        };
        for (LirOp op = 0; op < LIR_OP_COUNT; ++op) {
                Lir *L = function(LIR_VOID, params, countof(params), LIR_MODE_AUTO);
                LirOpInfo const *info = &LirOps[op];
                LirInst in = { .op = op, .dst = LIR_NONE, .nargs = info->argc };
                LirReg d = LIR_NONE;
                LirReg x = L->params[0];
                LirReg y = L->params[1];
                LirReg z = L->params[2];
                LirReg f = L->params[3];
                LirReg g = L->params[4];
                LirReg h = L->params[5];
                LirReg s = L->params[6];
                LirReg p = L->params[7];
                LirReg w = lir_reg(L, LIR_I32);
                LirLabel target = lir_label(L);
                LirOpnd mem = lir_m(p, x, 8, -16);
                LirLabel targets[] = { target, target };
                u8 machine[] = { 0x90 };
                u32 words[] = { 0xd503201f };
                LirRawBinding inputs[] = { { .phys = 0, .reg = x } };
                LirRawBinding outputs[] = { { .phys = 1, .reg = y } };
                emit(L, LIR_LI, w, (LirOpnd[]) { lir_i(3) }, 1);
                switch (info->form) {
                case LIR_FORM_MOV:
                        d = lir_reg(L, LIR_I64);
                        in.args[0] = lir_r(x);
                        break;
                case LIR_FORM_LI:
                        d = lir_reg(L, LIR_I64);
                        in.args[0] = lir_i(INT64_MIN);
                        break;
                case LIR_FORM_FLI:
                        d = lir_reg(L, LIR_F64);
                        in.args[0] = lir_f(1.5);
                        break;
                case LIR_FORM_LEA:
                        d = lir_reg(L, LIR_PTR);
                        in.args[0] = mem;
                        break;
                case LIR_FORM_IBINARY:
                case LIR_FORM_CHECKED:
                        d = lir_reg(L, LIR_I64);
                        in.args[0] = lir_r(x);
                        in.args[1] = lir_r(y);
                        in.args[2] = lir_l(target);
                        break;
                case LIR_FORM_IUNARY:
                        d = lir_reg(L, LIR_I64);
                        in.args[0] = lir_r(x);
                        break;
                case LIR_FORM_FBINARY:
                case LIR_FORM_FUNARY:
                case LIR_FORM_FMA:
                        d = lir_reg(L, LIR_F64);
                        in.args[0] = lir_r(f);
                        in.args[1] = lir_r(g);
                        in.args[2] = lir_r(h);
                        break;
                case LIR_FORM_I2F:
                        d = lir_reg(L, LIR_F64);
                        in.args[0] = lir_r(x);
                        break;
                case LIR_FORM_F2I:
                case LIR_FORM_BITCAST:
                        d = lir_reg(L, LIR_I64);
                        in.args[0] = lir_r(f);
                        break;
                case LIR_FORM_FEXT:
                        d = lir_reg(L, LIR_F64);
                        in.args[0] = lir_r(s);
                        break;
                case LIR_FORM_FTRUNC:
                        d = lir_reg(L, LIR_F32);
                        in.args[0] = lir_r(f);
                        break;
                case LIR_FORM_LD:
                        d = lir_reg(L, lir_type_class(info->type));
                        in.args[0] = mem;
                        break;
                case LIR_FORM_ST:
                        in.args[0] = mem;
                        in.args[1] = lir_r(x);
                        if (info->type == LIR_TYPE_F32) {
                                in.args[1] = lir_r(s);
                        } else if (info->type == LIR_TYPE_F64) {
                                in.args[1] = lir_r(f);
                        }
                        break;
                case LIR_FORM_SETCC:
                case LIR_FORM_SELECT:
                case LIR_FORM_BR:
                        in.args[0] = lir_cc(LIR_LT);
                        in.args[1] = lir_r(x);
                        in.args[2] = lir_r(y);
                        in.args[3] = lir_l(target);
                        if (op != LIR_BR) {
                                d = lir_reg(L, LIR_I64);
                        }
                        if (op == LIR_SELECT) {
                                in.args[3] = lir_r(y);
                                in.args[4] = lir_r(z);
                        }
                        break;
                case LIR_FORM_FSETCC:
                case LIR_FORM_FSELECT:
                case LIR_FORM_FBR:
                        in.args[0] = lir_cc(LIR_FUN);
                        in.args[1] = lir_r(f);
                        in.args[2] = lir_r(g);
                        in.args[3] = lir_l(target);
                        if (op != LIR_FBR) {
                                d = lir_reg(L, LIR_I64);
                        }
                        if (op == LIR_FSELECT) {
                                in.args[3] = lir_r(x);
                                in.args[4] = lir_r(y);
                        }
                        break;
                case LIR_FORM_BRZ:
                        in.args[0] = lir_r(x);
                        in.args[1] = lir_l(target);
                        break;
                case LIR_FORM_JMP:
                case LIR_FORM_POLL:
                        in.args[0] = lir_l(target);
                        break;
                case LIR_FORM_SWITCH:
                        in.args[0] = lir_r(x);
                        in.args[1] = lir_l(target);
                        in.targets = targets;
                        in.ntargets = countof(targets);
                        break;
                case LIR_FORM_RET:
                        break;
                case LIR_FORM_CALL:
                case LIR_FORM_TAILCALL:
                        in.args[0] = lir_i(1);
                        in.sig.ret = LIR_VOID;
                        break;
                case LIR_FORM_CAS:
                case LIR_FORM_ATOMIC:
                        d = lir_reg(L, LIR_I64);
                        in.args[0] = mem;
                        in.args[1] = lir_r(x);
                        in.args[2] = lir_r(y);
                        break;
                case LIR_FORM_FENCE:
                        break;
                case LIR_FORM_ALLOCA:
                        d = lir_reg(L, LIR_PTR);
                        in.args[0] = lir_i(32);
                        in.args[1] = lir_i(16);
                        break;
                case LIR_FORM_SITE:
                        in.args[0] = lir_i(UINT32_MAX);
                        break;
                case LIR_FORM_ENTRY:
                        CHECK(lir_entry(L, target));
                        break;
                case LIR_FORM_RAW:
                        in.raw = (LirRaw) {
                                .arm64 = words, .narm64 = countof(words),
                                .x64 = machine, .nx64 = countof(machine),
                                .in = inputs, .nin = countof(inputs),
                                .out = outputs, .nout = countof(outputs),
                                .gpr_clobber = 4
                        };
                        break;
                }
                if (op != LIR_ENTRY) {
                        in.dst = d;
                        CHECK(lir_emit(L, &in));
                        CHECK(lir_bind(L, target));
                }
                ret(L, LIR_NONE);
                valid(L);
                CHECK(L->resolved_mode == (op == LIR_POLL ? LIR_MODE_ATTACHED : LIR_MODE_DETACHED));
                LirBytes bytes;
                LirError err;
                CHECK(lir_serialize(L, &bytes, &err));
                Lir *decoded = lir_deserialize(bytes.items, bytes.count,
                                               bytes.holes, bytes.nholes, &err);
                CHECK(decoded != NULL);
                if (decoded != NULL) {
                        CHECK(decoded->nregs == L->nregs);
                        CHECK(decoded->nlabels == L->nlabels);
                        CHECK(decoded->ninsts == L->ninsts);
                        CHECK(decoded->mode == L->mode);
                        for (u32 i = 0; i < L->ninsts; ++i) {
                                CHECK(decoded->insts[i].op == L->insts[i].op);
                                CHECK(decoded->insts[i].dst == L->insts[i].dst);
                                CHECK(decoded->insts[i].nargs == L->insts[i].nargs);
                                CHECK(decoded->insts[i].ntargets == L->insts[i].ntargets);
                                CHECK(decoded->insts[i].raw.narm64 == L->insts[i].raw.narm64);
                                CHECK(decoded->insts[i].raw.nx64 == L->insts[i].raw.nx64);
                        }
                        valid(decoded);
                        lir_free(decoded);
                }
                for (usize n = 0; n < bytes.count; ++n) {
                        decoded = lir_deserialize(bytes.items, n, bytes.holes, bytes.nholes, &err);
                        CHECK(decoded == NULL);
                        lir_free(decoded);
                }
                lir_bytes_free(&bytes);
                lir_free(L);
        }
}

static void
check_flow(void)
{
        LirType types[] = { LIR_TYPE_I64 };
        for (u32 defined = 0; defined < 2; ++defined) {
                Lir *L = function(LIR_TYPE_I64, types, 1, LIR_MODE_AUTO);
                LirReg x = lir_reg(L, LIR_I64);
                LirLabel left = lir_label(L);
                LirLabel join = lir_label(L);
                emit(L, LIR_BRZ, LIR_NONE, (LirOpnd[]) { lir_r(L->params[0]), lir_l(left) }, 2);
                emit(L, LIR_LI, x, (LirOpnd[]) { lir_i(2) }, 1);
                emit(L, LIR_JMP, LIR_NONE, (LirOpnd[]) { lir_l(join) }, 1);
                CHECK(lir_bind(L, left));
                if (defined) {
                        emit(L, LIR_LI, x, (LirOpnd[]) { lir_i(1) }, 1);
                }
                CHECK(lir_bind(L, join));
                ret(L, x);
                if (defined) {
                        valid(L);
                } else {
                        invalid(L, LIR_ERROR_UNDEFINED);
                }
                lir_free(L);
        }
        for (u32 defined = 0; defined < 2; ++defined) {
                Lir *L = function(LIR_TYPE_I64, types, 1, LIR_MODE_AUTO);
                LirReg x = lir_reg(L, LIR_I64);
                LirLabel loop = lir_label(L);
                if (defined) {
                        emit(L, LIR_LI, x, (LirOpnd[]) { lir_i(0) }, 1);
                }
                CHECK(lir_bind(L, loop));
                emit(L, LIR_ADD, x, (LirOpnd[]) { lir_r(x), lir_i(1) }, 2);
                emit(L, LIR_BR, LIR_NONE,
                     (LirOpnd[]) { lir_cc(LIR_LT), lir_r(x), lir_r(L->params[0]), lir_l(loop) }, 4);
                ret(L, x);
                if (defined) {
                        LirCFG cfg;
                        LirError err;
                        valid(L);
                        CHECK(lir_cfg(L, &cfg, &err));
                        CHECK(cfg.nblocks == 4);
                        CHECK(cfg.blocks[1].nsucc == 2);
                        CHECK(cfg.blocks[1].succ[0] == 1);
                        CHECK(!cfg.blocks[3].reachable);
                        lir_cfg_free(&cfg);
                } else {
                        invalid(L, LIR_ERROR_UNDEFINED);
                }
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        invalid(L, LIR_ERROR_RETURN);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        valid(L);
        lir_free(L);
        L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        LirLabel loop = lir_label(L);
        CHECK(lir_bind(L, loop));
        emit(L, LIR_JMP, LIR_NONE, (LirOpnd[]) { lir_l(loop) }, 1);
        valid(L);
        lir_free(L);
}

static void
check_entries(void)
{
        LirType types[] = { LIR_TYPE_PTR };
        for (u32 pinned = 0; pinned < 2; ++pinned) {
                Lir *L = function(LIR_TYPE_PTR, types, 1, LIR_MODE_AUTO);
                LirReg p = L->params[0];
                if (pinned) {
                        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
                        p = lir_pinned(L, LIR_PIN_0);
                        CHECK(p == lir_pinned(L, LIR_PIN_0));
                }
                ret(L, p);
                LirLabel entry = lir_label(L);
                CHECK(lir_entry(L, entry));
                ret(L, p);
                if (pinned) {
                        valid(L);
                } else {
                        invalid(L, LIR_ERROR_ENTRY);
                }
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        LirReg x = lir_reg(L, LIR_I64);
        emit(L, LIR_LI, x, (LirOpnd[]) { lir_i(1) }, 1);
        ret(L, x);
        CHECK(lir_entry(L, lir_label(L)));
        emit(L, LIR_LI, x, (LirOpnd[]) { lir_i(2) }, 1);
        ret(L, x);
        valid(L);
        lir_free(L);
}

static void
check_calls(void)
{
        LirType types[12];
        LirOpnd args[12];
        for (u32 n = 0; n <= 12; ++n) {
                for (u32 i = 0; i < n; ++i) {
                        types[i] = i % 2 ? LIR_TYPE_F64 : LIR_TYPE_I64;
                }
                Lir *L = function(LIR_TYPE_I64, types, n, LIR_MODE_AUTO);
                for (u32 i = 0; i < n; ++i) {
                        args[i] = lir_r(L->params[i]);
                }
                LirReg d = lir_reg(L, LIR_I64);
                LirInst in = {
                        .op = LIR_CALL, .dst = d,
                        .args = { lir_i(1) }, .nargs = 1,
                        .call_args = args, .ncall_args = n,
                        .sig = { .ret = LIR_TYPE_I64, .params = types, .nparams = n,
                                 .nfixed = n / 2, .variadic = true }
                };
                CHECK(lir_emit(L, &in));
                if (n != 0) {
                        types[0] = LIR_TYPE_F64;
                        args[0] = lir_i(0);
                        CHECK(L->insts[0].sig.params[0] == LIR_TYPE_I64);
                        CHECK(L->insts[0].call_args[0].kind == LIR_OPERAND_REG);
                }
                ret(L, d);
                valid(L);
                lir_free(L);
        }
        for (u32 pinned = 0; pinned < 2; ++pinned) {
                types[0] = LIR_TYPE_I64;
                Lir *L = function(LIR_TYPE_I64, types, 1, LIR_MODE_AUTO);
                LirReg r = L->params[0];
                LirReg d = lir_reg(L, LIR_I64);
                if (pinned) {
                        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
                        r = lir_pinned(L, LIR_PIN_0);
                }
                LirInst in = {
                        .op = LIR_CALL, .dst = d,
                        .args = { lir_i(1) }, .nargs = 1,
                        .sig = { .ret = LIR_TYPE_I64 },
                        .flags = LIR_RETURNS_TWICE
                };
                CHECK(lir_emit(L, &in));
                ret(L, r);
                if (pinned) {
                        valid(L);
                } else {
                        invalid(L, LIR_ERROR_RETURNS_TWICE);
                }
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        LirReg d = lir_reg(L, LIR_I64);
        LirInst in = {
                .op = LIR_CALL, .dst = d,
                .args = { lir_i(1) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_I64 },
                .flags = LIR_RETURNS_TWICE
        };
        CHECK(lir_emit(L, &in));
        ret(L, d);
        valid(L);
        lir_free(L);
}

static void
check_attached_calls(void)
{
        LirCode code = { .sig = { .ret = LIR_VOID }, .mode = LIR_MODE_ATTACHED };
        Lir *L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        LirInst call = { .op = LIR_CALL, .dst = LIR_NONE, .nargs = 1,
                         .args = { { .kind = LIR_OPERAND_CODE, .code = &code } },
                         .sig = code.sig };
        CHECK(lir_emit(L, &call));
        ret(L, LIR_NONE);
        invalid(L, LIR_ERROR_SIGNATURE);
        L->insts[0].flags = LIR_MAY_GC;
        valid(L);
        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
        L->mode = LIR_MODE_DETACHED;
        invalid(L, LIR_ERROR_MODE);
        lir_free(L);
}

static void
check_errors(void)
{
        Lir *L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        LirLabel label = lir_label(L);
        CHECK(lir_bind(L, label));
        CHECK(!lir_bind(L, label));
        invalid(L, LIR_ERROR_LABEL);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        lir_label(L);
        invalid(L, LIR_ERROR_LABEL);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        LirReg r = lir_reg(L, LIR_I64);
        emit(L, LIR_FADD, r, (LirOpnd[]) { lir_i(1), lir_i(2) }, 2);
        invalid(L, LIR_ERROR_CLASS);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        r = lir_reg(L, LIR_I64);
        emit(L, LIR_LD_I64, r, (LirOpnd[]) { lir_m(r, LIR_NONE, 1, 0) }, 1);
        invalid(L, LIR_ERROR_OPERAND);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        emit(L, LIR_RET, LIR_NONE, (LirOpnd[]) { lir_i(1) }, 1);
        invalid(L, LIR_ERROR_RETURN);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        label = lir_label(L);
        LirInst in = { .op = LIR_SWITCH, .dst = LIR_NONE,
                       .args = { lir_i(0), lir_l(label) }, .nargs = 2 };
        CHECK(lir_emit(L, &in));
        CHECK(lir_bind(L, label));
        invalid(L, LIR_ERROR_LABEL);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        emit(L, LIR_FENCE, LIR_NONE, (LirOpnd[]) { lir_i(0) }, 1);
        invalid(L, LIR_ERROR_OPERAND);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        r = lir_reg(L, LIR_I64);
        emit(L, LIR_MOV, r, (LirOpnd[]) { lir_r(LIR_NONE) }, 1);
        invalid(L, LIR_ERROR_OPERAND);
        lir_free(L);
        L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        r = lir_reg(L, LIR_I64);
        LirInst missing = { .op = LIR_RET, .dst = LIR_NONE,
                            .args = { lir_r(r) }, .nargs = 1,
                            .span = { .source = 9, .start = 123, .end = 130 } };
        CHECK(lir_emit(L, &missing));
        LirError err;
        CHECK(!lir_validate(L, &err));
        CHECK(err.kind == LIR_ERROR_UNDEFINED);
        CHECK(err.op == 0);
        CHECK(err.span.source == 9 && err.span.start == 123 && err.span.end == 130);
        lir_free(L);
        LirSig sig = { .ret = LIR_TYPE_I64, .nparams = 1 };
        CHECK(lir_new("bad", &sig, LIR_MODE_AUTO, &err) == NULL);
        CHECK(err.kind == LIR_ERROR_SIGNATURE);
        LirType value_type = LIR_TYPE_VAL;
        L = function(LIR_VOID, &value_type, 1, LIR_MODE_AUTO);
        valid(L);
        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
        lir_free(L);
        L = function(LIR_VOID, &value_type, 1, LIR_MODE_DETACHED);
        invalid(L, LIR_ERROR_MODE);
        lir_free(L);
}

static void
check_modes(void)
{
        for (LirMode mode = LIR_MODE_AUTO; mode <= LIR_MODE_ATTACHED; ++mode) {
                Lir *L = function(LIR_VOID, NULL, 0, mode);
                CHECK(lir_vslot(L) != LIR_NONE);
                CHECK(L->nvslots == 1);
                ret(L, LIR_NONE);
                if (mode == LIR_MODE_DETACHED) {
                        invalid(L, LIR_ERROR_MODE);
                } else {
                        valid(L);
                        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
                }
                lir_free(L);
        }
        Lir *L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        Value v = { .type = VALUE_NIL };
        LirReg p = lir_reg(L, LIR_PTR);
        LirOpnd c = lir_const(L, &v);
        CHECK(c.kind == LIR_OPERAND_CONST);
        CHECK(L->roots[0].type == VALUE_NIL);
        v.type = VALUE_INTEGER;
        CHECK(L->roots[0].type == VALUE_NIL);
        emit(L, LIR_MOV, p, &c, 1);
        ret(L, LIR_NONE);
        valid(L);
        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_DETACHED);
        CHECK(lir_reg(L, LIR_REF) != LIR_NONE);
        invalid(L, LIR_ERROR_MODE);
        lir_free(L);
        L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        LirReg r = lir_reg(L, LIR_I64);
        LirOpnd hole = lir_hole(LIR_HOLE_IMM, 3);
        emit(L, LIR_LI, r, &hole, 1);
        ret(L, r);
        valid(L);
        lir_free(L);
}

static void
check_growth(void)
{
        Lir *L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        for (u32 i = 0; i < 70000; ++i) {
                LirLabel label = lir_label(L);
                CHECK(label == i);
                CHECK(lir_bind(L, label));
        }
        for (u32 i = 0; i < 128; ++i) {
                LirClass cls = i % 2 ? LIR_F64 : LIR_I64;
                LirReg r = lir_reg(L, cls);
                LirOpnd arg = i % 2 ? lir_f(i) : lir_i(i);
                emit(L, i % 2 ? LIR_FLI : LIR_LI, r, &arg, 1);
        }
        ret(L, LIR_NONE);
        valid(L);
        CHECK(L->nlabels == 70000);
        CHECK(L->nregs == 128);
        lir_free(L);
}

static void
check_constraints(void)
{
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I64, LIR_TYPE_F64 };
        for (u32 bad = 0; bad < 2; ++bad) {
                Lir *L = function(LIR_VOID, types, countof(types), LIR_MODE_AUTO);
                LirReg r = lir_reg(L, LIR_I64);
                LirOpnd mem = lir_m(L->params[0], L->params[1], bad ? 3 : 8, INT32_MIN);
                emit(L, LIR_LD_I64, r, &mem, 1);
                ret(L, LIR_NONE);
                if (bad) {
                        invalid(L, LIR_ERROR_OPERAND);
                } else {
                        valid(L);
                }
                lir_free(L);
        }
        Lir *L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        LirReg p = lir_reg(L, LIR_PTR);
        emit(L, LIR_ALLOCA, p, (LirOpnd[]) { lir_i(16), lir_i(3) }, 2);
        invalid(L, LIR_ERROR_CLASS);
        lir_free(L);
        for (u32 flags = 0; flags < 2; ++flags) {
                L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
                LirHelper helper = {
                        .name = "test", .sig = { .ret = LIR_VOID },
                        .flags = LIR_MAY_GC | LIR_MAY_THROW
                };
                LirInst in = {
                        .op = LIR_CALL, .dst = LIR_NONE,
                        .args = { { .kind = LIR_OPERAND_HELPER, .helper = &helper } },
                        .nargs = 1, .sig = { .ret = LIR_VOID },
                        .flags = flags ? helper.flags : 0
                };
                CHECK(lir_emit(L, &in));
                ret(L, LIR_NONE);
                if (flags) {
                        valid(L);
                        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
                } else {
                        invalid(L, LIR_ERROR_SIGNATURE);
                }
                lir_free(L);
        }
        L = function(LIR_VOID, NULL, 0, LIR_MODE_DETACHED);
        LirInst gc_call = {
                .op = LIR_CALL, .dst = LIR_NONE,
                .args = { lir_i(1) }, .nargs = 1,
                .sig = { .ret = LIR_VOID }, .flags = LIR_MAY_GC
        };
        CHECK(lir_emit(L, &gc_call));
        invalid(L, LIR_ERROR_MODE);
        lir_free(L);
        L = function(LIR_VOID, types, countof(types), LIR_MODE_AUTO);
        CHECK(lir_pc_param(L, 0));
        CHECK(L->pc_param == 0);
        CHECK(!lir_pc_param(L, 1));
        invalid(L, LIR_ERROR_SIGNATURE);
        lir_free(L);
        L = function(LIR_VOID, types, countof(types), LIR_MODE_AUTO);
        CHECK(!lir_pin_param(L, LIR_PIN_0, 2));
        invalid(L, LIR_ERROR_CLASS);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        LirReg x = lir_reg(L, LIR_I64);
        LirRawBinding inputs[] = { { .phys = 0, .reg = x } };
        u32 words[] = { 0xd503201f };
        LirInst raw = {
                .op = LIR_RAW, .dst = LIR_NONE,
                .raw = { .arm64 = words, .narm64 = 1, .in = inputs, .nin = 1 }
        };
        CHECK(lir_emit(L, &raw));
        invalid(L, LIR_ERROR_UNDEFINED);
        lir_free(L);
        L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        x = lir_reg(L, LIR_I64);
        LirRawBinding outputs[] = { { .phys = 0, .reg = x } };
        raw.raw.in = NULL;
        raw.raw.nin = 0;
        raw.raw.out = outputs;
        raw.raw.nout = 1;
        CHECK(lir_emit(L, &raw));
        ret(L, x);
        valid(L);
        lir_free(L);
        LirError err;
        LirSig sig = { .ret = (LirType)-1 };
        CHECK(lir_new("bad", &sig, LIR_MODE_AUTO, &err) == NULL);
        CHECK(err.kind == LIR_ERROR_SIGNATURE);
}

static void
check_serialization(void)
{
        for (u32 i = 0; i < 2; ++i) {
                LirType type = i == 0 ? LIR_TYPE_F64 : LIR_TYPE_PTR;
                Lir *L = function(type, NULL, 0, LIR_MODE_AUTO);
                LirReg r = lir_reg(L, i == 0 ? LIR_F64 : LIR_PTR);
                LirOpnd hole = lir_hole(i == 0 ? LIR_HOLE_FIMM : LIR_HOLE_PTR, 0);
                emit(L, i == 0 ? LIR_FLI : LIR_LI, r, &hole, 1);
                ret(L, r);
                LirBytes bytes;
                LirError err;
                CHECK(lir_serialize(L, &bytes, &err));
                bytes.holes[0].operand = i == 0 ? lir_f(-0.0) : lir_i(0x12345678);
                Lir *decoded = lir_deserialize(bytes.items, bytes.count,
                                               bytes.holes, bytes.nholes, &err);
                CHECK(decoded != NULL);
                if (decoded != NULL) {
                        CHECK(decoded->insts[0].args[0].kind == bytes.holes[0].operand.kind);
                        CHECK(memcmp(&decoded->insts[0].args[0].imm,
                                     &bytes.holes[0].operand.imm, sizeof (i64)) == 0);
                        lir_free(decoded);
                }
                lir_bytes_free(&bytes);
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_I64, NULL, 0, LIR_MODE_AUTO);
        LirReg x = lir_reg(L, LIR_I64);
        LirOpnd hole = lir_hole(LIR_HOLE_IMM, 0);
        LirInst in = {
                .op = LIR_LI, .dst = x, .args = { hole }, .nargs = 1,
                .span = { .source = 7, .start = 11, .end = 17 }
        };
        CHECK(lir_emit(L, &in));
        ret(L, x);
        LirBytes bytes;
        LirError err;
        CHECK(lir_serialize(L, &bytes, &err));
        CHECK(bytes.ninputs == 1 && bytes.nholes == 1);
        Lir *decoded = lir_deserialize(bytes.items, bytes.count, NULL, 0, &err);
        CHECK(decoded == NULL);
        CHECK(err.kind == LIR_ERROR_ENCODING);
        bytes.holes[0].operand = lir_f(1.0);
        decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded == NULL);
        CHECK(err.op == 0 && err.span.source == 7 && err.span.start == 11);
        bytes.holes[0].operand = lir_i(INT64_MIN);
        decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded != NULL);
        if (decoded != NULL) {
                CHECK(decoded->insts[0].args[0].imm == INT64_MIN);
                valid(decoded);
                lir_free(decoded);
        }
        bytes.items[4] = 3;
        CHECK(lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err) == NULL);
        bytes.items[4] = 1;
        u8 *extra = malloc(bytes.count + 1);
        CHECK(extra != NULL);
        memcpy(extra, bytes.items, bytes.count);
        extra[bytes.count] = 0;
        CHECK(lir_deserialize(extra, bytes.count + 1, bytes.holes, bytes.nholes, &err) == NULL);
        free(extra);
        lir_bytes_free(&bytes);
        lir_free(L);
        L = function(LIR_TYPE_PTR, NULL, 0, LIR_MODE_AUTO);
        LirReg p = lir_reg(L, LIR_PTR);
        Value v = { .type = VALUE_INTEGER, .z = 12345 };
        LirOpnd c = lir_const(L, &v);
        emit(L, LIR_MOV, p, &c, 1);
        ret(L, p);
        CHECK(lir_serialize(L, &bytes, &err));
        CHECK(bytes.ninputs == 0 && bytes.nholes == 1);
        CHECK(bytes.holes[0].value->z == 12345);
        lir_free(L);
        decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded != NULL);
        lir_bytes_free(&bytes);
        if (decoded != NULL) {
                CHECK(decoded->nroots == 1 && decoded->roots[0].z == 12345);
                CHECK(decoded->resolved_mode == LIR_MODE_ATTACHED);
                lir_free(decoded);
        }
        L = function(LIR_TYPE_PTR, NULL, 0, LIR_MODE_AUTO);
        p = lir_reg(L, LIR_PTR);
        c = lir_hole(LIR_HOLE_CONST, 0);
        emit(L, LIR_MOV, p, &c, 1);
        ret(L, p);
        CHECK(lir_serialize(L, &bytes, &err));
        bytes.holes[0].value = &v;
        decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded != NULL);
        if (decoded != NULL) {
                CHECK(decoded->nroots == 1 && decoded->roots[0].z == v.z);
                CHECK(decoded->insts[0].args[0].kind == LIR_OPERAND_CONST);
                lir_free(decoded);
        }
        lir_bytes_free(&bytes);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        LirHelper helper = { .name = "test", .address = (void *)1, .sig = { .ret = LIR_VOID } };
        in = (LirInst) {
                .op = LIR_CALL, .dst = LIR_NONE,
                .args = { { .kind = LIR_OPERAND_HELPER, .helper = &helper } }, .nargs = 1,
                .sig = { .ret = LIR_VOID }, .flags = LIR_CALL_SITE, .tag = 417
        };
        CHECK(lir_emit(L, &in));
        ret(L, LIR_NONE);
        CHECK(lir_serialize(L, &bytes, &err));
        CHECK(bytes.nholes == 1 && bytes.holes[0].operand.helper == &helper);
        decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded != NULL);
        if (decoded != NULL) {
                CHECK(decoded->insts[0].args[0].helper == &helper);
                CHECK(decoded->insts[0].flags == LIR_CALL_SITE && decoded->insts[0].tag == 417);
                lir_free(decoded);
        }
        u64 seed = 0xcff70ba7651b193e;
        u8 *mutated = malloc(bytes.count);
        CHECK(mutated != NULL);
        for (u32 i = 0; i < 2000; ++i) {
                memcpy(mutated, bytes.items, bytes.count);
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                mutated[seed % bytes.count] ^= (seed >> 32) | 1;
                decoded = lir_deserialize(mutated, bytes.count, bytes.holes, bytes.nholes, &err);
                if (decoded != NULL) {
                        valid(decoded);
                        lir_free(decoded);
                } else {
                        CHECK(err.kind != LIR_ERROR_NONE);
                }
        }
        free(mutated);
        lir_bytes_free(&bytes);
        lir_free(L);
        L = function(LIR_VOID, NULL, 0, LIR_MODE_AUTO);
        in.args[0] = lir_hole(LIR_HOLE_CALLEE, 0);
        CHECK(lir_emit(L, &in));
        ret(L, LIR_NONE);
        CHECK(lir_serialize(L, &bytes, &err));
        bytes.holes[0].operand = (LirOpnd) { .kind = LIR_OPERAND_HELPER, .helper = &helper };
        decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded != NULL);
        if (decoded != NULL) {
                CHECK(decoded->insts[0].args[0].helper == &helper);
                lir_free(decoded);
        }
        helper.flags = LIR_MAY_GC;
        CHECK(lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err) == NULL);
        CHECK(err.kind == LIR_ERROR_SIGNATURE);
        lir_bytes_free(&bytes);
        lir_free(L);
}

static void
check_poll_metadata(void)
{
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        Lir *L = function(LIR_VOID, types, countof(types), LIR_MODE_ATTACHED);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
        CHECK(lir_pin_param(L, LIR_PIN_1, 1));
        LirLabel entry = lir_label(L);
        LirLabel end = lir_label(L);
        CHECK(lir_entry(L, entry));
        L->insts[L->ninsts - 1].tag = 37;
        LirInst in = {
                .op = LIR_POLL, .dst = LIR_NONE,
                .args = { lir_r(lir_pinned(L, LIR_PIN_0)),
                          lir_r(lir_pinned(L, LIR_PIN_1)), lir_i(0), lir_l(end) },
                .nargs = 4, .flags = LIR_CALL_SITE, .tag = 99
        };
        CHECK(lir_emit(L, &in));
        CHECK(lir_bind(L, end));
        ret(L, LIR_NONE);
        valid(L);
        LirBytes bytes;
        LirError err;
        CHECK(lir_serialize(L, &bytes, &err));
        CHECK(bytes.items[4] == 2);
        Lir *copy = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(copy != NULL);
        if (copy != NULL) {
                CHECK(copy->insts[0].tag == 37);
                CHECK(copy->insts[1].tag == 99 && copy->insts[1].flags == LIR_CALL_SITE);
                valid(copy);
                lir_free(copy);
        }
        L->insts[1].flags |= LIR_RETURNS_TWICE;
        invalid(L, LIR_ERROR_OPERAND);
        lir_bytes_free(&bytes);
        lir_free(L);
}

int
main(void)
{
        check_ops();
        check_flow();
        check_entries();
        check_calls();
        check_attached_calls();
        check_errors();
        check_modes();
        check_growth();
        check_constraints();
        check_serialization();
        check_poll_metadata();
        printf("LIR: %u checks, %u failures\n", checks, failures);
        return failures != 0;
}
