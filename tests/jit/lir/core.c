#include "test.h"

static void
valid(Lir *L)
{
        LirError err;
        bool     ok = lir_validate(ty, L, &err);

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

        CHECK(!lir_validate(ty, L, &err));
        CHECK(err.kind == kind);
        CHECK(err.message[0] != '\0');
}

static void
judge(Lir *L, bool ok, LirErrorKind kind)
{
        if (ok) {
                valid(L);
        } else {
                invalid(L, kind);
        }
}

static Lir *
decode(LirBytes const *bytes, LirError *err)
{
        return lir_deserialize(
                ty,
                bytes->items,
                bytes->count,
                bytes->holes,
                bytes->nholes,
                err
        );
}

static void
encode(Lir *L, LirBytes *bytes, LirError *err)
{
        CHECK(lir_serialize(ty, L, bytes, err));
}

typedef struct {
        LirLabel      targets[2];
        LirRawBinding in;
        LirRawBinding out;
} Payload;

static u8 const  Nop64[]  = { 0x90 };
static u32 const NopA64[] = { 0xd503201f };

static void
operands(Lir *L, LirOp op, LirInst *in, LirLabel target, Payload *pay)
{
        LirOpInfo const *info = &LirOps[op];
        LirReg           x    = L->params[0];
        LirReg           y    = L->params[1];
        LirReg           z    = L->params[2];
        LirReg           f    = L->params[3];
        LirReg           g    = L->params[4];
        LirReg           h    = L->params[5];
        LirReg           s    = L->params[6];
        LirReg           p    = L->params[7];
        LirOpnd          mem  = lir_m(p, x, 8, -16);

        *pay = (Payload) {
                .targets = { target, target },
                .in      = { .phys = 0, .reg = x },
                .out     = { .phys = 1, .reg = y }
        };

#define D(cls) (in->dst = lir_reg(L, (cls)))
#define A(...) memcpy(in->args, O(__VA_ARGS__), sizeof O(__VA_ARGS__))

        switch (info->form) {
        case LF_MOV:      D(LIR_I64); A(lir_r(x));                              break;
        case LF_LI:       D(LIR_I64); A(lir_i(INT64_MIN));                      break;
        case LF_FLI:      D(LIR_F64); A(lir_f(1.5));                            break;
        case LF_LEA:      D(LIR_PTR); A(mem);                                   break;
        case LF_IUNARY:   D(LIR_I64); A(lir_r(x));                              break;
        case LF_I2F:      D(LIR_F64); A(lir_r(x));                              break;
        case LF_FEXT:     D(LIR_F64); A(lir_r(s));                              break;
        case LF_FTRUNC:   D(LIR_F32); A(lir_r(f));                              break;
        case LF_ALLOCA:   D(LIR_PTR); A(lir_i(32), lir_i(16));                  break;
        case LF_CAS:
        case LF_ATOMIC:   D(LIR_I64); A(mem, lir_r(x), lir_r(y));               break;
        case LF_F2I:
        case LF_BITCAST:  D(LIR_I64); A(lir_r(f));                              break;
        case LF_IBINARY:
        case LF_CHECKED:  D(LIR_I64); A(lir_r(x), lir_r(y), lir_l(target));     break;
        case LF_FBINARY:
        case LF_FUNARY:
        case LF_FMA:      D(LIR_F64); A(lir_r(f), lir_r(g), lir_r(h));          break;
        case LF_LD:       D(lir_type_class(info->type)); A(mem);                break;
        case LF_COPY:     A(deref(p, 0), deref(p, 32));                         break;
        case LF_BRZ:      A(lir_r(x), lir_l(target));                           break;
        case LF_JMP:
        case LF_POLL:     A(lir_l(target));                                     break;
        case LF_SITE:     A(lir_i(UINT32_MAX));                                 break;
        case LF_RET:
        case LF_FENCE:
        case LF_ENTRY:                                                          break;

        case LF_ST:
                switch (info->type) {
                case LT_F32: A(mem, lir_r(s)); break;
                case LT_F64: A(mem, lir_r(f)); break;
                default:     A(mem, lir_r(x)); break;
                }
                break;

        case LF_SETCC:
        case LF_SELECT:
        case LF_BR:
                A(lir_cc(LIR_LT), lir_r(x), lir_r(y), lir_l(target));
                if (op != LIR_BR) {
                        D(LIR_I64);
                }
                if (op == LIR_SELECT) {
                        A(lir_cc(LIR_LT), lir_r(x), lir_r(y), lir_r(y), lir_r(z));
                }
                break;

        case LF_FSETCC:
        case LF_FSELECT:
        case LF_FBR:
                A(lir_cc(LIR_FUN), lir_r(f), lir_r(g), lir_l(target));
                if (op != LIR_FBR) {
                        D(LIR_I64);
                }
                if (op == LIR_FSELECT) {
                        A(lir_cc(LIR_FUN), lir_r(f), lir_r(g), lir_r(x), lir_r(y));
                }
                break;

        case LF_SWITCH:
                A(lir_r(x), lir_l(target));
                in->targets  = pay->targets;
                in->ntargets = countof(pay->targets);
                break;

        case LF_CALL:
        case LF_TAILCALL:
                A(lir_i(1));
                in->sig.ret = LT_VOID;
                break;

        case LF_RAW:
                in->raw = (LirRaw) {
                        .arm64       = NopA64,
                        .narm64      = countof(NopA64),
                        .x64         = Nop64,
                        .nx64        = countof(Nop64),
                        .in          = &pay->in,
                        .nin         = 1,
                        .out         = &pay->out,
                        .nout        = 1,
                        .gpr_clobber = 4
                };
                break;
        }

#undef A
#undef D
}

static void
same_shape(Lir const *a, Lir const *b)
{
        CHECK(vN(a->regs) == vN(b->regs));
        CHECK(vN(a->labels) == vN(b->labels));
        CHECK(vN(a->insts) == vN(b->insts));
        CHECK(a->mode == b->mode);

        for (u32 i = 0; i < vN(b->insts); ++i) {
                LirInst const *x = v_(a->insts, i);
                LirInst const *y = v_(b->insts, i);
#define SAME(f) CHECK(x->f == y->f)
                SAME(op);
                SAME(dst);
                SAME(nargs);
                SAME(ntargets);
                SAME(raw.narm64);
                SAME(raw.nx64);
#undef SAME
        }
}

static void
check_ops(void)
{
        for (LirOp op = 0; op < LIR_OP_COUNT; ++op) {
                Lir *L = fn(
                        LT_VOID,
                        LT_I64, LT_I64, LT_I64,
                        LT_F64, LT_F64, LT_F64,
                        LT_F32, LT_PTR
                );

                LirInst  in     = { .op = op, .dst = LIR_NONE, .nargs = LirOps[op].argc };
                Payload  pay;
                LirReg   w      = lir_reg(L, LIR_I32);
                LirLabel target = lir_label(L);

                put(L, LIR_LI, w, lir_i(3));
                operands(L, op, &in, target, &pay);

                if (op == LIR_ENTRY) {
                        CHECK(lir_entry(L, target));
                } else {
                        push(L, in);
                        here(L, target);
                }

                ret(L, LIR_NONE);
                valid(L);

                LirMode mode = (op == LIR_POLL) ? LIR_MODE_ATTACHED : LIR_MODE_DETACHED;
                CHECK(L->resolved_mode == mode);

                LirBytes bytes;
                LirError err;

                encode(L, &bytes, &err);

                Lir *decoded = decode(&bytes, &err);
                CHECK(decoded != NULL);

                if (decoded != NULL) {
                        same_shape(decoded, L);
                        valid(decoded);
                        lir_free(decoded);
                }

                for (usize n = 0; n < bytes.count; ++n) {
                        LirBytes cut = bytes;
                        cut.count = n;
                        decoded = decode(&cut, &err);
                        CHECK(decoded == NULL);
                        lir_free(decoded);
                }

                lir_free(L);
        }
}

static void
check_flow(void)
{
        for (u32 defined = 0; defined < 2; ++defined) {
                Lir     *L    = fn(LT_I64, LT_I64);
                LirReg   x    = lir_reg(L, LIR_I64);
                LirLabel left = lir_label(L);
                LirLabel join = lir_label(L);

                put(L, LIR_BRZ, LIR_NONE, lir_r(L->params[0]), lir_l(left));
                put(L, LIR_LI, x, lir_i(2));
                put(L, LIR_JMP, LIR_NONE, lir_l(join));
                here(L, left);

                if (defined) {
                        put(L, LIR_LI, x, lir_i(1));
                }

                here(L, join);
                ret(L, x);
                judge(L, defined, LE_UNDEFINED);

                lir_free(L);
        }

        for (u32 defined = 0; defined < 2; ++defined) {
                Lir     *L   = fn(LT_I64, LT_I64);
                LirReg   x   = lir_reg(L, LIR_I64);
                LirLabel top = lir_label(L);

                if (defined) {
                        put(L, LIR_LI, x, lir_i(0));
                }

                LirOpnd n = lir_r(L->params[0]);

                here(L, top);
                put(L, LIR_ADD, x, lir_r(x), lir_i(1));
                put(L, LIR_BR, LIR_NONE, lir_cc(LIR_LT), lir_r(x), n, lir_l(top));
                ret(L, x);

                if (!defined) {
                        invalid(L, LE_UNDEFINED);
                        lir_free(L);
                        continue;
                }

                valid(L);

                WITH_SCRATCH {
                        LirCFG   cfg;
                        LirError err;
                        CHECK(lir_cfg(ty, L, &cfg, &err));
                        CHECK(cfg.nblocks == 4);
                        CHECK(cfg.blocks[1].nsucc == 2);
                        CHECK(cfg.blocks[1].succ[0] == 1);
                        CHECK(!cfg.blocks[3].reachable);
                }

                lir_free(L);
        }

        Lir *L = fn(LT_I64);
        invalid(L, LE_RETURN);
        lir_free(L);

        L = fn(LT_VOID);
        valid(L);
        lir_free(L);

        L = fn(LT_I64);

        LirLabel top = lir_label(L);

        here(L, top);
        put(L, LIR_JMP, LIR_NONE, lir_l(top));
        valid(L);

        lir_free(L);
}

static void
check_entries(void)
{
        for (u32 pinned = 0; pinned < 2; ++pinned) {
                Lir   *L = fn(LT_PTR, LT_PTR);
                LirReg p = L->params[0];

                if (pinned) {
                        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
                        p = lir_pinned(L, LIR_PIN_0);
                        CHECK(p == lir_pinned(L, LIR_PIN_0));
                }

                ret(L, p);
                CHECK(lir_entry(L, lir_label(L)));
                ret(L, p);
                judge(L, pinned, LE_ENTRY);

                lir_free(L);
        }

        Lir   *L = fn(LT_I64);
        LirReg x = lir_reg(L, LIR_I64);

        put(L, LIR_LI, x, lir_i(1));
        ret(L, x);
        CHECK(lir_entry(L, lir_label(L)));
        put(L, LIR_LI, x, lir_i(2));
        ret(L, x);
        valid(L);

        lir_free(L);
}

static LirInst
twice(LirReg d)
{
        LirInst in = call(lir_i(1), d, sig(LT_I64, NULL, 0), NULL);

        in.flags = LIR_RETURNS_TWICE;

        return in;
}

static void
check_calls(void)
{
        LirType types[12];
        LirOpnd args[12];

        for (u32 n = 0; n <= 12; ++n) {
                for (u32 i = 0; i < n; ++i) {
                        types[i] = (i % 2) ? LT_F64 : LT_I64;
                }

                Lir *L = build(LT_I64, types, n, LIR_MODE_AUTO);

                for (u32 i = 0; i < n; ++i) {
                        args[i] = lir_r(L->params[i]);
                }

                LirReg d = lir_reg(L, LIR_I64);

                push(L, call(lir_i(1), d, vsig(LT_I64, types, n, n / 2), args));

                if (n != 0) {
                        types[0] = LT_F64;
                        args[0]  = lir_i(0);
                        CHECK(v__(L->insts, 0).sig.params[0] == LT_I64);
                        CHECK(v__(L->insts, 0).call_args[0].kind == LO_REG);
                }

                ret(L, d);
                valid(L);

                lir_free(L);
        }

        for (u32 pinned = 0; pinned < 2; ++pinned) {
                Lir   *L = fn(LT_I64, LT_I64);
                LirReg r = L->params[0];
                LirReg d = lir_reg(L, LIR_I64);

                if (pinned) {
                        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
                        r = lir_pinned(L, LIR_PIN_0);
                }

                push(L, twice(d));
                ret(L, r);
                judge(L, pinned, LE_RETURNS_TWICE);

                lir_free(L);
        }

        Lir   *L = fn(LT_I64);
        LirReg d = lir_reg(L, LIR_I64);

        push(L, twice(d));
        ret(L, d);
        valid(L);

        lir_free(L);
}

static void
check_attached_calls(void)
{
        LirCode code = { .sig = { .ret = LT_VOID }, .mode = LIR_MODE_ATTACHED };
        LirOpnd body = { .kind = LO_CODE, .code = &code };
        Lir    *L    = fn(LT_VOID);

        push(L, call(body, LIR_NONE, code.sig, NULL));
        ret(L, LIR_NONE);
        invalid(L, LE_SIGNATURE);

        v_(L->insts, 0)->flags = LIR_MAY_GC;
        valid(L);
        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);

        L->mode = LIR_MODE_DETACHED;
        invalid(L, LE_MODE);

        lir_free(L);
}

static void
rebound(Lir *L)
{
        LirLabel label = lir_label(L);

        here(L, label);
        CHECK(!lir_bind(L, label));
}

static void
unbound(Lir *L)
{
        lir_label(L);
}

static void
int_fadd(Lir *L)
{
        put(L, LIR_FADD, lir_reg(L, LIR_I64), lir_i(1), lir_i(2));
}

static void
int_base(Lir *L)
{
        LirReg r = lir_reg(L, LIR_I64);
        put(L, LIR_LD_I64, r, deref(r, 0));
}

static void
void_value(Lir *L)
{
        put(L, LIR_RET, LIR_NONE, lir_i(1));
}

static void
empty_switch(Lir *L)
{
        LirLabel label = lir_label(L);

        push(L, jump_table(lir_i(0), label, NULL, 0));
        here(L, label);
}

static void
fence_operand(Lir *L)
{
        put(L, LIR_FENCE, LIR_NONE, lir_i(0));
}

static void
no_source(Lir *L)
{
        put(L, LIR_MOV, lir_reg(L, LIR_I64), lir_r(LIR_NONE));
}

static void
odd_align(Lir *L)
{
        put(L, LIR_ALLOCA, lir_reg(L, LIR_PTR), lir_i(16), lir_i(3));
}

static void
detached_gc(Lir *L)
{
        LirInst in = vcall(lir_i(1));

        in.flags = LIR_MAY_GC;
        push(L, in);
}

static void
check_errors(void)
{
        static struct {
                void       (*build)(Lir *);
                LirMode      mode;
                LirErrorKind kind;
        } const cases[] = {
                { rebound,       LIR_MODE_AUTO,     LE_LABEL   },
                { unbound,       LIR_MODE_AUTO,     LE_LABEL   },
                { int_fadd,      LIR_MODE_AUTO,     LE_CLASS   },
                { int_base,      LIR_MODE_AUTO,     LE_OPERAND },
                { void_value,    LIR_MODE_AUTO,     LE_RETURN  },
                { empty_switch,  LIR_MODE_AUTO,     LE_LABEL   },
                { fence_operand, LIR_MODE_AUTO,     LE_OPERAND },
                { no_source,     LIR_MODE_AUTO,     LE_OPERAND },
                { odd_align,     LIR_MODE_AUTO,     LE_CLASS   },
                { detached_gc,   LIR_MODE_DETACHED, LE_MODE    }
        };

        for (u32 i = 0; i < countof(cases); ++i) {
                Lir *L = fnm(cases[i].mode, LT_VOID);
                cases[i].build(L);
                invalid(L, cases[i].kind);
                lir_free(L);
        }

        Lir   *L = fn(LT_I64);
        LirReg r = lir_reg(L, LIR_I64);

        push(L, (LirInst) {
                .op    = LIR_RET,
                .dst   = LIR_NONE,
                .args  = { lir_r(r) },
                .nargs = 1,
                .span  = { .source = 9, .start = 123, .end = 130 }
        });

        LirError err;

        CHECK(!lir_validate(ty, L, &err));
        CHECK(err.kind == LE_UNDEFINED);
        CHECK(err.op == 0);
        CHECK(err.span.source == 9 && err.span.start == 123 && err.span.end == 130);

        lir_free(L);

        LirSig bad = { .ret = LT_I64, .nparams = 1 };

        CHECK(lir_new("bad", &bad, LIR_MODE_AUTO, &err) == NULL);
        CHECK(err.kind == LE_SIGNATURE);

        L = fn(LT_VOID, LT_VAL);
        valid(L);
        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
        lir_free(L);

        L = fnm(LIR_MODE_DETACHED, LT_VOID, LT_VAL);
        invalid(L, LE_MODE);
        lir_free(L);
}

static void
check_modes(void)
{
        for (LirMode mode = LIR_MODE_AUTO; mode <= LIR_MODE_ATTACHED; ++mode) {
                Lir *L = fnm(mode, LT_VOID);

                CHECK(lir_vslot(L) != LIR_NONE);
                CHECK(L->nvslots == 1);
                ret(L, LIR_NONE);

                if (mode == LIR_MODE_DETACHED) {
                        invalid(L, LE_MODE);
                } else {
                        valid(L);
                        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
                }

                lir_free(L);
        }

        Lir    *L = fn(LT_VOID);
        Value   v = { .type = VALUE_NIL };
        LirReg  p = lir_reg(L, LIR_PTR);
        LirOpnd c = lir_const(L, &v);

        CHECK(c.kind == LO_CONST);
        CHECK(v__(L->roots, 0).type == VALUE_NIL);

        v.type = VALUE_INTEGER;
        CHECK(v__(L->roots, 0).type == VALUE_NIL);

        put(L, LIR_MOV, p, c);
        ret(L, LIR_NONE);
        valid(L);
        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);

        lir_free(L);

        L = fnm(LIR_MODE_DETACHED, LT_VOID);
        CHECK(lir_reg(L, LIR_REF) != LIR_NONE);
        invalid(L, LE_MODE);
        lir_free(L);

        L = fn(LT_I64);

        LirReg r = lir_reg(L, LIR_I64);

        put(L, LIR_LI, r, lir_hole(LO_HOLE_IMM, 3));
        ret(L, r);
        valid(L);

        lir_free(L);
}

static void
check_growth(void)
{
        Lir *L = fn(LT_VOID);

        for (u32 i = 0; i < 70000; ++i) {
                LirLabel label = lir_label(L);
                CHECK(label == i);
                here(L, label);
        }

        for (u32 i = 0; i < 128; ++i) {
                bool odd = i % 2;
                put(
                        L,
                        odd ? LIR_FLI : LIR_LI,
                        lir_reg(L, odd ? LIR_F64 : LIR_I64),
                        odd ? lir_f(i) : lir_i(i)
                );
        }

        ret(L, LIR_NONE);
        valid(L);
        CHECK(vN(L->labels) == 70000);
        CHECK(vN(L->regs) == 128);

        lir_free(L);
}

static LirInst
raw(u32 *words, LirRawBinding *in, u32 nin, LirRawBinding *out, u32 nout)
{
        return (LirInst) {
                .op  = LIR_RAW,
                .dst = LIR_NONE,
                .raw = {
                        .arm64  = words,
                        .narm64 = 1,
                        .in     = in,
                        .nin    = nin,
                        .out    = out,
                        .nout   = nout
                }
        };
}

static void
check_constraints(void)
{
        for (u32 bad = 0; bad < 2; ++bad) {
                Lir    *L   = fn(LT_VOID, LT_PTR, LT_I64, LT_F64);
                LirReg  r   = lir_reg(L, LIR_I64);
                LirOpnd mem = lir_m(L->params[0], L->params[1], bad ? 3 : 8, INT32_MIN);

                put(L, LIR_LD_I64, r, mem);
                ret(L, LIR_NONE);
                judge(L, !bad, LE_OPERAND);

                lir_free(L);
        }

        for (u32 flags = 0; flags < 2; ++flags) {
                Lir      *L      = fn(LT_VOID);
                LirHelper helper = {
                        .name  = "test",
                        .sig   = { .ret = LT_VOID },
                        .flags = LIR_MAY_GC | LIR_MAY_THROW
                };
                LirOpnd   target = { .kind = LO_HELPER, .helper = &helper };
                LirInst   in     = vcall(target);

                in.flags = flags ? helper.flags : 0;
                push(L, in);
                ret(L, LIR_NONE);
                judge(L, flags, LE_SIGNATURE);

                if (flags) {
                        CHECK(L->resolved_mode == LIR_MODE_ATTACHED);
                }

                lir_free(L);
        }

        Lir *L = fn(LT_VOID, LT_PTR, LT_I64, LT_F64);

        CHECK(lir_pc_param(L, 0));
        CHECK(L->pc_param == 0);
        CHECK(!lir_pc_param(L, 1));
        invalid(L, LE_SIGNATURE);

        lir_free(L);

        L = fn(LT_VOID, LT_PTR, LT_I64, LT_F64);
        CHECK(!lir_pin_param(L, LIR_PIN_0, 2));
        invalid(L, LE_CLASS);
        lir_free(L);

        u32 nop[] = { 0xd503201f };

        L = fn(LT_VOID);

        LirRawBinding input = { .phys = 0, .reg = lir_reg(L, LIR_I64) };

        push(L, raw(nop, &input, 1, NULL, 0));
        invalid(L, LE_UNDEFINED);

        lir_free(L);

        L = fn(LT_I64);

        LirReg        x      = lir_reg(L, LIR_I64);
        LirRawBinding output = { .phys = 0, .reg = x };

        push(L, raw(nop, NULL, 0, &output, 1));
        ret(L, x);
        valid(L);

        lir_free(L);

        LirError err;
        LirSig   bad = { .ret = (LirType)-1 };

        CHECK(lir_new("bad", &bad, LIR_MODE_AUTO, &err) == NULL);
        CHECK(err.kind == LE_SIGNATURE);
}

static Lir *
returns(LirType type, LirOp op, LirOpnd x)
{
        Lir   *L = fn(type);
        LirReg r = lir_reg(L, lir_type_class(type));

        put(L, op, r, x);
        ret(L, r);

        return L;
}

static void
check_fills(void)
{
        for (u32 i = 0; i < 2; ++i) {
                bool     f = (i == 0);
                LirBytes bytes;
                LirError err;
                Lir     *L = f
                           ? returns(LT_F64, LIR_FLI, lir_hole(LO_HOLE_FIMM, 0))
                           : returns(LT_PTR, LIR_LI, lir_hole(LO_HOLE_PTR, 0));

                encode(L, &bytes, &err);

                LirOpnd fill = f ? lir_f(-0.0) : lir_i(0x12345678);
                bytes.holes[0].operand = fill;

                Lir *decoded = decode(&bytes, &err);
                CHECK(decoded != NULL);

                if (decoded != NULL) {
                        LirOpnd got = v__(decoded->insts, 0).args[0];
                        CHECK(got.kind == fill.kind);
                        CHECK(memcmp(&got.imm, &fill.imm, sizeof (i64)) == 0);
                        lir_free(decoded);
                }

                lir_free(L);
        }
}

static void
check_inputs(void)
{
        Lir     *L = fn(LT_I64);
        LirReg   x = lir_reg(L, LIR_I64);
        LirBytes bytes;
        LirError err;

        push(L, (LirInst) {
                .op    = LIR_LI,
                .dst   = x,
                .args  = { lir_hole(LO_HOLE_IMM, 0) },
                .nargs = 1,
                .span  = { .source = 7, .start = 11, .end = 17 }
        });
        ret(L, x);

        encode(L, &bytes, &err);
        CHECK(bytes.ninputs == 1 && bytes.nholes == 1);

        CHECK(lir_deserialize(ty, bytes.items, bytes.count, NULL, 0, &err) == NULL);
        CHECK(err.kind == LE_ENCODING);

        bytes.holes[0].operand = lir_f(1.0);
        CHECK(decode(&bytes, &err) == NULL);
        CHECK(err.op == 0 && err.span.source == 7 && err.span.start == 11);

        bytes.holes[0].operand = lir_i(INT64_MIN);

        Lir *decoded = decode(&bytes, &err);
        CHECK(decoded != NULL);

        if (decoded != NULL) {
                CHECK(v__(decoded->insts, 0).args[0].imm == INT64_MIN);
                valid(decoded);
                lir_free(decoded);
        }

        bytes.items[4] = 5;
        CHECK(decode(&bytes, &err) == NULL);
        bytes.items[4] = 1;

        u8 *extra = xmA(bytes.count + 1);

        memcpy(extra, bytes.items, bytes.count);
        extra[bytes.count] = 0;

        LirBytes longer = bytes;
        longer.items  = extra;
        longer.count += 1;
        CHECK(decode(&longer, &err) == NULL);

        xmF(extra);
        lir_free(L);
}

static void
check_constants(void)
{
        LirBytes bytes;
        LirError err;
        Value    v = { .type = VALUE_INTEGER, .z = 12345 };
        Lir     *L = fn(LT_PTR);
        LirReg   p = lir_reg(L, LIR_PTR);

        put(L, LIR_MOV, p, lir_const(L, &v));
        ret(L, p);

        encode(L, &bytes, &err);
        CHECK(bytes.ninputs == 0 && bytes.nholes == 1);
        CHECK(bytes.holes[0].value->z == 12345);
        lir_free(L);

        Lir *decoded = decode(&bytes, &err);
        CHECK(decoded != NULL);

        if (decoded != NULL) {
                CHECK(vN(decoded->roots) == 1 && v__(decoded->roots, 0).z == 12345);
                CHECK(decoded->resolved_mode == LIR_MODE_ATTACHED);
                lir_free(decoded);
        }

        L = returns(LT_PTR, LIR_MOV, lir_hole(LO_HOLE_CONST, 0));

        encode(L, &bytes, &err);
        bytes.holes[0].value = &v;

        decoded = decode(&bytes, &err);
        CHECK(decoded != NULL);

        if (decoded != NULL) {
                CHECK(vN(decoded->roots) == 1 && v__(decoded->roots, 0).z == v.z);
                CHECK(v__(decoded->insts, 0).args[0].kind == LO_CONST);
                lir_free(decoded);
        }

        lir_free(L);
}

static void
mutate(LirBytes const *bytes)
{
        u64      seed    = 0xcff70ba7651b193e;
        u8      *mutated = xmA(bytes->count);
        LirBytes copy    = *bytes;
        LirError err;

        copy.items = mutated;

        for (u32 i = 0; i < 2000; ++i) {
                memcpy(mutated, bytes->items, bytes->count);

                u64 bits = xorshift(&seed);
                mutated[bits % bytes->count] ^= (bits >> 32) | 1;

                Lir *decoded = decode(&copy, &err);

                if (decoded != NULL) {
                        valid(decoded);
                        lir_free(decoded);
                } else {
                        CHECK(err.kind != LE_NONE);
                }
        }

        xmF(mutated);
}

static void
check_helpers(void)
{
        LirBytes  bytes;
        LirError  err;
        LirHelper helper = {
                .name    = "test",
                .address = (void *)1,
                .sig     = { .ret = LT_VOID }
        };
        LirOpnd   target = { .kind = LO_HELPER, .helper = &helper };
        LirInst   in     = vcall(target);
        Lir      *L      = fn(LT_VOID);

        in.flags = LIR_CALL_SITE;
        in.tag   = 417;

        push(L, in);
        ret(L, LIR_NONE);

        encode(L, &bytes, &err);
        CHECK(bytes.nholes == 1 && bytes.holes[0].operand.helper == &helper);

        Lir *decoded = decode(&bytes, &err);
        CHECK(decoded != NULL);

        if (decoded != NULL) {
                LirInst const *got = v_(decoded->insts, 0);
                CHECK(got->args[0].helper == &helper);
                CHECK(got->flags == LIR_CALL_SITE && got->tag == 417);
                lir_free(decoded);
        }

        mutate(&bytes);

        lir_free(L);

        L = fn(LT_VOID);
        in.args[0] = lir_hole(LO_HOLE_CALLEE, 0);

        push(L, in);
        ret(L, LIR_NONE);

        encode(L, &bytes, &err);
        bytes.holes[0].operand = target;

        decoded = decode(&bytes, &err);
        CHECK(decoded != NULL);

        if (decoded != NULL) {
                CHECK(v__(decoded->insts, 0).args[0].helper == &helper);
                lir_free(decoded);
        }

        helper.flags = LIR_MAY_GC;
        CHECK(decode(&bytes, &err) == NULL);
        CHECK(err.kind == LE_SIGNATURE);

        lir_free(L);
}

static void
check_serialization(void)
{
        check_fills();
        check_inputs();
        check_constants();
        check_helpers();
}

static void
check_poll_metadata(void)
{
        Lir *L = fnm(LIR_MODE_ATTACHED, LT_VOID, LT_PTR, LT_PTR);

        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
        CHECK(lir_pin_param(L, LIR_PIN_1, 1));

        LirLabel entry = lir_label(L);
        LirLabel end   = lir_label(L);

        CHECK(lir_entry(L, entry));
        v_L(L->insts).tag = 37;

        push(L, (LirInst) {
                .op    = LIR_POLL,
                .dst   = LIR_NONE,
                .args  = {
                        lir_r(lir_pinned(L, LIR_PIN_0)),
                        lir_r(lir_pinned(L, LIR_PIN_1)),
                        lir_i(0),
                        lir_l(end)
                },
                .nargs = 4,
                .flags = LIR_CALL_SITE,
                .tag   = 99
        });
        here(L, end);
        ret(L, LIR_NONE);
        valid(L);

        LirBytes bytes;
        LirError err;

        encode(L, &bytes, &err);
        CHECK(bytes.items[4] == 2);

        Lir *copy = decode(&bytes, &err);
        CHECK(copy != NULL);

        if (copy != NULL) {
                LirInst const *poll = v_(copy->insts, 1);
                CHECK(v__(copy->insts, 0).tag == 37);
                CHECK(poll->tag == 99 && poll->flags == LIR_CALL_SITE);
                valid(copy);
                lir_free(copy);
        }

        v_(L->insts, 1)->flags |= LIR_RETURNS_TWICE;
        invalid(L, LE_OPERAND);

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

        return report("LIR");
}
