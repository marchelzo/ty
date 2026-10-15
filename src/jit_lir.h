typedef struct bc_lir_node {
        i32 next;
        i32 target;
        i32 sp;
        i32 fall_sp;
        i32 saved;
        i32 sentinel;
        i32 sentinel_sp;
        i32 owner;
        i32 outer;
        i32 catch_to;
        i32 finally_to;
        i32 end_to;
        LirLabel label;
        LirLabel deopt;
        LirLabel resume;
        u32 resume_id;
        LirLabel osr;
        u32 osr_id;
        i32 argc;
        i32 global;
        i32 nkw;
        i32 member;
        char const *kw_ip;
        u8 op;
        bool branch;
} BcLirNode;

typedef struct bc_slot {
        u8 kind;
        LirReg r;
        u64 bits;
        T2Type hint;
} BcSlot;

typedef struct bc_loop {
        i32 head;
        i32 end;
        i32 sp;
        LirLabel deopt;
        i32 slots[8];
        i32 nslots;
        u8 *live;
        i32 owned[8];
        u8 owned_bit[8];
        LirReg owned_reg[8];
        i32 nowned;
        bool stack;
        LirReg sreg[2];
} BcLoop;

typedef struct bc_lir {
        Lir *L;
        LirReg ty;
        LirReg locals;
        LirReg env;
        LirReg fp;
        LirReg ops;
        LirLabel deopt;
        BcLirNode *nodes;
        i32 size;
        i32 sp;
        i32 bound;
        i32 max_sp;
        i32 self_index;
        u32 nresume;
        u32 nosr;
        u32 offset;
        i32 at;
        bool ok;
        bool dynamic;
        bool has_try;
        bool compact;
        i32 *tier;
        BcSlot *known;
        u32 *known_gen;
        u32 gen;
        i32 tuple_off;
        i32 tuple_sp;
        i32 tuple_min;
        BcLoop *loops;
        i32 nloops;
        LirReg *lreg;
        LirReg *spin;
        i32 *active;
        i32 nactive;
        i32 saved;
        i32 sentinel;
        i32 sentinel_sp;
        char const *code;
        u32 last_call;
        Ty *ctx;
        Value const *function;
        BcSlot *vs;
        i32 *local_class;
        T2Type *local_type;
        TypeHintVector const *hints;
        bool speculate;
        bool skip_next;
        LirReg base_index;
} BcLir;

static bool
bc_method_fast(BcLir *c, BcLirNode const *node);

static i32
bc_prepare_call(Ty *ty, Value *out, Value *fn, i32 argc);

static void
bc_sync_call(Ty *ty, Value *out, Value *fn, i32 argc);

static void
bc_native_call(BcLir *c, LirOpnd *enter_args);

static void
bc_native_invoke(BcLir *c, LirReg frame, LirReg out);

static Frame *
bc_method_enter(Ty *ty, Value *top, i32 op, i32 member, i32 argc, char *kw_ip);

static void
bc_inline_call(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirReg self,
               LirLabel miss, LirLabel done);

static bool
bc_inline_method(BcLir *c, BcLirNode const *node, LirLabel *done);

static bool
bc_builtin_call(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirLabel miss, LirLabel done);

static bool
bc_inline_ctor(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirLabel *ready);

static bool
bc_try_plan(BcLir *c, Value const *callee, TyInlineKind kind, i32 argc, i32 base, LirReg self,
            Class *self_class, Class **arg_classes, i32 out, LirLabel done);

static LirReg
bc_call(BcLir *c, void *helper, LirType ret, LirType const *types,
        LirOpnd *args, u32 n);

static LirReg
bc_call_flags(BcLir *c, void *helper, LirType ret, LirType const *types,
              LirOpnd *args, u32 n, u32 flags);

static void
bc_state(BcLir *c, BcLirNode const *node, char const *ip);

static LirOpnd
bc_deopt_info(BcLir *c);

static bool
bc_loop_lower(BcLir *c, BcLirNode const *node, char const *ip);

static LirReg
bc_loop_reg(BcLir const *c, i32 slot);

static bool
bc_loop_pinned(BcLir const *c, i32 pos);

static LirReg
bc_value(BcLir *c, LirOp op, LirClass cls, LirOpnd const *args, u32 n)
{
        LirReg r = lir_reg(c->L, cls);
        c->ok = c->ok && r != LIR_NONE && lir_emit_to(c->L, op, r, args, n);
        return r;
}

static void
bc_effect(BcLir *c, LirOp op, LirOpnd const *args, u32 n)
{
        c->ok = c->ok && lir_emit_to(c->L, op, LIR_NONE, args, n);
}

static LirReg
bc_addr(BcLir *c, LirReg base, i32 disp)
{
        LirOpnd mem = lir_m(base, LIR_NONE, 1, disp);
        return bc_value(c, LIR_LEA, LIR_PTR, &mem, 1);
}

static LirReg
bc_load(BcLir *c, LirOp op, LirClass cls, LirReg base, i32 disp)
{
        LirOpnd mem = lir_m(base, LIR_NONE, 1, disp);
        return bc_value(c, op, cls, &mem, 1);
}

static void
bc_store(BcLir *c, LirOp op, LirReg base, i32 disp, LirOpnd value)
{
        LirOpnd args[] = { lir_m(base, LIR_NONE, 1, disp), value };
        bc_effect(c, op, args, countof(args));
}

static void
bc_value_copy(BcLir *c, LirReg dst, i32 di, LirReg src, i32 si)
{
        LirOpnd args[] = { lir_m(dst, LIR_NONE, 1, di), lir_m(src, LIR_NONE, 1, si) };
        bc_effect(c, LIR_COPY32, args, countof(args));
}

#include "jit_lir_local.h"

static void
bc_literal(BcLir *c, i32 type, u64 bits)
{
        i32 off = c->sp++ * sizeof (Value);
        for (u32 i = 0; i < sizeof (Value); i += 8) {
                bc_store(c, LIR_ST64, c->ops, off + i, lir_i(0));
        }
        bc_store(c, LIR_ST8, c->ops, off + offsetof(Value, type), lir_i(type));
        bc_store(c, LIR_ST64, c->ops, off + offsetof(Value, z), lir_i(bits));
}

static void
bc_branch(BcLir *c, LirCC cc, LirOpnd a, LirOpnd b, LirLabel target)
{
        LirOpnd args[] = { lir_cc(cc), a, b, lir_l(target) };
        bc_effect(c, LIR_BR, args, countof(args));
}

static void
bc_bind(BcLir *c, LirLabel label)
{
        c->ok = c->ok && lir_bind(c->L, label);
}

static void
bc_jump(BcLir *c, LirLabel label)
{
        LirOpnd arg = lir_l(label);
        bc_effect(c, LIR_JMP, &arg, 1);
}

static void
bc_numeric(BcLir *c, u8 op)
{
        i32 left = (c->sp - 2) * sizeof (Value);
        i32 right = left + sizeof (Value);
        LirLabel floats = lir_label(c->L);
        LirLabel slow = lir_label(c->L);
        LirLabel end = lir_label(c->L);
        LirReg at = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, left + offsetof(Value, type));
        LirReg bt = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, right + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_INTEGER), floats);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_INTEGER), floats);
        LirReg a = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, left + offsetof(Value, z));
        LirReg b = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, right + offsetof(Value, z));
        LirOp iop = LIR_SETCC;
        LirOp fop = LIR_FSETCC;
        LirCC icc = LIR_EQ;
        LirCC fcc = LIR_FEQ;
        bool cmp = true;
        void *helper;
        switch (op) {
        case INSTR_ADD: iop = LIR_ADD; fop = LIR_FADD; helper = jit_rt_add; cmp = false; break;
        case INSTR_SUB: iop = LIR_SUB; fop = LIR_FSUB; helper = jit_rt_sub; cmp = false; break;
        case INSTR_MUL: iop = LIR_MUL; fop = LIR_FMUL; helper = jit_rt_mul; cmp = false; break;
        case INSTR_EQ:  icc = LIR_EQ; fcc = LIR_FEQ; helper = jit_rt_eq; break;
        case INSTR_NEQ: icc = LIR_NE; fcc = LIR_FNE; helper = jit_rt_ne; break;
        case INSTR_LT:  icc = LIR_LT; fcc = LIR_FLT; helper = jit_rt_lt; break;
        case INSTR_GT:  icc = LIR_GT; fcc = LIR_FGT; helper = jit_rt_gt; break;
        case INSTR_LEQ: icc = LIR_LE; fcc = LIR_FLE; helper = jit_rt_le; break;
        default:       icc = LIR_GE; fcc = LIR_FGE; helper = jit_rt_ge; break;
        }
        LirOpnd args[] = { lir_r(a), lir_r(b) };
        LirOpnd compare[] = { lir_cc(icc), lir_r(a), lir_r(b) };
        LirReg d = bc_value(c, iop, LIR_I64, cmp ? compare : args, cmp ? 3 : 2);
        if (cmp) {
                for (u32 i = 0; i < sizeof (Value); i += 8) {
                        bc_store(c, LIR_ST64, c->ops, left + i, lir_i(0));
                }
                bc_store(c, LIR_ST8, c->ops, left + offsetof(Value, type), lir_i(VALUE_BOOLEAN));
        }
        bc_store(c, LIR_ST64, c->ops, left + offsetof(Value, z), lir_r(d));
        bc_jump(c, end);
        bc_bind(c, floats);
        if (c->compact || op == INSTR_EQ || op == INSTR_NEQ) {
                bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_REAL), slow);
                bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_REAL), slow);
                a = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, left + offsetof(Value, real));
                b = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, right + offsetof(Value, real));
        } else {
                LirLabel left_int = lir_label(c->L);
                LirLabel right_int = lir_label(c->L);
                LirLabel ready = lir_label(c->L);
                a = lir_reg(c->L, LIR_F64);
                b = lir_reg(c->L, LIR_F64);
                LirOpnd la = lir_m(c->ops, LIR_NONE, 1, left + offsetof(Value, real));
                LirOpnd lb = lir_m(c->ops, LIR_NONE, 1, right + offsetof(Value, real));
                bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_REAL), left_int);
                c->ok = c->ok && lir_emit_to(c->L, LIR_LD_F64, a, &la, 1);
                bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_REAL), right_int);
                c->ok = c->ok && lir_emit_to(c->L, LIR_LD_F64, b, &lb, 1);
                bc_jump(c, ready);
                bc_bind(c, right_int);
                bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_INTEGER), slow);
                LirReg zb = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, right + offsetof(Value, z));
                LirOpnd cb = lir_r(zb);
                c->ok = c->ok && lir_emit_to(c->L, LIR_I2F, b, &cb, 1);
                bc_jump(c, ready);
                bc_bind(c, left_int);
                bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_INTEGER), slow);
                bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_REAL), slow);
                LirReg za = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, left + offsetof(Value, z));
                LirOpnd ca = lir_r(za);
                c->ok = c->ok && lir_emit_to(c->L, LIR_I2F, a, &ca, 1);
                c->ok = c->ok && lir_emit_to(c->L, LIR_LD_F64, b, &lb, 1);
                bc_bind(c, ready);
        }
        args[0] = lir_r(a);
        args[1] = lir_r(b);
        compare[0] = lir_cc(fcc);
        compare[1] = lir_r(a);
        compare[2] = lir_r(b);
        d = bc_value(c, fop, cmp ? LIR_I64 : LIR_F64, cmp ? compare : args, cmp ? 3 : 2);
        if (cmp) {
                for (u32 i = 0; i < sizeof (Value); i += 8) {
                        bc_store(c, LIR_ST64, c->ops, left + i, lir_i(0));
                }
                bc_store(c, LIR_ST8, c->ops, left + offsetof(Value, type), lir_i(VALUE_BOOLEAN));
        }
        if (!cmp) {
                bc_store(c, LIR_ST64, c->ops, left + offsetof(Value, type), lir_i(VALUE_REAL));
        }
        bc_store(c, cmp ? LIR_ST64 : LIR_ST_F64, c->ops, left + offsetof(Value, real), lir_r(d));
        bc_jump(c, end);
        bc_bind(c, slow);
        LirReg out = bc_addr(c, c->ops, left);
        LirReg rhs = bc_addr(c, c->ops, right);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd call_args[] = { lir_r(c->ty), lir_r(out), lir_r(out), lir_r(rhs) };
        bc_call(c, helper, LIR_VOID, types, call_args, countof(call_args));
        bc_bind(c, end);
        --c->sp;
}

static void
bc_base_index(BcLir *c)
{
        LirReg base = bc_load(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, stack.items));
        LirOpnd arg = lir_r(c->ops);
        LirReg bits = bc_value(c, LIR_BITCAST, LIR_I64, &arg, 1);
        LirOpnd sub[] = { lir_r(bits), lir_r(base) };
        LirReg bytes = bc_value(c, LIR_SUB, LIR_I64, sub, countof(sub));
        LirOpnd shift[] = { lir_r(bytes), lir_i(5) };
        c->ok = c->ok && lir_emit_to(c->L, LIR_SHR, c->base_index, shift, countof(shift));
}

static void
bc_stack_count_at(BcLir *c, i32 slot)
{
        if (c->base_index != LIR_NONE) {
                LirReg count = c->base_index;
                if (slot != 0) {
                        LirOpnd add[] = { lir_r(c->base_index), lir_i(slot) };
                        count = bc_value(c, LIR_ADD, LIR_I64, add, countof(add));
                }
                bc_store(c, LIR_ST64, c->ty, offsetof(Ty, stack.count), lir_r(count));
                return;
        }
        LirReg top = bc_addr(c, c->ops, slot * sizeof (Value));
        LirReg base = bc_load(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, stack.items));
        LirOpnd arg = lir_r(top);
        LirReg bits = bc_value(c, LIR_BITCAST, LIR_I64, &arg, 1);
        LirOpnd sub[] = { lir_r(bits), lir_r(base) };
        LirReg bytes = bc_value(c, LIR_SUB, LIR_I64, sub, countof(sub));
        LirOpnd shift[] = { lir_r(bytes), lir_i(5) };
        LirReg count = bc_value(c, LIR_SHR, LIR_I64, shift, countof(shift));
        bc_store(c, LIR_ST64, c->ty, offsetof(Ty, stack.count), lir_r(count));
}

static void
bc_stack_count(BcLir *c)
{
        if (c->base_index != LIR_NONE) {
                bc_stack_count_at(c, c->sp);
                return;
        }
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirReg base = bc_load(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, stack.items));
        LirOpnd arg = lir_r(top);
        LirReg bits = bc_value(c, LIR_BITCAST, LIR_I64, &arg, 1);
        LirOpnd sub[] = { lir_r(bits), lir_r(base) };
        LirReg bytes = bc_value(c, LIR_SUB, LIR_I64, sub, countof(sub));
        LirOpnd shift[] = { lir_r(bytes), lir_i(5) };
        LirReg count = bc_value(c, LIR_SHR, LIR_I64, shift, countof(shift));
        bc_store(c, LIR_ST64, c->ty, offsetof(Ty, stack.count), lir_r(count));
}

static bool
bc_cfg_edge(BcLir *c, i32 offset, i32 sp, i32 *queue, u32 *n)
{
        if (offset < 0 || offset >= c->size || c->nodes[offset].next == 0) {
                return false;
        }
        BcLirNode *node = &c->nodes[offset];
        if (node->sp >= 0) {
                bool resets = node->op == INSTR_RESTORE_STACK_POS || node->op == INSTR_POP_STACK_POS
                           || node->op == INSTR_POP_STACK_POS_POP || node->op == INSTR_POP_STACK_POS_POP2;
                bool twins = resets && node->saved >= 0 && c->saved >= 0
                          && c->nodes[node->saved].sp == c->nodes[c->saved].sp
                          && c->nodes[node->saved].saved == c->nodes[c->saved].saved;
                if (node->saved != c->saved && !twins) {
                        i32 a = node->saved;
                        i32 b = c->saved;
                        i32 n = 0;
                        while (a >= 0 && b >= 0 && a != b && n++ < c->size) {
                                a = c->nodes[a].saved;
                                b = c->nodes[b].saved;
                        }
                        if (a != b) {
                                return false;
                        }
                        c->dynamic = true;
                }
                c->dynamic = c->dynamic || (node->sp != sp && !resets);
                return true;
        }
        node->sp = sp;
        node->saved = c->saved;
        node->sentinel = c->sentinel;
        node->sentinel_sp = c->sentinel_sp;
        queue[(*n)++] = offset;
        return true;
}

static bool
bc_in_try(BcLir const *c, i32 offset)
{
        for (i32 t = 0; t < c->size; ++t) {
                BcLirNode const *node = &c->nodes[t];
                if (node->next == 0 || node->op != INSTR_TRY || t > offset) {
                        continue;
                }
                i32 end = node->catch_to;
                if (node->finally_to > end) {
                        end = node->finally_to;
                }
                if (node->end_to > end) {
                        end = node->end_to;
                }
                if (end < 0 || offset < end) {
                        return true;
                }
        }
        return false;
}

static JitDeopt DeoptAt[512];

__attribute__((constructor)) static void
bc_deopt_table(void)
{
        for (i32 i = 0; i < (i32)countof(DeoptAt); ++i) {
                DeoptAt[i] = (JitDeopt) { .sp = i, .nsave = 0 };
        }
}

static LirOpnd
bc_deopt_info(BcLir *c)
{
        if (c->sp >= 0 && c->sp < (i32)countof(DeoptAt)) {
                return lir_i((uptr)&DeoptAt[c->sp]);
        }
        LirOpnd allocation[] = { lir_i(sizeof (JitDeopt)), lir_i(alignof (JitDeopt)) };
        LirReg info = bc_value(c, LIR_ALLOCA, LIR_PTR, allocation, countof(allocation));
        bc_store(c, LIR_ST32, info, offsetof(JitDeopt, sp), lir_i(c->sp));
        bc_store(c, LIR_ST32, info, offsetof(JitDeopt, nsave), lir_i(0));
        return lir_r(info);
}

static void
bc_tier_hot(i32 *count, i32 *info)
{
        Value f = { .type = VALUE_FUNCTION, .info = info };
        *count = INT32_MAX;
        jit_tier_up(&f);
}

static void
bc_tier_check(BcLir *c, LirLabel deopt)
{
        LirOpnd where = lir_i((uptr)c->tier);
        LirReg p = bc_value(c, LIR_LI, LIR_PTR, &where, 1);
        LirReg n = bc_load(c, LIR_LD_I32, LIR_I64, p, 0);
        LirOpnd dec[] = { lir_r(n), lir_i(-1) };
        LirReg m = bc_value(c, LIR_ADD, LIR_I64, dec, countof(dec));
        LirLabel cold = lir_label(c->L);
        bc_store(c, LIR_ST32, p, 0, lir_r(m));
        bc_branch(c, LIR_GT, lir_r(m), lir_i(0), cold);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(p), lir_i((uptr)c->function->info) };
        bc_call_flags(c, bc_tier_hot, LIR_VOID, types, args, countof(args), LIR_READS_NO_LOCALS);
        if (deopt != LIR_NONE) {
                bc_stack_count(c);
                bc_jump(c, deopt);
        }
        bc_bind(c, cold);
}

static bool
bc_lir_cfg(BcLir *c, Value const *f)
{
        char const *code = code_of(f);
        c->code = code;
        c->saved = -1;
        c->sentinel = -1;
        c->sentinel_sp = -1;
        i32 owner = -1;
        c->size = code_size_of(f);
        c->nodes = calloc((usize)c->size + 1, sizeof *c->nodes);
        i32 *queue = malloc(((usize)c->size + 1) * sizeof *queue);
        bool ok = false;
        u32 n = 0;
        if (c->nodes == NULL || queue == NULL) {
                goto End;
        }
        for (i32 off = 0; off < c->size;) {
                c->offset = off;
                BcLirNode *node = &c->nodes[off];
                node->next = StepInstruction(code + off) - code;
                node->sp = -1;
                node->target = -1;
                node->label = LIR_NONE;
                node->deopt = LIR_NONE;
                node->resume = LIR_NONE;
                node->op = code[off];
                node->owner = owner;
                node->outer = owner;
                node->saved = -1;
                if (node->op == INSTR_TRY) {
                        i32 delta;
                        memcpy(&delta, code + off + 1, sizeof delta);
                        node->catch_to = off + 5 + delta;
                        memcpy(&delta, code + off + 5, sizeof delta);
                        node->finally_to = delta == -1 ? -1 : off + 9 + delta;
                        memcpy(&delta, code + off + 9, sizeof delta);
                        node->end_to = delta == -1 ? -1 : off + 13 + delta;
                        owner = off;
                        node->owner = off;
                        c->dynamic = true;
                        c->has_try = true;
                } else if (node->op == INSTR_END_TRY) {
                        if (owner < 0) {
                                goto End;
                        }
                        owner = c->nodes[owner].outer;
                }
                if (node->op == INSTR_TRY_YIELD_FROM || node->op == INSTR_SPREAD_CHECK
                    || node->op == INSTR_GET_NEXT || node->op == INSTR_FIX_TO
                    || node->op == INSTR_FIX_EXTRA || node->op == INSTR_EXEC_CODE) {
                        c->dynamic = true;
                }
                if (node->next <= off || node->next > c->size) {
                        goto End;
                }
                switch (node->op) {
                case INSTR_TAIL_CALL:
                        node->argc = f->info[FUN_INFO_PARAM_COUNT];
                        node->member = node->argc + (f->info[FUN_INFO_CLASS] != -1);
                        node->target = 0;
                        node->branch = true;
                        break;
                case INSTR_CALL:
                case INSTR_CALL_GLOBAL:
                case INSTR_CALL_METHOD:
                case INSTR_TRY_CALL_METHOD:
                case INSTR_CALL_SELF_METHOD:
                case INSTR_CALL_STATIC_METHOD:
                case INSTR_CALL_SELF_STATIC: {
                        i32 at = off + 1;
                        if (node->op == INSTR_CALL_GLOBAL || node->op == INSTR_CALL_STATIC_METHOD) {
                                memcpy(&node->global, code + at, sizeof node->global);
                                at += sizeof node->global;
                        }
                        memcpy(&node->argc, code + at, sizeof node->argc);
                        at += sizeof node->argc;
                        if (node->op != INSTR_CALL && node->op != INSTR_CALL_GLOBAL) {
                                memcpy(&node->member, code + at, sizeof node->member);
                                at += sizeof node->member;
                        }
                        memcpy(&node->nkw, code + at, sizeof node->nkw);
                        node->kw_ip = code + at + sizeof node->nkw;
                        if (node->argc < -1 || node->nkw < 0) {
                                goto End;
                        }
                        if (node->argc == -1) {
                                c->dynamic = true;
                        }
                        break;
                }
                case INSTR_ENSURE_LEN:
                case INSTR_ENSURE_LEN_TUPLE:
                case INSTR_ENSURE_EQUALS_VAR:
                case INSTR_TRY_UNAPPLY:
                case INSTR_TRY_ASSIGN_NON_NIL:
                case INSTR_TRY_RANGE:
                case INSTR_TRY_INCRANGE:
                case INSTR_ENSURE_DICT:
                case INSTR_ENSURE_CONTAINS:
                case INSTR_ENSURE_SAME_KEYS:
                case INSTR_TRY_INDEX:
                case INSTR_INDEX_TUPLE:
                case INSTR_TRY_INDEX_TUPLE:
                case INSTR_TRY_MEMBER:
                case INSTR_TRY_TUPLE_MEMBER:
                case INSTR_TRY_TAG_POP:
                case INSTR_TRY_REGEX:
                case INSTR_TRY_STEAL_TAG:
                case INSTR_ARRAY_REST:
                case INSTR_TUPLE_REST:
                case INSTR_RECORD_REST:
                case INSTR_JNI:
                case INSTR_JII:
                case INSTR_JUMP_IF_TYPE:
                case INSTR_SPREAD_CHECK:
                case INSTR_LOOP_CHECK: {
                        i32 jump;
                        memcpy(&jump, code + off + 1, sizeof jump);
                        if (node->op == INSTR_SPREAD_CHECK) {
                                node->member = (u8)code[off + 5];
                        } else if (node->next - off >= 9) {
                                memcpy(&node->member, code + off + 5, sizeof node->member);
                        }
                        node->target = off + 5 + jump;
                        node->branch = true;
                        break;
                }
                case INSTR_MATCH_TAG:
                case INSTR_MATCH_STRING: {
                        i32 at = off + 1;
                        if (node->op == INSTR_MATCH_TAG) {
                                node->member = (u8)code[at++];
                        }
                        memcpy(&node->argc, code + at, sizeof node->argc);
                        at += sizeof node->argc;
                        i32 delta;
                        memcpy(&delta, code + at, sizeof delta);
                        at += sizeof delta;
                        node->target = at + delta;
                        node->kw_ip = code + at;
                        node->branch = true;
                        break;
                }
                case INSTR_JUMP:
                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE:
                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JUMP_IF_NIL:
                case INSTR_JUMP_IF_NONE:
                case INSTR_TRY_YIELD_FROM:
                case INSTR_JUMP_WTF:
                case INSTR_NONE_IF_NOT:
                case INSTR_SKIP_CHECK:
                case INSTR_JUMP_IF_SENTINEL:
                case INSTR_JUMP_IF_INIT:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR: {
                        i32 jump;
                        memcpy(&jump, code + off + 1, sizeof jump);
                        node->target = node->next + jump;
                        node->branch = true;
                        break;
                }
                default:
                        break;
                }
                off = node->next;
        }
        if (!bc_cfg_edge(c, 0, 0, queue, &n)) {
                goto End;
        }
        for (u32 q = 0; q < n; ++q) {
                c->offset = queue[q];
                BcLirNode *node = &c->nodes[queue[q]];
                i32 sp = node->sp;
                if (sp > c->max_sp) {
                        c->max_sp = sp;
                }
                c->saved = node->saved;
                c->sentinel = node->sentinel;
                c->sentinel_sp = node->sentinel_sp;
                i32 taken = sp;
                switch (node->op) {
                case INSTR_TRY:
                        c->sentinel = queue[q];
                        c->sentinel_sp = sp;
                        if (!bc_cfg_edge(c, node->catch_to, sp + 2, queue, &n)) {
                                goto End;
                        }
                        c->sentinel = node->sentinel;
                        c->sentinel_sp = node->sentinel_sp;
                        break;
                case INSTR_SAVE_STACK_POS:
                        c->saved = queue[q];
                        break;
                case INSTR_RESTORE_STACK_POS:
                case INSTR_POP_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                case INSTR_POP_STACK_POS_POP2:
                case INSTR_DROP_STACK_POS:
                        if (c->saved < 0) {
                                goto End;
                        }
                        if (node->op != INSTR_DROP_STACK_POS) {
                                sp = c->nodes[c->saved].sp
                                   - (node->op == INSTR_POP_STACK_POS_POP)
                                   - 2 * (node->op == INSTR_POP_STACK_POS_POP2);
                                c->sentinel = c->nodes[c->saved].sentinel;
                                c->sentinel_sp = c->nodes[c->saved].sentinel_sp;
                        }
                        if (node->op != INSTR_RESTORE_STACK_POS) {
                                c->saved = c->nodes[c->saved].saved;
                        }
                        break;
                case INSTR_CLEAR_EXTRA:
                        if (c->sentinel >= 0) {
                                sp = c->sentinel_sp;
                                BcLirNode const *parent = &c->nodes[c->sentinel];
                                c->sentinel = parent->sentinel;
                                c->sentinel_sp = parent->sentinel_sp;
                        } else if (node->owner >= 0) {
                                sp = c->nodes[node->owner].sp;
                        } else {
                                goto End;
                        }
                        break;
                case INSTR_FINALLY:
                case INSTR_RETHROW: {
                        if (node->owner < 0) {
                                goto End;
                        }
                        BcLirNode const *t = &c->nodes[node->owner];
                        if (node->op == INSTR_FINALLY && !bc_cfg_edge(c, node->next, sp, queue, &n)) {
                                goto End;
                        }
                        if (t->finally_to < 0
                            || !bc_cfg_edge(c, t->finally_to, t->sp + 1, queue, &n)) {
                                goto End;
                        }
                        continue;
                }
                case INSTR_END_TRY: {
                        BcLirNode const *t = &c->nodes[node->owner];
                        if (t->end_to >= 0 && !bc_cfg_edge(c, t->end_to, sp, queue, &n)) {
                                goto End;
                        }
                        for (i32 off = 0; off < c->size; ++off) {
                                BcLirNode const *f = &c->nodes[off];
                                if (f->next != 0 && f->op == INSTR_FINALLY && f->owner == node->owner
                                    && f->sp >= 0 && !bc_cfg_edge(c, f->next, f->sp, queue, &n)) {
                                        goto End;
                                }
                        }
                        continue;
                }
                case INSTR_CATCH:
                case INSTR_POP_TRY:
                case INSTR_CHECK_INIT:
                        break;
                case INSTR_TARGET_GLOBAL:
                case INSTR_TARGET_THREAD_LOCAL:
                case INSTR_TARGET_SELF_STATIC:
                case INSTR_TARGET_STATIC_MEMBER:
                case INSTR_DROP:
                case INSTR_DISCARD_DROP_GROUP:
                case INSTR_PUSH_DROP_GROUP:
                case INSTR_PUSH_DEFER_GROUP:
                case INSTR_CLEANUP:
                case INSTR_EXEC_CODE:
                case INSTR_DEBUG:
                case INSTR_REVERSE:
                case INSTR_SKIP_CHECK:
                case INSTR_JUMP_IF_INIT:
                case INSTR_NOP:
                case INSTR_CAPTURE:
                case INSTR_PATCH_ENV:
                case INSTR_TARGET_LOCAL:
                case INSTR_TARGET_CAPTURED:
                case INSTR_TARGET_REF:
                        break;
                case INSTR_MUT_ADD:
                case INSTR_MUT_SUB:
                case INSTR_MUT_MUL:
                case INSTR_MUT_DIV:
                case INSTR_MUT_MOD:
                case INSTR_MUT_AND:
                case INSTR_MUT_OR:
                case INSTR_MUT_XOR:
                case INSTR_MUT_SHL:
                case INSTR_MUT_SHR:
                case INSTR_ASSIGN:
                        if (sp < 1) {
                                goto End;
                        }
                        break;
                case INSTR_HALT:
                        goto End;
                case INSTR_LOAD_THREAD_LOCAL:
                case INSTR_PRE_INC:
                case INSTR_POST_INC:
                case INSTR_PRE_DEC:
                case INSTR_POST_DEC:
                case INSTR_BIND_STATIC:
                case INSTR_SELF_STATIC_ACCESS:
                case INSTR_STATIC_MEMBER_ACCESS:
                case INSTR_NAMESPACE:
                case INSTR_TRACE:
                case INSTR_OPERATOR:
                case INSTR_READ_INDEX:
                case INSTR_UNPOP:
                case INSTR_LOAD_LOCAL:
                case INSTR_LOAD_GLOBAL:
                case INSTR_PUSH_INDEX:
                case INSTR_ARRAY0:
                case INSTR_STRING:
                case INSTR_SELF:
                case INSTR_CLASS:
                case INSTR_TAG:
                case INSTR_REGEX:
                case INSTR_TYPE:
                case INSTR_VALUE:
                case INSTR_SELF_MEMBER_ACCESS:
                case INSTR_LOAD_CAPTURED:
                case INSTR_LOAD_REF:
                case INSTR_FUNCTION:
                case INSTR_GENERATOR:
                case INSTR_INT8:
                case INSTR_INTEGER:
                case INSTR_REAL:
                case INSTR_TRUE:
                case INSTR_FALSE:
                case INSTR_NIL:
                case INSTR_NONE:
                        ++sp;
                        break;
                case INSTR_RENDER_TEMPLATE: {
                        uptr value;
                        memcpy(&value, code + queue[q] + 1, sizeof value);
                        Expr const *expr = (Expr const *)value;
                        i32 count = vN(expr->template.holes);
                        if (sp < count) {
                                goto End;
                        }
                        sp += 1 - count;
                        break;
                }
                case INSTR_SENTINEL:
                        c->sentinel = queue[q];
                        c->sentinel_sp = sp++;
                        break;
                case INSTR_FIX_TO: {
                        i32 count;
                        memcpy(&count, code + queue[q] + 1, sizeof count);
                        if (count < 0 || c->sentinel < 0) {
                                goto End;
                        }
                        sp = c->sentinel_sp + 1 + count;
                        break;
                }
                case INSTR_FIX_EXTRA:
                        if (c->sentinel < 0) {
                                goto End;
                        }
                        break;
                case INSTR_LOOP_ITER:
                        if (sp < 2) {
                                goto End;
                        }
                        sp += 2;
                        break;
                case INSTR_ENSURE_LEN:
                case INSTR_ENSURE_LEN_TUPLE:
                case INSTR_ENSURE_EQUALS_VAR:
                case INSTR_TRY_UNAPPLY:
                case INSTR_TRY_ASSIGN_NON_NIL:
                case INSTR_TRY_RANGE:
                case INSTR_TRY_INCRANGE:
                case INSTR_ENSURE_DICT:
                case INSTR_ENSURE_CONTAINS:
                case INSTR_ENSURE_SAME_KEYS:
                case INSTR_TRY_INDEX:
                case INSTR_INDEX_TUPLE:
                case INSTR_TRY_INDEX_TUPLE:
                case INSTR_TRY_MEMBER:
                case INSTR_TRY_TUPLE_MEMBER:
                case INSTR_TRY_TAG_POP:
                case INSTR_TRY_REGEX:
                case INSTR_TRY_STEAL_TAG:
                case INSTR_ARRAY_REST:
                case INSTR_TUPLE_REST:
                case INSTR_RECORD_REST:
                case INSTR_JNI:
                case INSTR_JII:
                        if (sp < 1) {
                                goto End;
                        }
                        switch (node->op) {
                        case INSTR_TRY_INDEX:
                        case INSTR_INDEX_TUPLE:
                        case INSTR_TRY_INDEX_TUPLE:
                        case INSTR_TRY_MEMBER:
                        case INSTR_TRY_TUPLE_MEMBER:
                        case INSTR_TRY_REGEX:
                                ++sp;
                                break;
                        case INSTR_TRY_UNAPPLY:
                                if (sp < 2) {
                                        goto End;
                                }
                                --sp;
                                break;
                        case INSTR_TRY_RANGE:
                        case INSTR_TRY_INCRANGE:
                                if (sp < 3) {
                                        goto End;
                                }
                                sp -= 2;
                                taken = sp;
                                break;
                        case INSTR_ENSURE_EQUALS_VAR:
                        case INSTR_ENSURE_CONTAINS:
                        case INSTR_ENSURE_SAME_KEYS:
                                if (sp < 2) {
                                        goto End;
                                }
                                --sp;
                                taken = sp;
                                break;
                        case INSTR_JNI:
                        case INSTR_JII:
                                sp -= node->member < 0;
                                taken = sp;
                                break;
                        default:
                                break;
                        }
                        break;
                case INSTR_MATCH_TAG:
                case INSTR_MATCH_STRING:
                        if (sp < 1 || node->argc < 0
                            || !bc_cfg_edge(c, node->target, sp, queue, &n)) {
                                goto End;
                        }
                        for (i32 i = 0; i < node->argc; ++i) {
                                i32 id;
                                i32 delta;
                                char const *slot = node->kw_ip + i * 8;
                                memcpy(&id, slot, sizeof id);
                                memcpy(&delta, slot + 4, sizeof delta);
                                if (id != -1 && !bc_cfg_edge(c, slot + 8 - code + delta, sp, queue, &n)) {
                                        goto End;
                                }
                        }
                        continue;
                case INSTR_SLICE:
                        if (sp < 4) {
                                goto End;
                        }
                        sp -= 3;
                        break;
                case INSTR_GET_NEXT:
                        if (sp < 2) {
                                goto End;
                        }
                        ++sp;
                        break;
                case INSTR_JUMP_WTF:
                case INSTR_NONE_IF_NOT:
                        if (sp < 1) {
                                goto End;
                        }
                        --sp;
                        break;
                case INSTR_UNAPPLY:
                        if (sp < 2) {
                                goto End;
                        }
                        break;
                case INSTR_JUMP_IF_TYPE:
                        if (sp < 1) {
                                goto End;
                        }
                        break;
                case INSTR_LOOP_CHECK:
                        if (sp < 4 || node->member < 0) {
                                goto End;
                        }
                        taken = sp - 4;
                        sp += node->member - 1;
                        break;
                case INSTR_SPREAD_CHECK:
                        if (sp < 4) {
                                goto End;
                        }
                        taken = sp - 4;
                        sp += node->member - 1;
                        break;
                case INSTR_ARRAY_COMPR:
                case INSTR_SET_COMPR:
                        if (c->saved < 0) {
                                goto End;
                        }
                        sp = c->nodes[c->saved].sp;
                        c->saved = c->nodes[c->saved].saved;
                        break;
                case INSTR_DICT_COMPR: {
                        i32 n;
                        memcpy(&n, code + queue[q] + 5, sizeof n);
                        if (n < 0 || sp < 2 * n) {
                                goto End;
                        }
                        sp -= 2 * n;
                        break;
                }
                case INSTR_ARRAY:
                case INSTR_SET:
                case INSTR_DICT:
                case INSTR_DEFAULT_DICT:
                case INSTR_GATHER_TUPLE:
                        if (c->saved < 0) {
                                goto End;
                        }
                        sp = c->nodes[c->saved].sp + 1;
                        c->saved = c->nodes[c->saved].saved;
                        break;
                case INSTR_TUPLE:
                case INSTR_XTUPLE:
                case INSTR_CONCAT_STRINGS: {
                        i32 count;
                        memcpy(&count, code + queue[q] + 1, sizeof count);
                        if (count < 0 || sp < count) {
                                goto End;
                        }
                        sp += 1 - count;
                        break;
                }
                case INSTR_ASSIGN_SUBSCRIPT: {
                        u32 count = (u8)code[queue[q] + 1];
                        if (sp < count + 2) {
                                goto End;
                        }
                        sp -= count + 1;
                        break;
                }
                case INSTR_DROP2:
                        if (sp < 3) {
                                goto End;
                        }
                        sp -= 2;
                        break;
                case INSTR_POP2:
                case INSTR_TARGET_DYN_MEMBER:
                case INSTR_TARGET_SUBSCRIPT:
                        if (sp < 2) {
                                goto End;
                        }
                        sp -= 2;
                        break;
                case INSTR_TARGET_MEMBER:
                        if (sp < 1) {
                                goto End;
                        }
                        --sp;
                        break;
                case INSTR_TARGET_SELF_MEMBER:
                        break;
                case INSTR_MAYBE_ASSIGN:
                case INSTR_DECORATE:
                case INSTR_INTO_METHOD:
                case INSTR_BIND_CLASS:
                case INSTR_BIND_INSTANCE:
                case INSTR_BIND_GETTER:
                case INSTR_BIND_SETTER:
                case INSTR_PUSH_DROP:
                case INSTR_ENTER:
                case INSTR_TRY_YIELD_FROM:
                case INSTR_UNARY_OP:
                case INSTR_QUESTION:
                case INSTR_TO_REGEX:
                case INSTR_COMPILE_REGEX:
                case INSTR_EVAL:
                case INSTR_GET_TAG:
                case INSTR_NONE_IF_NIL:
                case INSTR_RETURN_IF_NOT_NONE:
                case INSTR_JUMP_IF_SENTINEL:
                case INSTR_UNTAG_OR_DIE:
                case INSTR_STEAL_TAG:
                case INSTR_THROW_IF_NIL:
                case INSTR_MEMBER_ACCESS:
                case INSTR_TRY_MEMBER_ACCESS:
                case INSTR_NEG:
                case INSTR_NOT:
                case INSTR_INC:
                case INSTR_DEC:
                case INSTR_TO_STRING:
                case INSTR_COUNT:
                case INSTR_CLASS_OF:
                case INSTR_TAG_PUSH:
                        if (sp < 1) {
                                goto End;
                        }
                        break;
                case INSTR_SWAP:
                        if (c->sentinel_sp == sp - 1) {
                                --c->sentinel_sp;
                        } else if (c->sentinel_sp == sp - 2) {
                                ++c->sentinel_sp;
                        }
                        if (sp < 2) {
                                goto End;
                        }
                        break;
                case INSTR_DUP2_SWAP:
                        if (sp < 2) {
                                goto End;
                        }
                        sp += 2;
                        break;
                case INSTR_PUSH_ARRAY_ELEM:
                case INSTR_PUSH_TUPLE_ELEM:
                case INSTR_PUSH_TUPLE_MEMBER:
                case INSTR_PUSH_UNTAGGED:
                case INSTR_PUSH_NTH:
                case INSTR_DUP:
                        if (sp < 1) {
                                goto End;
                        }
                        ++sp;
                        break;
                case INSTR_DEFER:
                case INSTR_ASSIGN_GLOBAL:
                case INSTR_ASSIGN_REGEX_MATCHES:
                case INSTR_ASSIGN_LOCAL:
                case INSTR_POP:
                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JUMP_IF_NIL:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR:
                        if (sp < 1) {
                                goto End;
                        }
                        --sp;
                        taken = node->op == INSTR_JUMP_AND || node->op == INSTR_JUMP_OR
                              ? node->sp : sp;
                        break;
                case INSTR_JUMP_IF_NONE:
                        if (sp < 1) {
                                goto End;
                        }
                        break;
                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE:
                        if (sp < 2) {
                                goto End;
                        }
                        sp -= 2;
                        taken = sp;
                        break;
                case INSTR_CALL:
                case INSTR_CALL_GLOBAL:
                case INSTR_CALL_METHOD:
                case INSTR_TRY_CALL_METHOD:
                case INSTR_CALL_SELF_METHOD:
                case INSTR_CALL_STATIC_METHOD:
                case INSTR_CALL_SELF_STATIC: {
                        bool explicit = node->op == INSTR_CALL
                                     || node->op == INSTR_CALL_METHOD
                                     || node->op == INSTR_TRY_CALL_METHOD;
                        bool dynamic_member = explicit && node->op != INSTR_CALL
                                           && node->member == -1;
                        if (node->argc == -1) {
                                if (c->saved < 0) {
                                        goto End;
                                }
                                sp = c->nodes[c->saved].sp + 1;
                                c->saved = c->nodes[c->saved].saved;
                                break;
                        }
                        if (sp < node->argc + node->nkw + explicit + dynamic_member) {
                                goto End;
                        }
                        sp -= node->argc + node->nkw + dynamic_member;
                        sp += !explicit;
                        break;
                }
                case INSTR_BINARY_OP:
                case INSTR_DIV:
                case INSTR_CMP:
                case INSTR_CHECK_MATCH:
                case INSTR_MOD:
                case INSTR_BIT_AND:
                case INSTR_BIT_OR:
                case INSTR_BIT_XOR:
                case INSTR_SHL:
                case INSTR_SHR:
                case INSTR_RANGE:
                case INSTR_INCRANGE:
                case INSTR_SUBSCRIPT:
                case INSTR_SAFE_SUBSCRIPT:
                case INSTR_GET_MEMBER:
                case INSTR_TRY_GET_MEMBER:
                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                case INSTR_EQ:
                case INSTR_NEQ:
                case INSTR_LT:
                case INSTR_GT:
                case INSTR_LEQ:
                case INSTR_GEQ:
                        if (sp < 2) {
                                goto End;
                        }
                        --sp;
                        break;
                case INSTR_YIELD:
                case INSTR_YIELD_SOME:
                        if (sp < 1) {
                                goto End;
                        }
                        break;
                case INSTR_YIELD_NONE:
                        ++sp;
                        break;
                case INSTR_DEFINE_TAG:
                case INSTR_DEFINE_CLASS: {
                        i32 count = 0;
                        i32 first = node->op == INSTR_DEFINE_TAG ? 9 : 5;
                        i32 last = node->op == INSTR_DEFINE_TAG ? 25 : 29;
                        for (i32 at = first; at < last; at += 4) {
                                i32 nmethods;
                                memcpy(&nmethods, code + queue[q] + at, sizeof nmethods);
                                if (nmethods < 0 || nmethods > sp - count) {
                                        goto End;
                                }
                                count += nmethods;
                        }
                        sp -= count;
                        break;
                }
                case INSTR_INIT_STATIC_FIELD:
                        if (sp < 1) {
                                goto End;
                        }
                        --sp;
                        break;
                case INSTR_TAIL_CALL:
                        if (sp < node->argc) {
                                goto End;
                        }
                        c->saved = -1;
                        c->sentinel = -1;
                        c->sentinel_sp = -1;
                        if (!bc_cfg_edge(c, 0, 0, queue, &n)) {
                                goto End;
                        }
                        continue;
                case INSTR_BAD_CALL:
                case INSTR_BAD_ASSIGN:
                        if (sp < 1) {
                                goto End;
                        }
                        continue;
                case INSTR_BAD_DISPATCH:
                        continue;
                case INSTR_TRAP:
                case INSTR_TRAP_TY:
                        continue;
                case INSTR_BAD_MATCH:
                case INSTR_THROW:
                        if (sp < 1) {
                                goto End;
                        }
                        continue;
                case INSTR_RETURN:
                case INSTR_RETURN_PRESERVE_CTX:
                        if (sp < 1) {
                                goto End;
                        }
                        continue;
                case INSTR_JUMP:
                        break;
                default:
                        goto End;
                }
                while (c->sentinel >= 0 && c->sentinel_sp >= sp) {
                        BcLirNode const *parent = &c->nodes[c->sentinel];
                        c->sentinel = parent->sentinel;
                        c->sentinel_sp = parent->sentinel_sp;
                }
                if (sp > INT32_MAX / sizeof (Value) - c->bound) {
                        goto End;
                }
                node->fall_sp = sp;
                if (node->branch && !bc_cfg_edge(c, node->target, taken, queue, &n)) {
                        goto End;
                }
                if (node->op != INSTR_JUMP && !bc_cfg_edge(c, node->next, sp, queue, &n)) {
                        goto End;
                }
        }
        ok = true;
End:
        free(queue);
        return ok;
}

static LirReg
bc_truthy(BcLir *c)
{
        i32 off = (c->sp - 1) * sizeof (Value);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, off + offsetof(Value, type));
        LirReg r = lir_reg(c->L, LIR_I64);
        LirLabel scalar = lir_label(c->L);
        LirLabel nil = lir_label(c->L);
        LirLabel end = lir_label(c->L);
        bc_branch(c, LIR_EQ, lir_r(type), lir_i(VALUE_INTEGER), scalar);
        bc_branch(c, LIR_EQ, lir_r(type), lir_i(VALUE_BOOLEAN), scalar);
        bc_branch(c, LIR_EQ, lir_r(type), lir_i(VALUE_NIL), nil);
        LirReg ptr = bc_addr(c, c->ops, off);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(c->ty), lir_r(ptr) };
        LirReg truth = bc_call(c, jit_rt_truthy, LIR_TYPE_I32, types, args, countof(args));
        LirOpnd answer = lir_r(truth);
        c->ok = c->ok && lir_emit_to(c->L, LIR_MOV, r, &answer, 1);
        bc_jump(c, end);
        bc_bind(c, scalar);
        LirReg value = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, off + offsetof(Value, z));
        LirOpnd compare[] = { lir_cc(LIR_NE), lir_r(value), lir_i(0) };
        c->ok = c->ok && lir_emit_to(c->L, LIR_SETCC, r, compare, countof(compare));
        bc_jump(c, end);
        bc_bind(c, nil);
        LirOpnd zero = lir_i(0);
        c->ok = c->ok && lir_emit_to(c->L, LIR_LI, r, &zero, 1);
        bc_bind(c, end);
        return r;
}

static void
bc_poll(BcLir *c, LirOpnd const *args)
{
        LirInst in = {
                .op = LIR_POLL, .dst = LIR_NONE, .nargs = 4,
                .flags = LIR_CALL_SITE,
                .tag = c->offset
        };
        memcpy(in.args, args, 4 * sizeof *args);
        c->ok = c->ok && lir_emit(c->L, &in);
}

static void
bc_compare_branch(BcLir *c, BcLirNode const *node, u8 op)
{
        i32 left = (c->sp - 2) * sizeof (Value);
        i32 right = left + sizeof (Value);
        bool equality = op == INSTR_EQ || op == INSTR_NEQ;
        LirLabel nil = equality ? lir_label(c->L) : LIR_NONE;
        LirLabel floats = lir_label(c->L);
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg result = lir_reg(c->L, LIR_I64);
        LirCC integer;
        LirCC floating;
        void *helper;
        switch (op) {
        case INSTR_EQ:  integer = LIR_EQ; floating = LIR_FEQ; helper = jit_rt_eq; break;
        case INSTR_NEQ: integer = LIR_NE; floating = LIR_FNE; helper = jit_rt_ne; break;
        case INSTR_LT:  integer = LIR_LT; floating = LIR_FLT; helper = jit_rt_lt; break;
        case INSTR_GT:  integer = LIR_GT; floating = LIR_FGT; helper = jit_rt_gt; break;
        case INSTR_LEQ: integer = LIR_LE; floating = LIR_FLE; helper = jit_rt_le; break;
        default:       integer = LIR_GE; floating = LIR_FGE; helper = jit_rt_ge; break;
        }
        LirReg at = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, left + offsetof(Value, type));
        LirReg bt = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, right + offsetof(Value, type));
        if (equality) {
                bc_branch(c, LIR_EQ, lir_r(at), lir_i(VALUE_NIL), nil);
                bc_branch(c, LIR_EQ, lir_r(bt), lir_i(VALUE_NIL), nil);
        }
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_INTEGER), floats);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_INTEGER), floats);
        LirReg a = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, left + offsetof(Value, z));
        LirReg b = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, right + offsetof(Value, z));
        LirOpnd args[] = { lir_cc(integer), lir_r(a), lir_r(b) };
        c->ok = c->ok && lir_emit_to(c->L, LIR_SETCC, result, args, countof(args));
        bc_jump(c, done);
        bc_bind(c, floats);
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_REAL), slow);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_REAL), slow);
        a = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, left + offsetof(Value, real));
        b = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, right + offsetof(Value, real));
        args[0] = lir_cc(floating);
        args[1] = lir_r(a);
        args[2] = lir_r(b);
        c->ok = c->ok && lir_emit_to(c->L, LIR_FSETCC, result, args, countof(args));
        bc_jump(c, done);
        if (equality) {
                bc_bind(c, nil);
                args[0] = lir_cc(integer);
                args[1] = lir_r(at);
                args[2] = lir_r(bt);
                c->ok = c->ok && lir_emit_to(c->L, LIR_SETCC, result, args, countof(args));
                bc_jump(c, done);
        }
        bc_bind(c, slow);
        LirReg out = bc_addr(c, c->ops, left);
        LirReg rhs = bc_addr(c, c->ops, right);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd call_args[] = { lir_r(c->ty), lir_r(out), lir_r(out), lir_r(rhs) };
        bc_call(c, helper, LIR_VOID, types, call_args, countof(call_args));
        LirOpnd memory = lir_m(c->ops, LIR_NONE, 1, left + offsetof(Value, z));
        c->ok = c->ok && lir_emit_to(c->L, LIR_LD_I64, result, &memory, 1);
        bc_bind(c, done);
        c->sp = node->fall_sp;
        if (c->dynamic) {
                bc_stack_count(c);
        }
        bc_branch(c, LIR_NE, lir_r(result), lir_i(0), c->nodes[node->target].label);
}

static void
bc_control(BcLir *c, BcLirNode const *node)
{
        LirLabel target = c->nodes[node->target].label;
        if (node->deopt != LIR_NONE) {
                LirOpnd info = bc_deopt_info(c);
                LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
                LirOpnd poll[] = { lir_r(c->ty), lir_r(top), info, lir_l(node->deopt) };
                bc_poll(c, poll);
                if (
                        c->tier != NULL
                     && node->op == INSTR_JUMP
                     && c->nodes[node->target].osr_id != 0
                ) {
                        bc_tier_check(c, node->deopt);
                }
        }
        u8 compare;
        switch (node->op) {
        case INSTR_JEQ: compare = INSTR_EQ; break;
        case INSTR_JNE: compare = INSTR_NEQ; break;
        case INSTR_JLT: compare = INSTR_LT; break;
        case INSTR_JGT: compare = INSTR_GT; break;
        case INSTR_JLE: compare = INSTR_LEQ; break;
        case INSTR_JGE: compare = INSTR_GEQ; break;
        default: compare = 0; break;
        }
        if (compare != 0) {
                bc_compare_branch(c, node, compare);
                return;
        }
        if (node->op == INSTR_JUMP) {
                bc_jump(c, target);
                return;
        }
        if (node->op == INSTR_JUMP_IF_TYPE) {
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->ops,
                                     (c->sp - 1) * sizeof (Value) + offsetof(Value, type));
                bc_branch(c, LIR_EQ, lir_r(type), lir_i(node->member), target);
                return;
        }
        LirReg value;
        LirCC cc;
        i64 test = 0;
        if (node->op == INSTR_JUMP_IF_NIL || node->op == INSTR_JUMP_IF_NONE
            || node->op == INSTR_JUMP_IF_SENTINEL) {
                value = bc_load(c, LIR_LD_U8, LIR_I64, c->ops,
                                (c->sp - 1) * sizeof (Value) + offsetof(Value, type));
                cc = LIR_EQ;
                test = VALUE_NONE;
                if (node->op == INSTR_JUMP_IF_NIL) {
                        test = VALUE_NIL;
                } else if (node->op == INSTR_JUMP_IF_SENTINEL) {
                        test = VALUE_SENTINEL;
                }
        } else {
                value = bc_truthy(c);
                cc = node->op == INSTR_JUMP_IF_NOT || node->op == INSTR_JUMP_AND ? LIR_EQ : LIR_NE;
        }
        if (c->dynamic && node->op != INSTR_JUMP_AND && node->op != INSTR_JUMP_OR) {
                c->sp = node->fall_sp;
                bc_stack_count(c);
        }
        bc_branch(c, cc, lir_r(value), lir_i(test), target);
}

static LirReg
bc_call_target(BcLir *c, LirOpnd target, LirType ret, LirType const *types,
               LirOpnd *args, u32 n, u32 flags)
{
        LirReg r = ret == LIR_VOID ? LIR_NONE : lir_reg(c->L, lir_type_class(ret));
        LirInst in = {
                .op = LIR_CALL, .dst = r, .args = { target }, .nargs = 1,
                .sig = { .ret = ret, .params = types, .nparams = n, .nfixed = n },
                .flags = flags,
                .tag = c->offset, .call_args = args, .ncall_args = n
        };
        c->last_call = c->L->ninsts;
        c->ok = c->ok && lir_emit(c->L, &in);
        return r;
}

static LirReg
bc_call_flags(BcLir *c, void *helper, LirType ret, LirType const *types,
              LirOpnd *args, u32 n, u32 flags)
{
        return bc_call_target(c, lir_i((uptr)helper), ret, types, args, n, flags);
}

static LirReg
bc_call(BcLir *c, void *helper, LirType ret, LirType const *types, LirOpnd *args, u32 n)
{
        u32 flags = LIR_MAY_GC | LIR_MAY_THROW | LIR_CALL_SITE | LIR_WRITES_LOCALS;
        if (helper == vm_global || helper == vm_get_self || helper == ClassOf
            || helper == jit_rt_truthy) {
                flags = LIR_READS_NO_LOCALS;
        }
        if (helper == jit_rt_throw || helper == vm_jit_end_try_rethrow) {
                flags |= LIR_NORETURN;
        }
        return bc_call_flags(c, helper, ret, types, args, n, flags);
}

static void
bc_invoke_keywords(BcLir *c, BcLirNode const *node)
{
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32,
                            LIR_TYPE_I32, LIR_TYPE_I32, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(node->global),
                          lir_i(node->argc), lir_i(node->nkw), lir_i((uptr)node->kw_ip) };
        void *helper = jit_rt_call_global_kw;
        u32 n = 6;
        if (node->op == INSTR_CALL) {
                args[2] = args[3];
                args[3] = args[4];
                args[4] = args[5];
                types[4] = LIR_TYPE_PTR;
                helper = jit_rt_call_kw;
                n = 5;
        } else if (node->op == INSTR_CALL_METHOD) {
                args[2] = lir_i(node->member);
                helper = jit_rt_call_method_kw;
        }
        bc_call(c, helper, LIR_VOID, types, args, n);
}

static void
bc_method(Ty *ty, Value *top, i32 op, i32 class, i32 member, i32 argc,
          i32 nkw, char *kw_ip)
{
        ty->stack.count = top - ty->stack.items;
        switch (op) {
        case INSTR_CALL_SELF_METHOD:
                xvP(ty->stack, *vm_get_self(ty));
                break;
        case INSTR_CALL_SELF_STATIC: {
                Value self = *vm_get_self(ty);
                xvP(ty->stack, CLASS(ClassOf(&self)));
                break;
        }
        case INSTR_CALL_STATIC_METHOD:
                xvP(ty->stack, CLASS(class));
                break;
        default:
                break;
        }
        jit_call_method_at(ty, ty->stack.items + ty->stack.count, member, argc,
                           nkw, kw_ip, op == INSTR_TRY_CALL_METHOD);
}

static void
bc_invoke_method(BcLir *c, BcLirNode const *node)
{
        if (bc_method_fast(c, node)) {
                return;
        }
        LirLabel inlined = LIR_NONE;
        bc_inline_method(c, node, &inlined);
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        if (node->nkw == 0 && node->argc >= 0 && node->member >= 0
            && (node->op == INSTR_CALL_METHOD || node->op == INSTR_CALL_SELF_METHOD)) {
                bool explicit = node->op == INSTR_CALL_METHOD;
                LirReg out = bc_addr(c, c->ops, (c->sp - explicit - node->argc) * sizeof (Value));
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32,
                                    LIR_TYPE_I32, LIR_TYPE_I32, LIR_TYPE_PTR };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(node->op), lir_i(node->member),
                                  lir_i(node->argc), lir_i((uptr)node->kw_ip) };
                LirReg frame = bc_call(c, bc_method_enter, LIR_TYPE_PTR, types, args, countof(args));
                bc_native_invoke(c, frame, out);
                if (inlined != LIR_NONE) {
                        bc_bind(c, inlined);
                }
                return;
        }
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32,
                            LIR_TYPE_I32, LIR_TYPE_I32, LIR_TYPE_I32,
                            LIR_TYPE_I32, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(node->op),
                          lir_i(node->global), lir_i(node->member), lir_i(node->argc),
                          lir_i(node->nkw), lir_i((uptr)node->kw_ip) };
        bc_call(c, bc_method, LIR_VOID, types, args, countof(args));
}

static void
bc_spread_call(Ty *ty, Value *top, i32 global, i32 nkw, char *kw_ip)
{
        ty->stack.count = top - ty->stack.items;
        Value fn = global < 0 ? ty->stack.items[--ty->stack.count] : *vm_global(ty, global);
        i32 argc = ty->stack.count - vXx(ty->st->sps) - nkw;
        gP(&fn);
        Value kwargs = BuildKwargsDict(ty, &kw_ip, nkw);
        DoCallEx(ty, &fn, argc, &kwargs, true);
        gX();
}

static bool
bc_tail_position(BcLir const *c, BcLirNode const *node)
{
        i32 n = node->next;
        for (i32 hops = 0; hops < 8 && n > 0 && n < c->size && c->nodes[n].op == INSTR_JUMP; ++hops) {
                n = c->nodes[n].target;
        }
        if (n <= 0 || n >= c->size || c->nodes[n].op != INSTR_RETURN) {
                return false;
        }
        for (i32 off = 0; off < c->size; ++off) {
                u8 op = c->nodes[off].op;
                if (
                        c->nodes[off].next != 0
                     && (op == INSTR_PUSH_DROP_GROUP || op == INSTR_PUSH_DEFER_GROUP || op == INSTR_DEFER)
                ) {
                        return false;
                }
        }
        return true;
}

static void
bc_tail_self(BcLir *c, BcLirNode const *node, LirReg fn)
{
        Value const *f = c->function;
        if (
                c->dynamic
             || c->has_try
             || c->base_index == LIR_NONE
             || c->self_index >= 0
             || is_starred(f)
             || node->argc > 16
             || c->bound > 48
             || !jit_linkable_global(f, node->argc)
             || !bc_tail_position(c, node)
        ) {
                return;
        }
        LirLabel miss = lir_label(c->L);
        LirLabel deopt = lir_label(c->L);
        LirLabel go = lir_label(c->L);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, fn, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_FUNCTION), miss);
        LirReg info = bc_load(c, LIR_LD_I64, LIR_PTR, fn, offsetof(Value, info));
        LirOpnd expected = lir_i((uptr)f->info);
        LirReg want = bc_value(c, LIR_LI, LIR_PTR, &expected, 1);
        bc_branch(c, LIR_NE, lir_r(info), lir_r(want), miss);
        LirReg env = bc_load(c, LIR_LD_I64, LIR_PTR, fn, offsetof(Value, env));
        bc_branch(c, LIR_NE, lir_r(env), lir_r(c->env), miss);
        LirOpnd state = bc_deopt_info(c);
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirOpnd poll[] = { lir_r(c->ty), lir_r(top), state, lir_l(deopt) };
        bc_poll(c, poll);
        bc_jump(c, go);
        bc_bind(c, deopt);
        bc_stack_count(c);
        LirOpnd result = lir_i(JIT_PACK(JIT_DEOPT, c->at));
        bc_effect(c, LIR_RET, &result, 1);
        bc_bind(c, go);
        i32 base = c->sp - 1 - node->argc;
        for (i32 i = 0; i < node->argc; ++i) {
                bc_value_copy(c, c->locals, i * sizeof (Value), c->ops, (base + i) * sizeof (Value));
        }
        for (i32 i = node->argc; i < c->bound; ++i) {
                bc_store(c, LIR_ST64, c->locals, i * sizeof (Value), lir_i(VALUE_NIL));
        }
        bc_stack_count_at(c, 0);
        bc_jump(c, c->nodes[0].label);
        bc_bind(c, miss);
}

static void
bc_invoke(BcLir *c, BcLirNode const *node)
{
        if (node->op != INSTR_CALL && node->op != INSTR_CALL_GLOBAL) {
                bc_invoke_method(c, node);
                return;
        }
        if (node->argc == -1) {
                LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32,
                                    LIR_TYPE_I32, LIR_TYPE_PTR };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top),
                                  lir_i(node->op == INSTR_CALL_GLOBAL ? node->global : -1),
                                  lir_i(node->nkw), lir_i((uptr)node->kw_ip) };
                bc_call(c, bc_spread_call, LIR_VOID, types, args, countof(args));
                return;
        }
        if (node->nkw != 0) {
                bc_invoke_keywords(c, node);
                return;
        }
        LirReg fn;
        bool global = node->op == INSTR_CALL_GLOBAL;
        i32 first = c->sp - node->argc - !global;
        LirLabel done = LIR_NONE;
        if (global) {
                LirOpnd where = lir_i((uptr)&Globals.items);
                LirReg address = bc_value(c, LIR_LI, LIR_PTR, &where, 1);
                LirReg globals = bc_load(c, LIR_LD_I64, LIR_PTR, address, 0);
                fn = bc_addr(c, globals, node->global * sizeof (Value));
                Value const *callee = vm_global(c->ctx, node->global);
                if (
                        !c->compact
                     && jit_linkable_global(callee, node->argc)
                     && callee->info[FUN_INFO_BOUND] - node->argc <= 32
                ) {
                        LirLabel miss = lir_label(c->L);
                        done = lir_label(c->L);
                        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, fn, offsetof(Value, type));
                        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_FUNCTION), miss);
                        LirReg info = bc_load(c, LIR_LD_I64, LIR_PTR, fn, offsetof(Value, info));
                        LirOpnd expected = lir_i((uptr)callee->info);
                        LirReg want = bc_value(c, LIR_LI, LIR_PTR, &expected, 1);
                        bc_branch(c, LIR_NE, lir_r(info), lir_r(want), miss);
                        bc_try_plan(c, callee, TY_INLINE_GLOBAL, node->argc, first, LIR_NONE,
                                    NULL, NULL, first, done);
                        bc_inline_call(c, fn, callee, first, node->argc, LIR_NONE, miss, done);
                        bc_bind(c, miss);
                } else if (callee->type == VALUE_CLASS && node->argc <= 8) {
                        bc_inline_ctor(c, fn, callee, first, node->argc, &done);
                } else if (callee->type == VALUE_BUILTIN_FUNCTION) {
                        LirLabel miss = lir_label(c->L);
                        done = lir_label(c->L);
                        bc_builtin_call(c, fn, callee, first, node->argc, miss, done);
                        bc_bind(c, miss);
                }
        } else {
                fn = bc_addr(c, c->ops, (c->sp - 1) * sizeof (Value));
                i32 at = node - c->nodes;
                bc_tail_self(c, node, fn);
                if (
                        !c->compact
                     && jit_linkable_global(c->function, node->argc)
                     && c->function->info[FUN_INFO_BOUND] - node->argc <= 32
                     && !(at >= 5 && (u8)c->code[at - 5] == INSTR_CLASS)
                ) {
                        LirLabel miss = lir_label(c->L);
                        done = lir_label(c->L);
                        bc_inline_call(c, fn, c->function, first, node->argc, LIR_NONE, miss, done);
                        bc_bind(c, miss);
                }
                if (at >= 5 && (u8)c->code[at - 5] == INSTR_CLASS && c->nodes[at - 5].sp >= 0
                    && c->nodes[at - 5].next == at && node->label == LIR_NONE && node->argc <= 8) {
                        Value klass = { .type = VALUE_CLASS };
                        memcpy(&klass.class, c->code + at - 4, sizeof klass.class);
                        bc_inline_ctor(c, fn, &klass, first, node->argc, &done);
                }
        }
        LirReg out = bc_addr(c, c->ops, first * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(c->ty), lir_r(out), lir_r(fn), lir_i(node->argc) };
        bc_stack_count(c);
        if (node->resume_id == 0) {
                bc_native_call(c, args);
                if (done != LIR_NONE) {
                        bc_bind(c, done);
                }
                return;
        }
        if (node->resume_id == 0) {
                bc_call(c, bc_sync_call, LIR_VOID, types, args, countof(args));
                return;
        }
        LirReg status = bc_call(c, bc_prepare_call, LIR_TYPE_I32,
                                types, args, countof(args));
        LirLabel returned = lir_label(c->L);
        bc_branch(c, LIR_EQ, lir_r(status), lir_i(0), returned);
        LirOpnd result = lir_i(JIT_PACK(JIT_CALL, node->resume_id));
        bc_effect(c, LIR_RET, &result, 1);
        bc_bind(c, returned);
}

static LirReg
bc_reference(BcLir *c, i32 local, bool all)
{
        LirReg ptr = bc_addr(c, c->locals, local * sizeof (Value));
        LirLabel again = lir_label(c->L);
        LirLabel end = lir_label(c->L);
        bc_bind(c, again);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, ptr, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_REF), end);
        LirOpnd mem = lir_m(ptr, LIR_NONE, 1, offsetof(Value, ref));
        c->ok = c->ok && lir_emit_to(c->L, LIR_LD_I64, ptr, &mem, 1);
        if (all) {
                bc_jump(c, again);
        }
        bc_bind(c, end);
        return ptr;
}

static void
bc_assign_value(Ty *ty, Value const *value)
{
        ty->stack.count = value - ty->stack.items + 1;
        DoAssignExec(ty);
}

static void
bc_target(BcLir *c, char const *ip, u8 op)
{
        i32 index;
        memcpy(&index, ip + 1, sizeof index);
        LirReg ptr;
        switch (op) {
        case INSTR_TARGET_CAPTURED:
                ptr = bc_load(c, LIR_LD_I64, LIR_PTR, c->env, index * sizeof (Value *));
                break;
        case INSTR_TARGET_REF:
                ptr = bc_reference(c, index, false);
                break;
        default:
                ptr = bc_addr(c, c->locals, index * sizeof (Value));
                break;
        }
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(c->ty), lir_r(ptr) };
        bc_call(c, vm_jit_push_target, LIR_VOID, types, args, countof(args));
}

static void
bc_mutate(BcLir *c, u8 op)
{
        void *helper;
        switch (op) {
        case INSTR_MUT_ADD: helper = DoMutAdd; break;
        case INSTR_MUT_SUB: helper = DoMutSub; break;
        case INSTR_MUT_MUL: helper = DoMutMul; break;
        case INSTR_MUT_DIV: helper = DoMutDiv; break;
        case INSTR_MUT_MOD: helper = DoMutMod; break;
        case INSTR_MUT_AND: helper = DoMutAnd; break;
        case INSTR_MUT_OR: helper = DoMutOr; break;
        case INSTR_MUT_XOR: helper = DoMutXor; break;
        case INSTR_MUT_SHL: helper = DoMutShl; break;
        case INSTR_MUT_SHR: helper = DoMutShr; break;
        default:
                c->ok = false;
                return;
        }
        bc_stack_count(c);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_BOOL };
        LirOpnd args[] = { lir_r(c->ty), lir_i(1) };
        bc_call(c, helper, LIR_VOID, types, args, countof(args));
}

static void
bc_capture(BcLir *c, char const *ip)
{
        i32 local;
        i32 index;
        memcpy(&local, ip + 1, sizeof local);
        memcpy(&index, ip + 1 + sizeof local, sizeof index);
        LirReg ptr = bc_addr(c, c->locals, local * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(c->ty), lir_r(ptr), lir_r(c->env), lir_i(index) };
        bc_call(c, jit_rt_capture, LIR_VOID, types, args, countof(args));
}

static void
bc_function_literal(BcLir *c, char const *ip, u8 op)
{
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i((uptr)(ip + 1)) };
        void *helper = op == INSTR_FUNCTION ? jit_rt_function : jit_rt_generator;
        bc_call(c, helper, LIR_VOID, types, args, countof(args));
}

static void
bc_yield(BcLir *c, BcLirNode const *node)
{
        if (c->has_try) {
                LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top) };
                void *helper;
                switch (node->op) {
                case INSTR_YIELD:      helper = jit_rt_yield;      break;
                case INSTR_YIELD_SOME: helper = jit_rt_yield_some; break;
                default:              helper = jit_rt_yield_none; break;
                }
                LirReg fp = bc_call(c, helper, LIR_TYPE_I32, types, args, countof(args));
                if (node->op == INSTR_YIELD_NONE) {
                        LirLabel next = lir_label(c->L);
                        bc_branch(c, LIR_GE, lir_r(fp), lir_i(0), next);
                        LirOpnd result = lir_i(JIT_RETURN);
                        bc_effect(c, LIR_RET, &result, 1);
                        bc_bind(c, next);
                }
                return;
        }
        i32 reason;
        switch (node->op) {
        case INSTR_YIELD: reason = JIT_YIELD; break;
        case INSTR_YIELD_SOME: reason = JIT_YIELD_SOME; break;
        default: reason = JIT_YIELD_NONE; break;
        }
        bc_stack_count(c);
        LirOpnd result = lir_i(JIT_PACK(reason, node->resume_id));
        bc_effect(c, LIR_RET, &result, 1);
}

#include "jit_lir_try.h"
#include "jit_lir_call.h"
#include "jit_lir_member.h"
#include "jit_lir_fast.h"
#include "jit_lir_inline.h"
#include "jit_lir_vstack.h"
#include "jit_lir_loop.h"
#include "jit_lir_ops.h"
#include "jit_lir_pattern.h"
#include "jit_lir_state.h"
#include "jit_lir_misc.h"
#include "jit_lir_finish.h"

static void
bc_mark_label(BcLir *c, i32 offset)
{
        if (offset >= 0 && offset < c->size && c->nodes[offset].sp >= 0
            && c->nodes[offset].label == LIR_NONE) {
                c->nodes[offset].label = lir_label(c->L);
        }
}

static u64 OpStatInsts[256];
static u64 OpStatCount[256];

static void
opstat_dump(void)
{
        for (int i = 0; i < 256; ++i) {
                if (OpStatCount[i] != 0) {
                        fprintf(stderr, "opstat %s %llu %llu\n", GetInstructionName(i),
                                (unsigned long long)OpStatCount[i], (unsigned long long)OpStatInsts[i]);
                }
        }
}

__attribute__((constructor)) static void
opstat_init(void)
{
        if (getenv("TY_JIT_OPSTAT") != NULL) {
                atexit(opstat_dump);
        }
}


static JitFn *
bc_lir_compile(Ty *ty, Value const *f)
{
        if (lir_target() == NULL) {
                return NULL;
        }
#ifdef TY_PROFILER
        u64 begin = TyMonotonicTime();
#else
        u64 begin = jit_audit_level() >= 2 ? TyMonotonicTime() : 0;
#endif
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirSig sig = { .ret = LIR_TYPE_I32, .params = types, .nparams = 5, .nfixed = 5 };
        LirError err;
        BcLir c = { .L = lir_new(name_of(f), &sig, LIR_MODE_ATTACHED, &err),
                    .bound = f->info[FUN_INFO_BOUND],
                    .self_index = f->info[FUN_INFO_CLASS] == -1
                                ? -1 : f->info[FUN_INFO_PARAM_COUNT],
                    .ctx = ty, .function = f, .ok = true, .tuple_off = -1 };
        if (c.L == NULL) {
                return NULL;
        }
        c.compact = jit_tier() == 1
                 || ((jit_tier() == 0 || jit_tier() == 3)
                     && !(atomic_load((_Atomic i16 *)flags_of(f)) & FF_JIT_TIER2));
        if (!bc_lir_cfg(&c, f)) {
                if (jit_audit_level() >= 2) {
                        fprintf(stderr, "jit-audit: lir cfg decline %s off=%u op=%s\n",
                                name_of(f), c.offset, GetInstructionName(c.code[c.offset]));
                }
                lir_free(c.L);
                free(c.nodes);
                return NULL;
        }
        if (c.dynamic && c.size > 4096) {
                if (jit_audit_level() >= 2) {
                        fprintf(stderr, "jit-audit: lir decline %s reason=large dynamic stack\n", name_of(f));
                }
                lir_free(c.L);
                free(c.nodes);
                return NULL;
        }
        for (i32 off = 0; off < c.size; ++off) {
                if (c.nodes[off].next != 0 && c.nodes[off].sp >= 0) {
                        if ((!c.has_try && (c.nodes[off].op == INSTR_YIELD
                                || c.nodes[off].op == INSTR_YIELD_SOME
                                || c.nodes[off].op == INSTR_YIELD_NONE))) {
                                c.nodes[off].resume = lir_label(c.L);
                                c.nodes[off].resume_id = ++c.nresume;
                                bc_mark_label(&c, c.nodes[off].next);
                        }
                        if (c.nodes[off].branch && c.nodes[off].target <= off) {
                                c.nodes[off].deopt = lir_label(c.L);
                        }
                        BcLirNode const *node = &c.nodes[off];
                        if (node->branch) {
                                bc_mark_label(&c, node->target);
                        }
                        if (node->op == INSTR_CALL && bc_tail_position(&c, node)) {
                                bc_mark_label(&c, 0);
                        }
                        if (node->op == INSTR_TRY) {
                                bc_mark_label(&c, node->catch_to);
                                bc_mark_label(&c, node->finally_to);
                                bc_mark_label(&c, node->end_to);
                        } else if (node->op == INSTR_FINALLY) {
                                bc_mark_label(&c, node->next);
                        } else if (node->op == INSTR_MATCH_TAG || node->op == INSTR_MATCH_STRING) {
                                for (i32 i = 0; i < node->argc; ++i) {
                                        i32 id;
                                        i32 delta;
                                        char const *slot = node->kw_ip + i * 8;
                                        memcpy(&id, slot, sizeof id);
                                        memcpy(&delta, slot + 4, sizeof delta);
                                        if (id != -1) {
                                                bc_mark_label(&c, slot + 8 - c.code + delta);
                                        }
                                }
                        }
                }
        }
        if (!c.dynamic && getenv("TY_JIT_NO_OSR") == NULL) {
                for (i32 off = 0; off < c.size; ++off) {
                        BcLirNode const *node = &c.nodes[off];
                        if (node->next == 0 || node->sp < 0 || !node->branch || node->target > off) {
                                continue;
                        }
                        BcLirNode *head = &c.nodes[node->target];
                        if (c.has_try && bc_in_try(&c, node->target)) {
                                continue;
                        }
                        if (head->osr_id == 0 && head->label != LIR_NONE && head->sp >= 0) {
                                head->osr = lir_label(c.L);
                                head->osr_id = ++c.nresume;
                                c.nosr += 1;
                        }
                }
        }
        c.ok = lir_pin_param(c.L, LIR_PIN_0, 0)
            && lir_pin_param(c.L, LIR_PIN_1, 2)
            && lir_pin_param(c.L, LIR_PIN_2, 3)
            && lir_pc_param(c.L, 4);
        c.L->ty_param = 0;
        c.L->stable_pins = (1 << LIR_PIN_0) | (1 << LIR_PIN_2);
        c.L->stack_pins = (1 << LIR_PIN_1) | (1 << LIR_PIN_3);
        c.ty = lir_pinned(c.L, LIR_PIN_0);
        c.locals = lir_pinned(c.L, LIR_PIN_1);
        c.env = lir_pinned(c.L, LIR_PIN_2);
        c.ops = lir_pinned(c.L, LIR_PIN_3);
        if (c.dynamic) {
                c.fp = lir_pinned(c.L, LIR_PIN_4);
                c.L->regs[c.fp].cls = LIR_I64;
                LirReg base = bc_load(&c, LIR_LD_I64, LIR_I64, c.ty, offsetof(Ty, stack.items));
                LirOpnd ptr = lir_r(c.locals);
                LirReg bits = bc_value(&c, LIR_BITCAST, LIR_I64, &ptr, 1);
                LirOpnd args[] = { lir_r(bits), lir_r(base) };
                c.ok = c.ok && lir_emit_to(c.L, LIR_SUB, c.fp, args, countof(args));
        }
        LirOpnd mem = lir_m(c.locals, LIR_NONE, 1, c.bound * sizeof (Value));
        c.ok = c.ok && lir_emit_to(c.L, LIR_LEA, c.ops, &mem, 1);
        c.base_index = LIR_NONE;
        if (!c.dynamic) {
                c.base_index = lir_reg(c.L, LIR_I64);
                bc_base_index(&c);
        }
        c.deopt = lir_label(c.L);
        LirLabel normal = lir_label(c.L);
        if (c.nresume != 0) {
                LirLabel *targets = malloc(((usize)c.nresume + 1) * sizeof *targets);
                if (targets == NULL) {
                        lir_free(c.L);
                        free(c.nodes);
                        return NULL;
                }
                targets[0] = normal;
                for (i32 off = 0; off < c.size; ++off) {
                        BcLirNode const *node = &c.nodes[off];
                        if (node->next != 0 && node->resume_id != 0) {
                                targets[node->resume_id] = node->resume;
                        }
                        if (node->next != 0 && node->osr_id != 0) {
                                targets[node->osr_id] = node->osr;
                        }
                }
                LirInst dispatch = {
                        .op = LIR_SWITCH, .dst = LIR_NONE,
                        .args = { lir_r(c.L->params[1]), lir_l(normal) }, .nargs = 2,
                        .targets = targets, .ntargets = c.nresume + 1
                };
                c.ok = c.ok && lir_emit(c.L, &dispatch);
                free(targets);
        }
        bc_bind(&c, normal);
        if (c.max_sp > 240) {
                LirType reserve_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
                LirOpnd reserve_args[] = { lir_r(c.ty), lir_r(c.ops), lir_i(c.max_sp) };
                bc_call(&c, bc_reserve, LIR_VOID, reserve_types,
                        reserve_args, countof(reserve_args));
        }
        static JitDeopt const deopt = {0};
        LirOpnd poll[] = { lir_r(c.ty), lir_r(c.ops), lir_i((uptr)&deopt), lir_l(c.deopt) };
        bc_poll(&c, poll);
        if (c.compact && jit_tier() != 1) {
                c.tier = malloc(sizeof *c.tier);
                if (c.tier != NULL) {
                        *c.tier = jit_tier() == 3 ? 3 : JIT_TIER_BUDGET;
                        bc_tier_check(&c, LIR_NONE);
                }
        }
        c.ok = c.ok && bc_vs_plan(&c, ty, f);
        c.ok = c.ok && bc_loop_plan(&c);
        char const *ip = code_of(f);
        int stat_op = -1;
        u32 stat_n = c.L->ninsts;
        while (c.ok && ip < code_of(f) + c.size) {
                BcLirNode const *node = &c.nodes[ip - code_of(f)];
                if (stat_op >= 0) {
                        OpStatInsts[stat_op] += c.L->ninsts - stat_n;
                }
                stat_op = (u8)*ip;
                OpStatCount[stat_op] += node->sp >= 0;
                stat_n = c.L->ninsts;
                if (node->sp < 0) {
                        ip = StepInstruction(ip);
                        continue;
                }
                c.sp = node->sp;
                bc_loop_leave(&c, ip - code_of(f));
                if (node->label != LIR_NONE) {
                        bc_vs_flush_below(&c, node->sp);
                        bc_loop_enter(&c, ip - code_of(f));
                        bc_vs_forget(&c);
                        bc_bind(&c, node->label);
                }
                if (c.vs != NULL) {
                        for (i32 i = node->sp; i < c.max_sp + 8; ++i) {
                                c.vs[i].kind = VS_MEM;
                                c.vs[i].hint = T2_TYPE_INVALID;
                        }
                        if (c.hints != NULL && node->sp > 0) {
                                T2Type hint = find_type_hint(c.hints, ip - code_of(f));
                                if (hint != T2_TYPE_INVALID) {
                                        c.vs[node->sp - 1].hint = hint;
                                }
                        }
                }
                if (c.dynamic) {
                        bc_dynamic_ops(&c);
                }
                c.offset = StepInstruction(ip) - code_of(f);
                c.at = ip - code_of(f);
#ifdef TY_PROFILER
                bc_stack_count(&c);
                LirType tick_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
                LirOpnd tick_args[] = { lir_r(c.ty), lir_i((uptr)ip) };
                bc_call(&c, jit_profiler_tick, LIR_VOID, tick_types,
                        tick_args, countof(tick_args));
#endif
                u8 op = *ip;
                i32 local;
                u64 bits;
                if (bc_vs_lower(&c, node, ip)) {
                        ip = StepInstruction(ip);
                        if (c.skip_next) {
                                ip = StepInstruction(ip);
                                c.skip_next = false;
                        }
                        continue;
                }
                bc_vs_flush_all(&c);
                bc_vs_forget(&c);
                switch (op) {
                case INSTR_TRY_YIELD_FROM:
                case INSTR_TAIL_CALL:
                case INSTR_DEFINE_TAG:
                case INSTR_DEFINE_CLASS:
                case INSTR_INIT_STATIC_FIELD:
                case INSTR_BAD_CALL:
                case INSTR_BAD_ASSIGN:
                case INSTR_BAD_DISPATCH:
                        bc_finish_op(&c, node, ip);
                        break;
                case INSTR_EXEC_CODE:
                case INSTR_DEBUG:
                case INSTR_REVERSE:
                case INSTR_RENDER_TEMPLATE:
                case INSTR_NAMESPACE:
                case INSTR_TRACE:
                case INSTR_OPERATOR:
                case INSTR_READ_INDEX:
                case INSTR_UNARY_OP:
                case INSTR_QUESTION:
                case INSTR_TO_REGEX:
                case INSTR_COMPILE_REGEX:
                case INSTR_EVAL:
                case INSTR_GET_TAG:
                case INSTR_NONE_IF_NIL:
                case INSTR_RETURN_IF_NOT_NONE:
                case INSTR_BINARY_OP:
                case INSTR_SLICE:
                case INSTR_GET_NEXT:
                case INSTR_FIX_TO:
                case INSTR_FIX_EXTRA:
                case INSTR_TRAP:
                case INSTR_TRAP_TY:
                case INSTR_JUMP_WTF:
                case INSTR_NONE_IF_NOT:
                case INSTR_SKIP_CHECK:
                        bc_misc(&c, node, ip);
                        break;
                case INSTR_JUMP_IF_INIT:
                case INSTR_TARGET_GLOBAL:
                case INSTR_TARGET_THREAD_LOCAL:
                case INSTR_TARGET_SELF_STATIC:
                case INSTR_TARGET_STATIC_MEMBER:
                case INSTR_DROP:
                case INSTR_DISCARD_DROP_GROUP:
                case INSTR_PUSH_DROP_GROUP:
                case INSTR_PUSH_DEFER_GROUP:
                case INSTR_CLEANUP:
                case INSTR_LOAD_THREAD_LOCAL:
                case INSTR_PRE_INC:
                case INSTR_POST_INC:
                case INSTR_PRE_DEC:
                case INSTR_POST_DEC:
                case INSTR_BIND_STATIC:
                case INSTR_SELF_STATIC_ACCESS:
                case INSTR_STATIC_MEMBER_ACCESS:
                case INSTR_MAYBE_ASSIGN:
                case INSTR_DECORATE:
                case INSTR_INTO_METHOD:
                case INSTR_BIND_CLASS:
                case INSTR_BIND_INSTANCE:
                case INSTR_BIND_GETTER:
                case INSTR_BIND_SETTER:
                case INSTR_PUSH_DROP:
                case INSTR_ENTER:
                case INSTR_DEFER:
                case INSTR_ASSIGN_GLOBAL:
                case INSTR_TARGET_DYN_MEMBER:
                        bc_state(&c, node, ip);
                        break;
                case INSTR_ENSURE_LEN:
                case INSTR_ENSURE_LEN_TUPLE:
                case INSTR_ENSURE_EQUALS_VAR:
                case INSTR_TRY_UNAPPLY:
                case INSTR_TRY_ASSIGN_NON_NIL:
                case INSTR_TRY_RANGE:
                case INSTR_TRY_INCRANGE:
                case INSTR_ENSURE_DICT:
                case INSTR_ENSURE_CONTAINS:
                case INSTR_ENSURE_SAME_KEYS:
                case INSTR_TRY_INDEX:
                case INSTR_INDEX_TUPLE:
                case INSTR_TRY_INDEX_TUPLE:
                case INSTR_TRY_MEMBER:
                case INSTR_TRY_TUPLE_MEMBER:
                case INSTR_TRY_TAG_POP:
                case INSTR_TRY_REGEX:
                case INSTR_TRY_STEAL_TAG:
                case INSTR_ARRAY_REST:
                case INSTR_TUPLE_REST:
                case INSTR_RECORD_REST:
                case INSTR_JNI:
                case INSTR_JII:
                case INSTR_MATCH_TAG:
                case INSTR_MATCH_STRING:
                        if (bc_pattern(&c, node, ip)) {
                                ip = StepInstruction(ip);
                        }
                        break;
                case INSTR_UNAPPLY:
                case INSTR_PUSH_ARRAY_ELEM:
                case INSTR_PUSH_TUPLE_ELEM:
                case INSTR_PUSH_TUPLE_MEMBER:
                case INSTR_PUSH_UNTAGGED:
                case INSTR_UNTAG_OR_DIE:
                case INSTR_STEAL_TAG:
                case INSTR_THROW_IF_NIL:
                case INSTR_BAD_MATCH:
                case INSTR_ASSIGN_REGEX_MATCHES:
                {
                        LirReg top = bc_addr(&c, c.ops, c.sp * sizeof (Value));
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
                        LirOpnd args[] = { lir_r(c.ty), lir_r(top), lir_i((uptr)ip) };
                        bc_call(&c, bc_destructure, LIR_VOID, types, args, countof(args));
                        if (op == INSTR_BAD_MATCH) {
                                c.L->insts[c.last_call].flags |= LIR_NORETURN;
                        }
                        break;
                }
                case INSTR_UNPOP:
                        ++c.sp;
                        break;
                case INSTR_DROP2:
                        bc_value_copy(&c, c.ops, (c.sp - 3) * sizeof (Value),
                                      c.ops, (c.sp - 1) * sizeof (Value));
                        c.sp -= 2;
                        break;
                case INSTR_PUSH_NTH:
                        memcpy(&local, ip + 1, sizeof local);
                        bc_value_copy(&c, c.ops, c.sp * sizeof (Value),
                                      c.ops, (c.sp - 1 - local) * sizeof (Value));
                        ++c.sp;
                        break;
                case INSTR_ARRAY_COMPR:
                case INSTR_SET_COMPR:
                case INSTR_DICT_COMPR:
                case INSTR_PUSH_INDEX:
                case INSTR_LOOP_CHECK:
                case INSTR_SPREAD_CHECK:
                case INSTR_ASSIGN_SUBSCRIPT:
                case INSTR_ARRAY:
                case INSTR_ARRAY0:
                case INSTR_SET:
                case INSTR_DICT:
                case INSTR_DEFAULT_DICT:
                case INSTR_GATHER_TUPLE:
                case INSTR_TUPLE:
                case INSTR_XTUPLE:
                case INSTR_STRING:
                case INSTR_SELF:
                case INSTR_CLASS:
                case INSTR_TAG:
                case INSTR_REGEX:
                case INSTR_TYPE:
                case INSTR_VALUE:
                case INSTR_CONCAT_STRINGS:
                case INSTR_MEMBER_ACCESS:
                case INSTR_SELF_MEMBER_ACCESS:
                case INSTR_TRY_MEMBER_ACCESS:
                case INSTR_SUBSCRIPT:
                case INSTR_SAFE_SUBSCRIPT:
                case INSTR_GET_MEMBER:
                case INSTR_TRY_GET_MEMBER:
                case INSTR_TAG_PUSH:
                case INSTR_NEG:
                case INSTR_NOT:
                case INSTR_INC:
                case INSTR_DEC:
                case INSTR_TO_STRING:
                case INSTR_COUNT:
                case INSTR_CLASS_OF:
                case INSTR_DIV:
                case INSTR_CMP:
                case INSTR_CHECK_MATCH:
                case INSTR_MOD:
                case INSTR_BIT_AND:
                case INSTR_BIT_OR:
                case INSTR_BIT_XOR:
                case INSTR_SHL:
                case INSTR_SHR:
                case INSTR_RANGE:
                case INSTR_INCRANGE:
                case INSTR_SWAP:
                case INSTR_POP2:
                case INSTR_DUP2_SWAP:
                        bc_more(&c, node, ip);
                        break;
                case INSTR_TRY:
                case INSTR_CATCH:
                case INSTR_RETHROW:
                case INSTR_FINALLY:
                case INSTR_POP_TRY:
                case INSTR_END_TRY:
                        bc_try(&c, node);
                        break;
                case INSTR_SAVE_STACK_POS:
                case INSTR_RESTORE_STACK_POS:
                case INSTR_POP_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                case INSTR_POP_STACK_POS_POP2:
                case INSTR_DROP_STACK_POS:
                case INSTR_CLEAR_EXTRA:
                        bc_saved_stack(&c, op);
                        break;
                case INSTR_SENTINEL:
                        bc_literal(&c, VALUE_SENTINEL, 0);
                        break;
                case INSTR_CHECK_INIT:
                        break;
                case INSTR_NOP:
                case INSTR_HALT:
                        break;
                case INSTR_LOAD_LOCAL:
                        memcpy(&local, ip + 1, sizeof local);
                        bc_local_load(&c, local);
                        if (c.vs != NULL && c.local_type != NULL && local >= 0 && local < c.bound) {
                                c.vs[c.sp - 1].hint = c.local_type[local];
                        }
                        break;
                case INSTR_LOAD_GLOBAL: {
                        memcpy(&local, ip + 1, sizeof local);
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I32 };
                        LirOpnd args[] = { lir_r(c.ty), lir_i(local) };
                        LirReg ptr = bc_call(&c, vm_global, LIR_TYPE_PTR, types, args, countof(args));
                        bc_value_copy(&c, c.ops, c.sp++ * sizeof (Value), ptr, 0);
                        break;
                }
                case INSTR_LOAD_CAPTURED: {
                        memcpy(&local, ip + 1, sizeof local);
                        LirReg ptr = bc_load(&c, LIR_LD_I64, LIR_PTR, c.env, local * sizeof (Value *));
                        bc_value_copy(&c, c.ops, c.sp++ * sizeof (Value), ptr, 0);
                        break;
                }
                case INSTR_LOAD_REF: {
                        memcpy(&local, ip + 1, sizeof local);
                        LirReg ptr = bc_reference(&c, local, true);
                        bc_value_copy(&c, c.ops, c.sp++ * sizeof (Value), ptr, 0);
                        break;
                }
                case INSTR_LOOP_ITER:
                        if (bc_fast_loop(&c, node)) {
                                ip = StepInstruction(ip);
                                break;
                        }
                        bc_more(&c, node, ip);
                        break;
                case INSTR_TARGET_SUBSCRIPT:
                        if (bc_fast_target_subscript(&c, node)) {
                                ip = StepInstruction(ip);
                                break;
                        }
                        bc_more(&c, node, ip);
                        break;
                case INSTR_TARGET_LOCAL:
                        if (bc_fast_target_local(&c, node, ip)) {
                                ip = StepInstruction(ip);
                                break;
                        }
                        bc_target(&c, ip, op);
                        break;
                case INSTR_TARGET_MEMBER:
                case INSTR_TARGET_SELF_MEMBER:
                        if (bc_member_assign(&c, node, ip)) {
                                ip = StepInstruction(ip);
                        } else {
                                bc_more(&c, node, ip);
                        }
                        break;
                case INSTR_TARGET_CAPTURED:
                case INSTR_TARGET_REF:
                        bc_target(&c, ip, op);
                        break;
                case INSTR_MUT_ADD:
                case INSTR_MUT_SUB:
                case INSTR_MUT_MUL:
                case INSTR_MUT_DIV:
                case INSTR_MUT_MOD:
                case INSTR_MUT_AND:
                case INSTR_MUT_OR:
                case INSTR_MUT_XOR:
                case INSTR_MUT_SHL:
                case INSTR_MUT_SHR:
                        bc_mutate(&c, op);
                        break;
                case INSTR_ASSIGN: {
                        LirReg ptr = bc_addr(&c, c.ops, (c.sp - 1) * sizeof (Value));
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
                        LirOpnd args[] = { lir_r(c.ty), lir_r(ptr) };
                        bc_call(&c, bc_assign_value, LIR_VOID, types, args, countof(args));
                        break;
                }
                case INSTR_CAPTURE:
                        bc_capture(&c, ip);
                        break;
                case INSTR_FUNCTION:
                case INSTR_GENERATOR:
                        bc_function_literal(&c, ip, op);
                        break;
                case INSTR_PATCH_ENV: {
                        memcpy(&local, ip + 1, sizeof local);
                        LirReg ptr = bc_addr(&c, c.ops, (c.sp - 1) * sizeof (Value));
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
                        LirOpnd args[] = { lir_r(c.ty), lir_r(ptr), lir_i(local) };
                        bc_call(&c, jit_rt_patch_env, LIR_VOID, types, args, countof(args));
                        break;
                }
                case INSTR_YIELD:
                case INSTR_YIELD_SOME:
                case INSTR_YIELD_NONE:
                        bc_yield(&c, node);
                        break;
                case INSTR_THROW: {
                        LirReg ptr = bc_addr(&c, c.ops, (c.sp - 1) * sizeof (Value));
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
                        LirOpnd args[] = { lir_r(c.ty), lir_r(ptr) };
                        bc_call(&c, jit_rt_throw, LIR_VOID, types, args, countof(args));
                        c.L->insts[c.last_call].flags |= LIR_NORETURN;
                        break;
                }
                case INSTR_ASSIGN_LOCAL:
                        memcpy(&local, ip + 1, sizeof local);
                        bc_local_store(&c, local);
                        break;
                case INSTR_INT8:
                        bc_literal(&c, VALUE_INTEGER, (i8)ip[1]);
                        break;
                case INSTR_INTEGER:
                case INSTR_REAL:
                        memcpy(&bits, ip + 1, sizeof bits);
                        bc_literal(&c, op == INSTR_REAL ? VALUE_REAL : VALUE_INTEGER, bits);
                        break;
                case INSTR_TRUE:  bc_literal(&c, VALUE_BOOLEAN, 1); break;
                case INSTR_FALSE: bc_literal(&c, VALUE_BOOLEAN, 0); break;
                case INSTR_NIL:   bc_literal(&c, VALUE_NIL, 0); break;
                case INSTR_NONE:  bc_literal(&c, VALUE_NONE, 0); break;
                case INSTR_DUP:
                        bc_value_copy(&c, c.ops, c.sp * sizeof (Value), c.ops, (c.sp - 1) * sizeof (Value));
                        ++c.sp;
                        break;
                case INSTR_POP:
                        --c.sp;
                        break;
                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                case INSTR_EQ:
                case INSTR_NEQ:
                case INSTR_LT:
                case INSTR_GT:
                case INSTR_LEQ:
                case INSTR_GEQ:
                        if (!bc_inline_operator(&c, op)) {
                                bc_numeric(&c, op);
                        }
                        break;
                case INSTR_CALL:
                case INSTR_CALL_GLOBAL:
                case INSTR_CALL_METHOD:
                case INSTR_TRY_CALL_METHOD:
                case INSTR_CALL_SELF_METHOD:
                case INSTR_CALL_STATIC_METHOD:
                case INSTR_CALL_SELF_STATIC:
                        bc_invoke(&c, node);
                        break;
                case INSTR_RETURN:
                case INSTR_RETURN_PRESERVE_CTX: {
                        bc_stack_count(&c);
                        LirOpnd ret = lir_i(JIT_RETURN);
                        bc_effect(&c, LIR_RET, &ret, 1);
                        break;
                }
                case INSTR_JUMP:
                case INSTR_JUMP_IF_TYPE:
                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE:
                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JUMP_IF_NIL:
                case INSTR_JUMP_IF_SENTINEL:
                case INSTR_JUMP_IF_NONE:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR:
                        bc_control(&c, node);
                        break;
                default:
                        c.ok = false;
                        break;
                }
                if (c.dynamic && bc_sync_after(op)
                    && !((op == INSTR_CALL || op == INSTR_CALL_GLOBAL
                       || op == INSTR_CALL_METHOD || op == INSTR_TRY_CALL_METHOD
                       || op == INSTR_CALL_SELF_METHOD || op == INSTR_CALL_STATIC_METHOD
                       || op == INSTR_CALL_SELF_STATIC) && node->argc == -1)) {
                        c.sp = node->fall_sp;
                        bc_stack_count(&c);
                }
                ip = StepInstruction(ip);
        }
        for (i32 off = 0; off < c.size; ++off) {
                BcLirNode const *node = &c.nodes[off];
                if (node->next != 0 && node->osr_id != 0) {
                        c.ok = c.ok && lir_entry(c.L, node->osr);
                        c.L->insts[c.L->ninsts - 1].tag = off;
                        if (c.base_index != LIR_NONE) {
                                bc_base_index(&c);
                        }
                        bc_loop_osr(&c, off, node->sp);
                        bc_jump(&c, node->label);
                }
                if (node->next != 0 && node->resume_id != 0) {
                        c.ok = c.ok && lir_entry(c.L, node->resume);
                        c.L->insts[c.L->ninsts - 1].tag = node->next;
                        if (c.base_index != LIR_NONE) {
                                bc_base_index(&c);
                        }
                        bc_jump(&c, c.nodes[node->next].label);
                }
        }
        bc_loop_stubs(&c);
        bc_bind(&c, c.deopt);
        LirOpnd ret = lir_i(JIT_PACK(JIT_DEOPT, 0));
        bc_effect(&c, LIR_RET, &ret, 1);
        for (i32 off = 0; off < c.size; ++off) {
                if (c.nodes[off].deopt != LIR_NONE && c.nodes[off].next != 0
                    && c.nodes[off].sp >= 0) {
                        bc_bind(&c, c.nodes[off].deopt);
                        ret = lir_i(JIT_PACK(JIT_DEOPT, off));
                        bc_effect(&c, LIR_RET, &ret, 1);
                }
        }
        u32 ninsts = c.L->ninsts;
        u32 nregs = c.L->nregs;
        u32 *osr = c.nosr != 0 ? malloc(2 * c.nosr * sizeof *osr) : NULL;
        u32 nosr = 0;
        if (osr != NULL) {
                for (i32 off = 0; off < c.size; ++off) {
                        if (c.nodes[off].next != 0 && c.nodes[off].osr_id != 0) {
                                osr[2 * nosr] = off;
                                osr[2 * nosr + 1] = c.nodes[off].osr_id;
                                nosr += 1;
                        }
                }
        }
        LirCode *code = c.ok ? lir_finish_owned(c.L, &err) : NULL;
        lir_free(c.L);
        free(c.nodes);
        free(c.vs);
        free(c.local_class);
        free(c.local_type);
        free(c.known);
        free(c.known_gen);
        for (i32 i = 0; i < c.nloops; ++i) {
                free(c.loops[i].live);
        }
        free(c.loops);
        free(c.lreg);
        free(c.spin);
        free(c.active);
        if (code == NULL) {
                free(osr);
                free(c.tier);
                if (jit_audit_level() >= 2) {
                        fprintf(stderr, "jit-audit: lir decline %s op=%u reason=%s\n",
                                name_of(f), err.op, err.message);
                }
                return NULL;
        }
        if (jit_audit_level() >= 2) {
                fprintf(stderr, "jit-audit: lir %s native=%zu insts=%u regs=%u bc=%d dynamic=%d try=%d compile_us=%llu\n",
                        name_of(f), code->size, ninsts, nregs, c.size, c.dynamic, c.has_try,
                        (unsigned long long)((TyMonotonicTime() - begin) / 1000));
        }
#ifdef TY_PROFILER
        Expr const *expr = !from_eval(f) ? expr_of(f) : NULL;
        u64 elapsed = TyMonotonicTime() - begin;
        TySpinLockLock(&JitLogMutex);
        jit_total_compile_ns += elapsed;
        jit_total_native_bytes += code->size;
        xvP(jit_compile_log, ((JitCompileRecord) {
                .name = name_of(f),
                .class_name = expr != NULL && expr->class != NULL
                            ? expr->class->name : "",
                .expr = expr,
                .native_size = code->size,
                .compile_time_ns = elapsed,
                .bc_code_size = c.size
        }));
        TySpinLockUnlock(&JitLogMutex);
#endif
        code->osr = osr;
        code->nosr = nosr;
        code->tier = c.tier;
        bc_perf_map(code->body, code->size, name_of(f),
                    !from_eval(f) ? expr_of(f) : NULL);
        code = lir_code_adopt(ty, code);
        set_jit_code_of(f, code);
        if (!from_eval(f)) {
                Value root = { .type = VALUE_PTR, .ptr = code, .gcptr = code };
                gc_immortalize(ty, &root);
        }
        return code->body;
}
