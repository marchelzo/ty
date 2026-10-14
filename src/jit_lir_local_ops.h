static void
bc_cached_arithmetic(BcLir *c, BcLocal const *local, u8 op, bool floating)
{
        LirClass cls = floating ? LIR_F64 : LIR_I64;
        LirReg left = local->regs[1];
        if (floating != local->floating) {
                LirOpnd bits = lir_r(left);
                left = bc_value(c, LIR_BITCAST, cls, &bits, 1);
        }
        LirReg right = bc_load(c, floating ? LIR_LD_F64 : LIR_LD_I64, cls, c->ops,
                              (c->sp - 1) * sizeof (Value) + offsetof(Value, z));
        LirOp operation;
        switch (op) {
        case INSTR_MUT_ADD: operation = floating ? LIR_FADD : LIR_ADD; break;
        case INSTR_MUT_SUB: operation = floating ? LIR_FSUB : LIR_SUB; break;
        default:           operation = floating ? LIR_FMUL : LIR_MUL; break;
        }
        LirOpnd args[] = { lir_r(left), lir_r(right) };
        LirReg result = bc_value(c, operation, cls, args, countof(args));
        LirOpnd value = lir_r(result);
        if (floating != local->floating) {
                result = bc_value(c, LIR_BITCAST, local->floating ? LIR_F64 : LIR_I64, &value, 1);
                value = lir_r(result);
        }
        c->ok = c->ok && lir_emit_to(c->L, LIR_MOV, local->regs[1], &value, 1);
        bc_cached_store(c, local, c->ops, (c->sp - 1) * sizeof (Value));
}

static bool
bc_cached_target(BcLir *c, BcLirNode const *node, char const *ip)
{
        if (c->cache_at == NULL || node->next >= c->size) {
                return false;
        }
        i32 slot;
        memcpy(&slot, ip + 1, sizeof slot);
        i32 index = c->cache_at[slot];
        BcLirNode const *next = &c->nodes[node->next];
        if (index < 0 || next->label != LIR_NONE || next->sp != node->sp
            || (next->op != INSTR_ASSIGN && next->op != INSTR_MUT_ADD
                && next->op != INSTR_MUT_SUB && next->op != INSTR_MUT_MUL)) {
                return false;
        }
        BcLocal const *local = &c->cached[index];
        c->offset = next->next;
#ifdef TY_PROFILER
        LirType tick_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd tick_args[] = { lir_r(c->ty), lir_i((uptr)(c->code + node->next)) };
        bc_stack_count(c);
        bc_call(c, jit_profiler_tick, LIR_VOID, tick_types, tick_args, countof(tick_args));
#endif
        if (next->op == INSTR_ASSIGN) {
                bc_cached_load(c, local, c->ops, (c->sp - 1) * sizeof (Value));
                return true;
        }
        LirLabel real = lir_label(c->L);
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirOpnd mask[] = { lir_r(local->regs[0]), lir_i(UINT8_MAX) };
        LirReg type = bc_value(c, LIR_AND, LIR_I64, mask, countof(mask));
        LirReg right = bc_load(c, LIR_LD_U8, LIR_I64, c->ops,
                              (c->sp - 1) * sizeof (Value) + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), real);
        bc_branch(c, LIR_NE, lir_r(right), lir_i(VALUE_INTEGER), real);
        bc_cached_arithmetic(c, local, next->op, false);
        bc_jump(c, done);
        bc_bind(c, real);
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_REAL), slow);
        bc_branch(c, LIR_NE, lir_r(right), lir_i(VALUE_REAL), slow);
        bc_cached_arithmetic(c, local, next->op, true);
        bc_jump(c, done);
        bc_bind(c, slow);
        bc_target(c, ip, INSTR_TARGET_LOCAL);
        bc_mutate(c, next->op);
        bc_bind(c, done);
        return true;
}
