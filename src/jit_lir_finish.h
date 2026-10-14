static void
bc_reserve(Ty *ty, Value *base, i32 n)
{
        usize required = base - ty->stack.items + n;
        if (required > ty->stack.capacity) {
                xvR(ty->stack, required);
        }
}

static void
bc_tail(Ty *ty, Value *locals, Value *args, i32 argc, i32 bound, i32 kept)
{
        jit_rt_tail_loop(locals, args, argc, bound, kept);
        ty->stack.count = locals - ty->stack.items + bound;
}

static void
bc_finish_op(BcLir *c, BcLirNode const *node, char const *ip)
{
        LirType ptr = LIR_TYPE_PTR;
        LirType integer = LIR_TYPE_I32;
        bc_stack_count(c);
        if (node->op == INSTR_TRY_YIELD_FROM) {
                LirOpnd arg = lir_r(c->ty);
                LirReg direct = bc_call(c, vm_jit_yield_from, LIR_TYPE_BOOL, &ptr, &arg, 1);
                bc_branch(c, LIR_NE, lir_r(direct), lir_i(0), c->nodes[node->target].label);
                return;
        }
        if (node->op == INSTR_TAIL_CALL) {
                LirOpnd allocation[] = { lir_i(sizeof (JitDeopt)), lir_i(alignof (JitDeopt)) };
                LirReg info = bc_value(c, LIR_ALLOCA, LIR_PTR, allocation, countof(allocation));
                bc_store(c, LIR_ST32, info, offsetof(JitDeopt, sp), lir_i(c->sp));
                bc_store(c, LIR_ST32, info, offsetof(JitDeopt, nsave), lir_i(0));
                LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
                LirOpnd poll[] = { lir_r(c->ty), lir_r(top), lir_r(info), lir_l(node->deopt) };
                bc_poll(c, poll);
                LirReg args = bc_addr(c, c->ops, (c->sp - node->argc) * sizeof (Value));
                LirType types[] = { ptr, ptr, ptr, integer, integer, integer };
                LirOpnd values[] = { lir_r(c->ty), lir_r(c->locals), lir_r(args),
                                     lir_i(node->argc), lir_i(c->bound), lir_i(node->member) };
                bc_call(c, bc_tail, LIR_VOID, types, values, countof(values));
                bc_jump(c, c->nodes[0].label);
                return;
        }
        if (node->op == INSTR_DEFINE_TAG || node->op == INSTR_DEFINE_CLASS
            || node->op == INSTR_INIT_STATIC_FIELD) {
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_i((uptr)ip) };
                bc_call(c, vm_jit_declaration, LIR_VOID, types, args, countof(args));
                return;
        }
        LirType types[] = { ptr, integer, ptr };
        LirOpnd args[] = { lir_r(c->ty), lir_i(node->op), lir_i((uptr)ip) };
        bc_call(c, vm_jit_failure, LIR_VOID, types, args, countof(args));
        LirOpnd result = lir_i(JIT_RETURN);
        bc_effect(c, LIR_RET, &result, 1);
}
