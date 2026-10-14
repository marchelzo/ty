static void
bc_misc(BcLir *c, BcLirNode const *node, char const *ip)
{
        LirType ptr = LIR_TYPE_PTR;
        LirType integer = LIR_TYPE_I32;
        i32 n = 0;
        uptr data = 0;
        bc_stack_count(c);
        switch (node->op) {
        case INSTR_TRAP_TY: {
                LirOpnd result = lir_i(JIT_PACK(JIT_DEOPT, ip - c->code));
                bc_effect(c, LIR_RET, &result, 1);
                return;
        }
        case INSTR_RETURN_IF_NOT_NONE: {
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->ops,
                                     (c->sp - 1) * sizeof (Value) + offsetof(Value, type));
                LirLabel next = lir_label(c->L);
                bc_branch(c, LIR_EQ, lir_r(type), lir_i(VALUE_NONE), next);
                LirOpnd result = lir_i(JIT_RETURN);
                bc_effect(c, LIR_RET, &result, 1);
                bc_bind(c, next);
                return;
        }
        case INSTR_JUMP_WTF:
        case INSTR_NONE_IF_NOT:
        case INSTR_SKIP_CHECK: {
                LirType types[] = { ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->op) };
                LirReg taken = bc_call(c, vm_jit_extra_branch, LIR_TYPE_BOOL, types, args, countof(args));
                bc_branch(c, LIR_NE, lir_r(taken), lir_i(0), c->nodes[node->target].label);
                return;
        }
        case INSTR_UNARY_OP:
        case INSTR_BINARY_OP:
        case INSTR_FIX_TO:
        case INSTR_REVERSE:
        case INSTR_OPERATOR:
                memcpy(&n, ip + 1, sizeof n);
                data = (uptr)(ip + 5);
                break;
        case INSTR_EXEC_CODE:
        case INSTR_EVAL:
        case INSTR_RENDER_TEMPLATE:
        case INSTR_NAMESPACE:
                memcpy(&data, ip + 1, sizeof data);
                break;
        case INSTR_COMPILE_REGEX:
        case INSTR_DEBUG:
                data = (uptr)(ip + 1);
                break;
        default:
                break;
        }
        LirType types[] = { ptr, integer, integer, ptr };
        LirOpnd args[] = { lir_r(c->ty), lir_i(node->op), lir_i(n), lir_i(data) };
        bc_call(c, vm_jit_misc, LIR_VOID, types, args, countof(args));
        if (node->op == INSTR_TRAP) {
                c->L->insts[c->L->ninsts - 1].flags |= LIR_NORETURN;
        }
}
