static void
bc_state(BcLir *c, BcLirNode const *node, char const *ip)
{
        LirType ptr = LIR_TYPE_PTR;
        LirType integer = LIR_TYPE_I32;
        i32 n = 0;
        i32 z = 0;
        uptr info = 0;
        switch (node->op) {
        case INSTR_DECORATE:
                memcpy(&info, ip + 1, sizeof info);
                break;
        case INSTR_LOAD_THREAD_LOCAL:
        case INSTR_TARGET_GLOBAL:
        case INSTR_TARGET_THREAD_LOCAL:
        case INSTR_TARGET_SELF_STATIC:
        case INSTR_ASSIGN_GLOBAL:
        case INSTR_INTO_METHOD:
        case INSTR_BIND_CLASS:
        case INSTR_SELF_STATIC_ACCESS:
                memcpy(&n, ip + 1, sizeof n);
                break;
        case INSTR_TARGET_STATIC_MEMBER:
        case INSTR_STATIC_MEMBER_ACCESS:
        case INSTR_BIND_INSTANCE:
        case INSTR_BIND_GETTER:
        case INSTR_BIND_SETTER:
        case INSTR_BIND_STATIC:
                memcpy(&n, ip + 1, sizeof n);
                memcpy(&z, ip + 5, sizeof z);
                break;
        default:
                break;
        }
        bc_stack_count(c);
        switch (node->op) {
        case INSTR_JUMP_IF_INIT: {
                LirOpnd arg = lir_r(c->ty);
                LirReg initialized = bc_call(c, vm_jit_check_init, LIR_TYPE_BOOL, &ptr, &arg, 1);
                bc_branch(c, LIR_NE, lir_r(initialized), lir_i(0), c->nodes[node->target].label);
                return;
        }
        case INSTR_LOAD_THREAD_LOCAL:
        case INSTR_ASSIGN_GLOBAL: {
                LirType types[] = { ptr, integer, LIR_TYPE_BOOL };
                LirOpnd args[] = { lir_r(c->ty), lir_i(n), lir_i(node->op == INSTR_LOAD_THREAD_LOCAL) };
                LirReg slot = bc_call(c, vm_jit_state_slot, ptr, types, args, countof(args));
                if (node->op == INSTR_LOAD_THREAD_LOCAL) {
                        bc_value_copy(c, c->ops, c->sp++ * sizeof (Value), slot, 0);
                } else {
                        bc_value_copy(c, slot, 0, c->ops, --c->sp * sizeof (Value));
                }
                return;
        }
        case INSTR_TARGET_GLOBAL:
        case INSTR_TARGET_THREAD_LOCAL:
        case INSTR_TARGET_SELF_STATIC:
        case INSTR_TARGET_STATIC_MEMBER:
        case INSTR_TARGET_DYN_MEMBER: {
                LirType types[] = { ptr, integer, integer, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->op), lir_i(n), lir_i(z) };
                bc_call(c, vm_jit_target, LIR_VOID, types, args, countof(args));
                c->sp -= node->op == INSTR_TARGET_DYN_MEMBER ? 2 : 0;
                return;
        }
        case INSTR_MAYBE_ASSIGN:
        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC: {
                LirType types[] = { ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->op) };
                bc_call(c, vm_jit_mutation, LIR_VOID, types, args, countof(args));
                c->sp += node->op != INSTR_MAYBE_ASSIGN;
                return;
        }
        case INSTR_PUSH_DEFER_GROUP:
                return;
        case INSTR_DROP:
        case INSTR_DISCARD_DROP_GROUP:
        case INSTR_PUSH_DROP_GROUP:
        case INSTR_PUSH_DROP:
        case INSTR_DEFER:
        case INSTR_CLEANUP:
        case INSTR_ENTER: {
                LirType types[] = { ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->op) };
                bc_call(c, vm_jit_scope, LIR_VOID, types, args, countof(args));
                c->sp -= node->op == INSTR_DEFER;
                return;
        }
        default: {
                LirType types[] = { ptr, integer, integer, integer, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->op), lir_i(n), lir_i(z), lir_i(info) };
                bc_call(c, vm_jit_binding, LIR_VOID, types, args, countof(args));
                c->sp += node->op == INSTR_BIND_STATIC
                      || node->op == INSTR_SELF_STATIC_ACCESS
                      || node->op == INSTR_STATIC_MEMBER_ACCESS;
                return;
        }
        }
}
