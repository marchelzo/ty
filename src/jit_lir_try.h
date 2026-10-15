static void
bc_dynamic_ops(BcLir *c)
{
        LirReg base = bc_load(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, stack.items));
        LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, stack.count));
        LirOpnd sub[] = { lir_r(count), lir_i(c->sp) };
        LirReg index = bc_value(c, LIR_SUB, LIR_I64, sub, countof(sub));
        LirOpnd shift[] = { lir_r(index), lir_i(5) };
        index = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd mem = lir_m(base, index, 1, 0);
        c->ok = c->ok && lir_emit_to(c->L, LIR_LEA, c->ops, &mem, 1);
}

static void
bc_restore_locals(BcLir *c)
{
        LirReg base = bc_load(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, stack.items));
        LirOpnd mem = lir_m(base, c->fp, 1, 0);
        c->ok = c->ok && lir_emit_to(c->L, LIR_LEA, c->locals, &mem, 1);
}

static void *
bc_push_try(Ty *ty, Value *top, char *catch_addr, char *finally_addr, char *end_addr)
{
        ty->stack.count = top - ty->stack.items;
        return vm_jit_push_try(ty, catch_addr, finally_addr, end_addr);
}

static void
bc_stack_save(Ty *ty)
{
        xvP(ty->st->sps, ty->stack.count);
}

static void
bc_stack_restore(Ty *ty)
{
        ty->stack.count = v_L(ty->st->sps);
}

static void
bc_stack_pop(Ty *ty)
{
        ty->stack.count = vXx(ty->st->sps);
}

static void
bc_stack_pop_one(Ty *ty)
{
        ty->stack.count = vXx(ty->st->sps) - 1;
}

static void
bc_stack_pop_two(Ty *ty)
{
        ty->stack.count = vXx(ty->st->sps) - 2;
}

static void
bc_stack_drop(Ty *ty)
{
        vXx(ty->st->sps);
}

static void
bc_clear_extra(Ty *ty)
{
        while (ty->stack.items[ty->stack.count - 1].type != VALUE_SENTINEL) {
                --ty->stack.count;
        }
        --ty->stack.count;
}

static bool
bc_inline_saved_stack(BcLir *c, u8 op)
{
        i32 drop;
        switch (op) {
        case INSTR_SAVE_STACK_POS:      drop = -1; break;
        case INSTR_POP_STACK_POS:       drop = 0;  break;
        case INSTR_POP_STACK_POS_POP:   drop = 1;  break;
        case INSTR_POP_STACK_POS_POP2:  drop = 2;  break;
        case INSTR_DROP_STACK_POS:      drop = -2; break;
        default:                        return false;
        }
        if (c->dynamic || c->compact || c->base_index == LIR_NONE) {
                return false;
        }
        LirReg st = bc_load(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, st));
        LirReg n = bc_load(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, sps.count));
        if (drop == -1) {
                LirLabel slow = lir_label(c->L);
                LirLabel done = lir_label(c->L);
                LirReg cap = bc_load(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, sps.capacity));
                bc_branch(c, LIR_UGE, lir_r(n), lir_r(cap), slow);
                LirReg count = c->base_index;
                if (c->sp != 0) {
                        LirOpnd add[] = { lir_r(c->base_index), lir_i(c->sp) };
                        count = bc_value(c, LIR_ADD, LIR_I64, add, countof(add));
                }
                LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, st, offsetof(co_state, sps.items));
                LirOpnd at = lir_m(items, n, sizeof (usize), 0);
                LirOpnd store[] = { at, lir_r(count) };
                c->ok = c->ok && lir_emit_to(c->L, LIR_ST64, LIR_NONE, store, countof(store));
                LirOpnd one[] = { lir_r(n), lir_i(1) };
                LirReg next = bc_value(c, LIR_ADD, LIR_I64, one, countof(one));
                bc_store(c, LIR_ST64, st, offsetof(co_state, sps.count), lir_r(next));
                bc_jump(c, done);
                bc_bind(c, slow);
                LirType type = LIR_TYPE_PTR;
                LirOpnd arg = lir_r(c->ty);
                bc_call(c, bc_stack_save, LIR_VOID, &type, &arg, 1);
                bc_bind(c, done);
                return true;
        }
        LirOpnd minus[] = { lir_r(n), lir_i(-1) };
        LirReg last = bc_value(c, LIR_ADD, LIR_I64, minus, countof(minus));
        bc_store(c, LIR_ST64, st, offsetof(co_state, sps.count), lir_r(last));
        if (drop >= 0) {
                LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, st, offsetof(co_state, sps.items));
                LirOpnd at = lir_m(items, last, sizeof (usize), 0);
                LirReg count = bc_value(c, LIR_LD_I64, LIR_I64, &at, 1);
                if (drop != 0) {
                        LirOpnd less[] = { lir_r(count), lir_i(-drop) };
                        count = bc_value(c, LIR_ADD, LIR_I64, less, countof(less));
                }
                bc_store(c, LIR_ST64, c->ty, offsetof(Ty, stack.count), lir_r(count));
        }
        return true;
}

static void
bc_saved_stack(BcLir *c, u8 op)
{
        void *helper;
        switch (op) {
        case INSTR_SAVE_STACK_POS:      helper = bc_stack_save; break;
        case INSTR_RESTORE_STACK_POS:   helper = bc_stack_restore; break;
        case INSTR_POP_STACK_POS:       helper = bc_stack_pop; break;
        case INSTR_POP_STACK_POS_POP2:  helper = bc_stack_pop_two; break;
        case INSTR_POP_STACK_POS_POP:   helper = bc_stack_pop_one; break;
        case INSTR_DROP_STACK_POS:      helper = bc_stack_drop; break;
        default:                       helper = bc_clear_extra; break;
        }
        if (c->dynamic || op == INSTR_SAVE_STACK_POS || op == INSTR_DROP_STACK_POS
            || op == INSTR_CLEAR_EXTRA) {
                bc_stack_count(c);
        }
        if (bc_inline_saved_stack(c, op)) {
                return;
        }
        LirType type = LIR_TYPE_PTR;
        LirOpnd arg = lir_r(c->ty);
        bc_call(c, helper, LIR_VOID, &type, &arg, 1);
}

static bool
bc_sync_after(u8 op)
{
        switch (op) {
        case INSTR_TRY_YIELD_FROM:
        case INSTR_TAIL_CALL:
        case INSTR_DEFINE_TAG:
        case INSTR_DEFINE_CLASS:
        case INSTR_INIT_STATIC_FIELD:
        case INSTR_BAD_CALL:
        case INSTR_BAD_ASSIGN:
        case INSTR_BAD_DISPATCH:
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
        case INSTR_ARRAY_COMPR:
        case INSTR_SET_COMPR:
        case INSTR_DICT_COMPR:
        case INSTR_LOOP_ITER:
        case INSTR_LOOP_CHECK:
        case INSTR_SPREAD_CHECK:
        case INSTR_GATHER_TUPLE:
        case INSTR_ARRAY:
        case INSTR_SET:
        case INSTR_DICT:
        case INSTR_DEFAULT_DICT:
                return false;
        case INSTR_TRY:
        case INSTR_CATCH:
        case INSTR_POP_TRY:
        case INSTR_SAVE_STACK_POS:
        case INSTR_DROP_STACK_POS:
                return true;
        case INSTR_RETHROW:
        case INSTR_FINALLY:
        case INSTR_END_TRY:
        case INSTR_RESTORE_STACK_POS:
        case INSTR_POP_STACK_POS:
        case INSTR_POP_STACK_POS_POP2:
        case INSTR_POP_STACK_POS_POP:
        case INSTR_CLEAR_EXTRA:
        case INSTR_THROW:
        case INSTR_RETURN:
        case INSTR_RETURN_PRESERVE_CTX:
        case INSTR_JUMP:
                return false;
        default:
                return true;
        }
}

static void
bc_try(BcLir *c, BcLirNode const *node)
{
        LirType ptr = LIR_TYPE_PTR;
        LirOpnd ty = lir_r(c->ty);
        BcLirNode const *t = &c->nodes[node->owner];
        switch (node->op) {
        case INSTR_TRY: {
                LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
                LirType types[] = { ptr, ptr, ptr, ptr, ptr };
                LirOpnd args[] = {
                        ty, lir_r(top), lir_i((uptr)(c->code + t->catch_to)),
                        lir_i(t->finally_to < 0 ? 0 : (uptr)(c->code + t->finally_to)),
                        lir_i(t->end_to < 0 ? 0 : (uptr)(c->code + t->end_to))
                };
                LirReg env = bc_call(c, bc_push_try, ptr, types, args, countof(args));
                LirOpnd buffer = lir_r(env);
                LirReg status = bc_call_flags(c, _setjmp, LIR_TYPE_I32, &ptr, &buffer, 1,
                                             LIR_RETURNS_TWICE);
                LirLabel normal = lir_label(c->L);
                bc_branch(c, LIR_EQ, lir_r(status), lir_i(0), normal);
                bc_restore_locals(c);
                bc_store(c, LIR_ST64, c->ty, offsetof(Ty, ip), lir_i((uptr)&JIT));
                bc_jump(c, c->nodes[t->catch_to].label);
                bc_bind(c, normal);
                break;
        }
        case INSTR_CATCH:
                bc_call(c, jit_rt_catch, LIR_VOID, &ptr, &ty, 1);
                break;
        case INSTR_POP_TRY:
                bc_call(c, jit_rt_pop_try, LIR_VOID, &ptr, &ty, 1);
                break;
        case INSTR_RETHROW:
                bc_call(c, jit_rt_rethrow_setup, LIR_VOID, &ptr, &ty, 1);
                bc_jump(c, c->nodes[t->finally_to].label);
                break;
        case INSTR_FINALLY: {
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { ty, lir_i((uptr)(c->code + node->next)) };
                bc_call(c, jit_rt_finally_enter, LIR_VOID, types, args, countof(args));
                bc_jump(c, c->nodes[t->finally_to].label);
                break;
        }
        case INSTR_END_TRY: {
                bc_stack_count(c);
                LirReg end = bc_call(c, jit_rt_end_try, ptr, &ptr, &ty, 1);
                LirLabel returned = lir_label(c->L);
                bc_branch(c, LIR_NE, lir_r(end), lir_i(0), returned);
                bc_call(c, vm_jit_end_try_rethrow, LIR_VOID, &ptr, &ty, 1);
                c->L->insts[c->last_call].flags |= LIR_NORETURN;
                bc_bind(c, returned);
                if (t->end_to >= 0) {
                        bc_branch(c, LIR_EQ, lir_r(end), lir_i((uptr)(c->code + t->end_to)),
                                  c->nodes[t->end_to].label);
                }
                for (i32 off = 0; off < c->size; ++off) {
                        BcLirNode const *f = &c->nodes[off];
                        if (f->next != 0 && f->op == INSTR_FINALLY && f->owner == node->owner && f->sp >= 0) {
                                bc_branch(c, LIR_EQ, lir_r(end), lir_i((uptr)(c->code + f->next)),
                                          c->nodes[f->next].label);
                        }
                }
                if (t->end_to >= 0) {
                        bc_jump(c, c->nodes[t->end_to].label);
                }
                break;
        }
        default:
                c->ok = false;
                break;
        }
}
