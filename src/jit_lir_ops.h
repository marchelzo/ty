static void
bc_aggregate(Ty *ty, Value *top, i32 op)
{
        ty->stack.count = top - ty->stack.items;
        isize base = vXx(ty->st->sps);
        i32 n = ty->stack.count - base;
        switch (op) {
        case INSTR_ARRAY:
                jit_rt_array(ty, ty->stack.items + base, ty->stack.items + base, n);
                break;
        case INSTR_SET:
                DoSetLiteral(ty, n);
                break;
        case INSTR_DICT:
                DoDictLiteral(ty, n, NULL);
                break;
        case INSTR_GATHER_TUPLE:
                jit_rt_tuple(ty, top, n, NULL);
                break;
        default: {
                Value value = ty->stack.items[--ty->stack.count];
                DoDictLiteral(ty, n - 1, &value);
                break;
        }
        }
        ty->stack.count = base + 1;
}

static void
bc_comprehend(Ty *ty, Value *top, i32 op, i32 index, i32 count)
{
        ty->stack.count = top - ty->stack.items;
        if (op == INSTR_DICT_COMPR) {
                Dict *dict = ty->stack.items[ty->stack.count - 2 * count - index - 1].dict;
                for (i32 i = 0; i < count; ++i) {
                        Value key = ty->stack.items[ty->stack.count - 2 * i - 2];
                        Value value = ty->stack.items[ty->stack.count - 2 * i - 1];
                        dict_put_value(ty, dict, key, value);
                }
                ty->stack.count -= 2 * count;
        } else {
                count = ty->stack.count - vXx(ty->st->sps);
                if (op == INSTR_ARRAY_COMPR) {
                        jit_rt_array_compr(ty, ty->stack.items + ty->stack.count, index, count);
                } else {
                        DoSetCompr(ty, index, count);
                }
        }
}

static void
bc_target_member(Ty *ty, Value *top, i32 member, bool self)
{
        ty->stack.count = top - ty->stack.items;
        Value obj = self ? *vm_get_self(ty) : ty->stack.items[--ty->stack.count];
        DoTargetMember(ty, obj, member);
}

static void
bc_target_subscript(Ty *ty, Value *top)
{
        ty->stack.count = top - ty->stack.items;
        DoTargetSubscript(ty);
}

static void
bc_swap_values(BcLir *c)
{
        LirReg values[4];
        i32 a = (c->sp - 1) * sizeof (Value);
        i32 b = a - sizeof (Value);
        for (u32 i = 0; i < countof(values); ++i) {
                values[i] = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, a + i * 8);
        }
        bc_value_copy(c, c->ops, a, c->ops, b);
        for (u32 i = 0; i < countof(values); ++i) {
                bc_store(c, LIR_ST64, c->ops, b + i * 8, lir_r(values[i]));
        }
}

static void
bc_more(BcLir *c, BcLirNode const *node, char const *ip)
{
        LirType ptr = LIR_TYPE_PTR;
        LirType integer = LIR_TYPE_I32;
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirReg last = bc_addr(c, c->ops, (c->sp - 1) * sizeof (Value));
        i32 n = 0;
        void *helper;
        switch (node->op) {
        case INSTR_SELF: {
                LirOpnd arg = lir_r(c->ty);
                LirReg self = bc_call(c, vm_get_self, ptr, &ptr, &arg, 1);
                bc_value_copy(c, c->ops, c->sp++ * sizeof (Value), self, 0);
                return;
        }
        case INSTR_CLASS:
        case INSTR_TAG:
                memcpy(&n, ip + 1, sizeof n);
                bc_literal(c, node->op == INSTR_CLASS ? VALUE_CLASS : VALUE_TAG, n);
                return;
        case INSTR_REGEX:
        case INSTR_TYPE:
        case INSTR_VALUE: {
                uptr value;
                memcpy(&value, ip + 1, sizeof value);
                if (node->op == INSTR_VALUE) {
                        LirOpnd arg = lir_i(value);
                        LirReg base = bc_value(c, LIR_LI, LIR_PTR, &arg, 1);
                        bc_value_copy(c, c->ops, c->sp++ * sizeof (Value), base, 0);
                } else {
                        bc_literal(c, node->op == INSTR_REGEX ? VALUE_REGEX : VALUE_TYPE, value);
                }
                return;
        }
        case INSTR_CLASS_OF: {
                LirOpnd arg = lir_r(last);
                LirReg class = bc_call(c, ClassOf, integer, &ptr, &arg, 1);
                --c->sp;
                bc_literal(c, VALUE_CLASS, 0);
                bc_store(c, LIR_ST32, c->ops,
                         (c->sp - 1) * sizeof (Value) + offsetof(Value, class), lir_r(class));
                return;
        }
        case INSTR_COUNT: {
                LirType types[] = { ptr, ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(last), lir_r(last) };
                bc_call(c, jit_rt_count, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_ARRAY_COMPR:
        case INSTR_SET_COMPR:
        case INSTR_DICT_COMPR: {
                i32 count = 0;
                memcpy(&n, ip + 1, sizeof n);
                if (node->op == INSTR_DICT_COMPR) {
                        memcpy(&count, ip + 5, sizeof count);
                }
                LirType types[] = { ptr, ptr, integer, integer, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(node->op), lir_i(n), lir_i(count) };
                bc_call(c, bc_comprehend, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_PUSH_INDEX:
                memcpy(&n, ip + 1, sizeof n);
                bc_literal(c, VALUE_INDEX, 0);
                bc_store(c, LIR_ST32, c->ops, (c->sp - 1) * sizeof (Value) + offsetof(Value, nt), lir_i(n));
                return;
        case INSTR_LOOP_ITER: {
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top) };
                bc_call(c, jit_rt_loop_iter, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_LOOP_CHECK: {
                LirType types[] = { ptr, integer, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->member), lir_r(last) };
                LirReg result = bc_call(c, jit_rt_loop_check, integer, types, args, countof(args));
                bc_branch(c, LIR_NE, lir_r(result), lir_i(0), c->nodes[node->target].label);
                return;
        }
        case INSTR_SPREAD_CHECK: {
                LirType types[] = { ptr, LIR_TYPE_BOOL };
                LirOpnd args[] = { lir_r(c->ty), lir_i(node->member) };
                bc_stack_count(c);
                LirReg result = bc_call(c, vm_jit_spread_check, LIR_TYPE_BOOL,
                                       types, args, countof(args));
                bc_branch(c, LIR_NE, lir_r(result), lir_i(0), c->nodes[node->target].label);
                return;
        }
        case INSTR_ASSIGN_SUBSCRIPT: {
                n = (u8)ip[1];
                LirType types[] = { ptr, ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(n) };
                bc_call(c, jit_rt_assign_subscript, LIR_VOID, types, args, countof(args));
                c->sp -= n + 1;
                return;
        }
        case INSTR_POP2:
                c->sp -= 2;
                return;
        case INSTR_SWAP:
                bc_swap_values(c);
                return;
        case INSTR_DUP2_SWAP:
                bc_value_copy(c, c->ops, c->sp * sizeof (Value), c->ops, (c->sp - 1) * sizeof (Value));
                bc_value_copy(c, c->ops, (c->sp + 1) * sizeof (Value), c->ops, (c->sp - 2) * sizeof (Value));
                c->sp += 2;
                return;
        case INSTR_ARRAY:
        case INSTR_SET:
        case INSTR_DICT:
        case INSTR_GATHER_TUPLE:
        case INSTR_DEFAULT_DICT: {
                LirType types[] = { ptr, ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(node->op) };
                bc_call(c, bc_aggregate, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_ARRAY0: {
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top) };
                bc_call(c, jit_rt_array0, LIR_VOID, types, args, countof(args));
                ++c->sp;
                return;
        }
        case INSTR_STRING: {
                memcpy(&n, ip + 1, sizeof n);
                LirType types[] = { ptr, ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(n) };
                bc_call(c, jit_rt_string, LIR_VOID, types, args, countof(args));
                ++c->sp;
                return;
        }
        case INSTR_TUPLE: {
                uptr ids;
                memcpy(&n, ip + 1, sizeof n);
                memcpy(&ids, ip + 1 + sizeof n, sizeof ids);
                LirType types[] = { ptr, ptr, integer, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(n), lir_i(ids) };
                bc_call(c, jit_rt_tuple, LIR_VOID, types, args, countof(args));
                c->sp += 1 - n;
                return;
        }
        case INSTR_XTUPLE: {
                memcpy(&n, ip + 1, sizeof n);
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_i((uptr)(ip + 1)) };
                bc_stack_count(c);
                bc_call(c, vm_jit_tuple_literal, LIR_VOID, types, args, countof(args));
                c->sp += 1 - n;
                return;
        }
        case INSTR_CONCAT_STRINGS: {
                memcpy(&n, ip + 1, sizeof n);
                LirReg base = bc_addr(c, c->ops, (c->sp - n) * sizeof (Value));
                LirType types[] = { ptr, ptr, ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(base), lir_r(base), lir_i(n) };
                bc_call(c, jit_rt_concat_strings, LIR_VOID, types, args, countof(args));
                c->sp += 1 - n;
                return;
        }
        case INSTR_TARGET_MEMBER:
        case INSTR_TARGET_SELF_MEMBER: {
                memcpy(&n, ip + 1, sizeof n);
                bool self = node->op == INSTR_TARGET_SELF_MEMBER;
                LirType types[] = { ptr, ptr, integer, LIR_TYPE_BOOL };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(n), lir_i(self) };
                bc_call(c, bc_target_member, LIR_VOID, types, args, countof(args));
                c->sp -= !self;
                return;
        }
        case INSTR_TARGET_SUBSCRIPT: {
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(top) };
                bc_call(c, bc_target_subscript, LIR_VOID, types, args, countof(args));
                c->sp -= 2;
                return;
        }
        case INSTR_MEMBER_ACCESS:
        case INSTR_SELF_MEMBER_ACCESS: {
                memcpy(&n, ip + 1, sizeof n);
                bool self = node->op == INSTR_SELF_MEMBER_ACCESS;
                LirReg out = self ? top : last;
                LirType types[] = { ptr, ptr, ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(out), self ? lir_i(0) : lir_r(out), lir_i(n) };
                bc_call(c, jit_rt_member, LIR_VOID, types, args, countof(args));
                c->sp += self;
                return;
        }
        case INSTR_TRY_MEMBER_ACCESS:
        case INSTR_TAG_PUSH: {
                memcpy(&n, ip + 1, sizeof n);
                LirType types[] = { ptr, ptr, integer };
                LirOpnd args[] = { lir_r(c->ty), lir_r(node->op == INSTR_TAG_PUSH ? last : top), lir_i(n) };
                helper = node->op == INSTR_TAG_PUSH ? jit_rt_tag_push : jit_rt_try_member;
                bc_call(c, helper, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_NEG:
        case INSTR_NOT: {
                LirType types[] = { ptr, ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(last), lir_r(last) };
                helper = node->op == INSTR_NEG ? jit_rt_neg : jit_rt_not;
                bc_call(c, helper, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_INC:
        case INSTR_DEC:
        case INSTR_TO_STRING: {
                LirType types[] = { ptr, ptr };
                LirOpnd args[] = { lir_r(c->ty), lir_r(last) };
                switch (node->op) {
                case INSTR_INC: helper = jit_rt_inc; break;
                case INSTR_DEC: helper = jit_rt_dec; break;
                default: helper = jit_rt_to_string; break;
                }
                bc_call(c, helper, LIR_VOID, types, args, countof(args));
                return;
        }
        case INSTR_SUBSCRIPT:
        case INSTR_SAFE_SUBSCRIPT:
        case INSTR_GET_MEMBER:
        case INSTR_TRY_GET_MEMBER: {
                LirType types[] = { ptr, ptr };
                LirReg left = bc_addr(c, c->ops, (c->sp - 2) * sizeof (Value));
                LirOpnd args[] = { lir_r(c->ty), lir_r(left) };
                switch (node->op) {
                case INSTR_SUBSCRIPT: helper = jit_rt_subscript; break;
                case INSTR_SAFE_SUBSCRIPT: helper = jit_rt_safe_subscript; break;
                case INSTR_GET_MEMBER: helper = jit_rt_get_member; args[1] = lir_r(top); break;
                default: helper = jit_rt_try_get_member; args[1] = lir_r(top); break;
                }
                bc_call(c, helper, LIR_VOID, types, args, countof(args));
                --c->sp;
                return;
        }
        default:
                break;
        }
        switch (node->op) {
        case INSTR_CMP:       helper = jit_rt_cmp; break;
        case INSTR_CHECK_MATCH: helper = jit_rt_check_match; break;
        case INSTR_DIV:       helper = jit_rt_div; break;
        case INSTR_MOD:       helper = jit_rt_mod; break;
        case INSTR_BIT_AND:   helper = jit_rt_bit_and; break;
        case INSTR_BIT_OR:    helper = jit_rt_bit_or; break;
        case INSTR_BIT_XOR:   helper = jit_rt_bit_xor; break;
        case INSTR_SHL:       helper = jit_rt_shl; break;
        case INSTR_SHR:       helper = jit_rt_shr; break;
        case INSTR_RANGE:     helper = jit_rt_range; break;
        case INSTR_INCRANGE:  helper = jit_rt_incrange; break;
        default:
                c->ok = false;
                return;
        }
        LirReg left = bc_addr(c, c->ops, (c->sp - 2) * sizeof (Value));
        LirType types[] = { ptr, ptr, ptr, ptr };
        LirOpnd args[] = { lir_r(c->ty), lir_r(left), lir_r(left), lir_r(last) };
        bc_call(c, helper, LIR_VOID, types, args, countof(args));
        --c->sp;
}
