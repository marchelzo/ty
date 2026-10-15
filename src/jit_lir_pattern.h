static i32
bc_match_tag(Ty *ty, Value const *value, bool wrapped)
{
        if (wrapped) {
                return value->type & VALUE_TAGGED ? tags_first(ty, value->tags) : -1;
        }
        return value->type == VALUE_TAG ? value->tag : -1;
}

static bool
bc_pattern_test(Ty *ty, Value *top, char const *ip)
{
        ty->stack.count = top - ty->stack.items;
        Value *v = top - 1;
        i32 n = 0;
        i32 z = 0;
        if (StepInstruction(ip) - ip >= 9) {
                memcpy(&n, ip + 5, sizeof n);
        }
        switch ((u8)*ip) {
        case INSTR_ENSURE_LEN:
                return v->type == VALUE_ARRAY && v->array->count <= n;
        case INSTR_ENSURE_LEN_TUPLE:
                return v->type == VALUE_TUPLE && v->count <= n;
        case INSTR_ENSURE_DICT:
                return v->type == VALUE_DICT;
        case INSTR_TRY_TAG_POP:
                return jit_rt_try_tag_pop(ty, v, n);
        case INSTR_TRY_MEMBER:
                return vm_jit_try_match_member(ty, n);
        case INSTR_TRY_UNAPPLY:
                return !vm_jit_unapply(ty, true);
        case INSTR_TRY_ASSIGN_NON_NIL: {
                Value *target = vm_jit_pop_target(ty);
                if (v->type == VALUE_NIL) {
                        return false;
                }
                *target = *v;
                return true;
        }
        case INSTR_TRY_STEAL_TAG:
                return jit_rt_try_steal_tag(ty, v, vm_jit_pop_target(ty));
        case INSTR_ENSURE_EQUALS_VAR: {
                bool result = v_eq(v - 1, v);
                --ty->stack.count;
                return result;
        }
        case INSTR_ENSURE_CONTAINS: {
                bool result = dict_has_value(ty, v[-1].dict, v);
                --ty->stack.count;
                return result;
        }
        case INSTR_ENSURE_SAME_KEYS: {
                bool result = dict_same_keys(ty, v[-1].dict, v->dict);
                --ty->stack.count;
                return result;
        }
        case INSTR_TRY_RANGE:
        case INSTR_TRY_INCRANGE: {
                Value hi = v[0];
                Value lo = v[-1];
                Value subject = v[-2];
                bool result = value_compare(ty, &subject, &lo) >= 0
                           && value_compare(ty, &subject, &hi) <= ((u8)*ip == INSTR_TRY_INCRANGE ? 0 : -1);
                ty->stack.count -= 2;
                return result;
        }
        case INSTR_TRY_INDEX: {
                bool required = (u8)ip[9];
                if (!jit_rt_try_index(v, top, n, required)) {
                        return false;
                }
                ++ty->stack.count;
                return true;
        }
        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE:
                if (v->type != VALUE_TUPLE) {
                        return false;
                }
                if (n >= v->count) {
                        if ((u8)*ip == INSTR_INDEX_TUPLE) {
                                return false;
                        }
                        *top = NIL;
                } else {
                        *top = v->items[n];
                }
                ++ty->stack.count;
                return true;
        case INSTR_TRY_TUPLE_MEMBER: {
                bool required = (u8)ip[5];
                memcpy(&z, ip + 6, sizeof z);
                if (!jit_rt_try_tuple_member(v, top, required, z)) {
                        return false;
                }
                ++ty->stack.count;
                return true;
        }
        case INSTR_TRY_REGEX: {
                uptr regex;
                memcpy(&regex, ip + 5, sizeof regex);
                Value subject = *v;
                return jit_rt_try_regex(ty, &subject, (Regex *)regex, top);
        }
        case INSTR_ARRAY_REST:
                memcpy(&z, ip + 9, sizeof z);
                if (v->type != VALUE_ARRAY || v->array->count < n + z) {
                        return false;
                }
                return vm_jit_array_rest(ty, v, vm_jit_pop_target(ty), n, z);
        case INSTR_TUPLE_REST:
                return jit_rt_tuple_rest(ty, v, n);
        case INSTR_RECORD_REST: {
                if (v->type != VALUE_TUPLE) {
                        return false;
                }
                i32 const *ids = (i32 const *)ALIGNED_FOR(i32, ip + 5);
                return vm_jit_record_rest(ty, v, vm_jit_pop_target(ty), ids);
        }
        case INSTR_JNI:
        case INSTR_JII: {
                bool result = jit_rt_jii(ty, v, n < 0 ? -n : n);
                ty->stack.count -= n < 0;
                return (u8)*ip == INSTR_JNI ? result : !result;
        }
        default:
                return false;
        }
}

static void
bc_destructure(Ty *ty, Value *top, char *ip)
{
        ty->stack.count = top - ty->stack.items;
        Value value = top[-1];
        i32 n = 0;
        if (StepInstruction(ip) - ip >= 5) {
                memcpy(&n, ip + 1, sizeof n);
        }
        switch ((u8)*ip) {
        case INSTR_UNAPPLY:
                vm_jit_unapply(ty, false);
                break;
        case INSTR_PUSH_ARRAY_ELEM: {
                bool required = (u8)ip[5];
                if (!jit_rt_try_index(&value, top, n, required)) {
                        goto Failed;
                }
                ++ty->stack.count;
                break;
        }
        case INSTR_PUSH_TUPLE_ELEM:
                if (!jit_rt_index_tuple(&value, top, n)) {
                        goto Failed;
                }
                ++ty->stack.count;
                break;
        case INSTR_PUSH_TUPLE_MEMBER: {
                bool required = (u8)ip[1];
                memcpy(&n, ip + 2, sizeof n);
                if (value.ids == NULL || !jit_rt_try_tuple_member(&value, top, required, n)) {
                        goto Failed;
                }
                ++ty->stack.count;
                break;
        }
        case INSTR_PUSH_UNTAGGED:
                *top = value;
                (PopTag)(ty, top);
                ++ty->stack.count;
                break;
        case INSTR_UNTAG_OR_DIE:
                if (!tags_same(ty, tags_first(ty, value.tags), n)) {
                        goto Failed;
                }
                (PopTag)(ty, top - 1);
                break;
        case INSTR_STEAL_TAG:
                if (value.tags == 0) {
                        goto Failed;
                }
                if (!jit_rt_try_steal_tag(ty, top - 1, vm_jit_pop_target(ty))) {
                        goto Failed;
                }
                break;
        case INSTR_THROW_IF_NIL:
                if (value.type == VALUE_NIL) {
                        goto Failed;
                }
                break;
        case INSTR_BAD_MATCH:
                goto Failed;
        case INSTR_ASSIGN_REGEX_MATCHES:
                jit_rt_assign_regex_matches(ty, top - 1, n);
                --ty->stack.count;
                break;
        default:
                break;
        }
        return;
Failed:
        vm_jit_fail(ty, ty->stack.items + ty->stack.count, ip);
}

static bool
bc_pattern(BcLir *c, BcLirNode const *node, char const *ip)
{
        bool fused = false;
        if (
                !c->dynamic
             && c->nodes[node->target].label != LIR_NONE
             && bc_fast_pattern(c, node, ip, &fused)
        ) {
                return fused;
        }
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirReg last = bc_addr(c, c->ops, (c->sp - 1) * sizeof (Value));
        bc_stack_count(c);
        if (node->op == INSTR_MATCH_TAG || node->op == INSTR_MATCH_STRING) {
                LirReg key;
                if (node->op == INSTR_MATCH_TAG) {
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_BOOL };
                        LirOpnd args[] = { lir_r(c->ty), lir_r(last), lir_i(node->member) };
                        key = bc_call(c, bc_match_tag, LIR_TYPE_I32, types, args, countof(args));
                } else {
                        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_PTR };
                        LirOpnd args[] = { lir_r(last), lir_i(node->argc), lir_i((uptr)node->kw_ip) };
                        key = bc_call(c, jit_rt_match_string, LIR_TYPE_I32, types, args, countof(args));
                }
                for (i32 i = 0; i < node->argc; ++i) {
                        i32 id;
                        i32 delta;
                        char const *slot = node->kw_ip + i * 8;
                        memcpy(&id, slot, sizeof id);
                        memcpy(&delta, slot + 4, sizeof delta);
                        if (id != -1) {
                                i32 target = slot + 8 - c->code + delta;
                                bc_branch(c, LIR_EQ, lir_r(key), lir_i(node->op == INSTR_MATCH_TAG ? id : i),
                                          c->nodes[target].label);
                        }
                }
                bc_jump(c, c->nodes[node->target].label);
                return false;
        }
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i((uptr)ip) };
        LirReg pass = bc_call(c, bc_pattern_test, LIR_TYPE_BOOL, types, args, countof(args));
        bc_branch(c, LIR_EQ, lir_r(pass), lir_i(0), c->nodes[node->target].label);
        return false;
}
