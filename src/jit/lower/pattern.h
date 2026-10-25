static i32
match_tag(Ty *ty, Value const *value, bool wrapped)
{
        if (wrapped) {
                return (value->type & VALUE_TAGGED) ? tags_first(ty, value->tags) : -1;
        }

        return (value->type == VALUE_TAG) ? value->tag : -1;
}

inline static bool
popped(Ty *ty, i32 n, bool result)
{
        ty->stack.count -= n;
        return result;
}

inline static bool
pushed(Ty *ty, bool ok)
{
        ty->stack.count += ok;
        return ok;
}

static bool
tuple_at(Value const *v, Value *top, i32 n, bool required)
{
        if (v->type != VALUE_TUPLE) {
                return false;
        }

        if (n < v->count) {
                *top = v->items[n];
        } else if (required) {
                return false;
        } else {
                *top = NIL;
        }

        return true;
}

static bool
pattern_test(Ty *ty, Value *top, char const *ip)
{
        u8     op = *ip;
        Value *v  = top - 1;
        i32    n  = (StepInstruction(ip) - ip >= 9) ? load_i32(ip + 5) : 0;

        ty->stack.count = top - ty->stack.items;

        switch (op) {
        case INSTR_ENSURE_LEN:
                return (v->type == VALUE_ARRAY) && (v->array->count <= n);

        case INSTR_ENSURE_LEN_TUPLE:
                return (v->type == VALUE_TUPLE) && (v->count <= n);

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

        case INSTR_ENSURE_EQUALS_VAR:
                return popped(ty, 1, v_eq(v - 1, v));

        case INSTR_ENSURE_CONTAINS:
                return popped(ty, 1, dict_has_value(ty, v[-1].dict, v));

        case INSTR_ENSURE_SAME_KEYS:
                return popped(ty, 1, dict_same_keys(ty, v[-1].dict, v->dict));

        case INSTR_TRY_RANGE:
        case INSTR_TRY_INCRANGE: {
                Value hi      = v[0];
                Value lo      = v[-1];
                Value subject = v[-2];
                i32   limit   = (op == INSTR_TRY_INCRANGE) ? 0 : -1;
                bool  within  = (value_compare(ty, &subject, &lo) >= 0)
                             && (value_compare(ty, &subject, &hi) <= limit);

                return popped(ty, 2, within);
        }

        case INSTR_TRY_INDEX:
                return pushed(ty, jit_rt_try_index(v, top, n, (u8)ip[9]));

        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE:
                return pushed(ty, tuple_at(v, top, n, op == INSTR_INDEX_TUPLE));

        case INSTR_TRY_TUPLE_MEMBER: {
                bool required = (u8)ip[5];
                i32  member   = load_i32(ip + 6);
                return pushed(ty, jit_rt_try_tuple_member(v, top, required, member));
        }

        case INSTR_TRY_REGEX: {
                Value subject = *v;
                return jit_rt_try_regex(ty, &subject, (Regex *)peek(u64, ip + 5), top);
        }

        case INSTR_ARRAY_REST: {
                i32 after = load_i32(ip + 9);

                if (v->type != VALUE_ARRAY || v->array->count < n + after) {
                        return false;
                }

                return vm_jit_array_rest(ty, v, vm_jit_pop_target(ty), n, after);
        }

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
                bool found = popped(ty, n < 0, jit_rt_jii(ty, v, (n < 0) ? -n : n));
                return (op == INSTR_JNI) ? found : !found;
        }

        default:
                return false;
        }
}

static void
destructure(Ty *ty, Value *top, char *ip)
{
        Value value = top[-1];
        i32   n     = (StepInstruction(ip) - ip >= 5) ? load_i32(ip + 1) : 0;

        ty->stack.count = top - ty->stack.items;

        switch ((u8)*ip) {
        case INSTR_UNAPPLY:
                vm_jit_unapply(ty, false);
                break;

        case INSTR_PUSH_ARRAY_ELEM:
                if (!pushed(ty, jit_rt_try_index(&value, top, n, (u8)ip[5]))) {
                        goto Failed;
                }
                break;

        case INSTR_PUSH_TUPLE_ELEM:
                if (!pushed(ty, jit_rt_index_tuple(&value, top, n))) {
                        goto Failed;
                }
                break;

        case INSTR_PUSH_TUPLE_MEMBER: {
                bool required = (u8)ip[1];
                i32  member   = load_i32(ip + 2);

                if (value.ids == NULL) {
                        goto Failed;
                }

                if (!pushed(ty, jit_rt_try_tuple_member(&value, top, required, member))) {
                        goto Failed;
                }
                break;
        }

        case INSTR_PUSH_UNTAGGED:
                *top = value;
                (PopTag)(ty, top);
                ty->stack.count += 1;
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
                ty->stack.count -= 1;
                break;

        default:
                break;
        }

        return;

Failed:
        vm_jit_fail(ty, ty->stack.items + ty->stack.count, ip);
}

static LirReg
match_key(BcLir *c, LirReg value, bool wrapped)
{
        LirReg   key  = lir_reg(c->L, LIR_I64);
        LirLabel none = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   type = ldx(c, LIR_LD_U8, LIR_I64, value, VOFF(type));

        if (wrapped) {
                jz(c, binop(c, LIR_AND, LIR_I64, lir_r(type), lir_i(VALUE_TAGGED)), none);
                mov(c, key, ldw(c, tag_list(c, ldx(c, LIR_LD_U16, LIR_I64, value, VOFF(tags))), offsetof(struct tags, tag)));
        } else {
                unless(c, type, VALUE_TAG, none);
                mov(c, key, ldx(c, LIR_LD_U16, LIR_I64, value, VOFF(tag)));
        }

        jump(c, done);

        bind(c, none);
        vset(c, LIR_LI, key, lir_i(-1));

        bind(c, done);

        return key;
}

static void
switch_match(BcLir *c, BcLirNode const *node, LirReg last)
{
        bool   tag = (node->op == INSTR_MATCH_TAG);
        LirReg key;

        if (tag) {
                key = match_key(c, last, node->member);
        } else {
                key = ccall(
                        c,
                        jit_rt_match_string,
                        LT_I32,
                        preg(last),
                        imm32(node->argc),
                        pimm(node->kw_ip)
                );
        }

        for (i32 i = 0; i < node->argc; ++i) {
                i32 id;
                i32 to = arm(c, node, i, &id);

                if (id != -1) {
                        LirOpnd want = lir_i(tag ? id : i);
                        jcc(c, LIR_EQ, lir_r(key), want, exit_edge(c, to));
                }
        }

        jump(c, dest(c, node));
}

static bool
lower_pattern(BcLir *c, BcLirNode const *node, char const *ip)
{
        bool fused = false;

        if (
                !c->dynamic
             && (dest(c, node) != LIR_NONE)
             && fast_pattern(c, node, ip, &fused)
        ) {
                return fused;
        }

        LirReg top  = slot_of(c, c->sp);
        LirReg last = slot_of(c, c->sp - 1);

        sync_sp(c);

        if (matches(node)) {
                switch_match(c, node, last);
                return false;
        }

        LirReg pass = tycall(c, pattern_test, LT_BOOL, preg(top), pimm(ip));

        jz(c, pass, dest(c, node));

        return false;
}

