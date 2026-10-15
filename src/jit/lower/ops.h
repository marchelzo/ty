static void *const BinaryHelpers[] = {
        [INSTR_CMP]         = (void *)jit_rt_cmp,
        [INSTR_CHECK_MATCH] = (void *)jit_rt_check_match,
        [INSTR_MOD]         = (void *)jit_rt_mod,
        [INSTR_BIT_AND]     = (void *)jit_rt_bit_and,
        [INSTR_BIT_OR]      = (void *)jit_rt_bit_or,
        [INSTR_BIT_XOR]     = (void *)jit_rt_bit_xor,
        [INSTR_SHL]         = (void *)jit_rt_shl,
        [INSTR_SHR]         = (void *)jit_rt_shr,
        [INSTR_RANGE]       = (void *)jit_rt_range,
        [INSTR_INCRANGE]    = (void *)jit_rt_incrange
};

static void
aggregate(Ty *ty, Value *top, i32 op)
{
        ty->stack.count = top - ty->stack.items;

        isize  base = vXx(ty->st->sps);
        i32    n    = ty->stack.count - base;
        Value *xs   = ty->stack.items + base;

        switch (op) {
        case INSTR_ARRAY:        jit_rt_array(ty, xs, xs, n);    break;
        case INSTR_SET:          DoSetLiteral(ty, n);            break;
        case INSTR_DICT:         DoDictLiteral(ty, n, NULL);     break;
        case INSTR_GATHER_TUPLE: jit_rt_tuple(ty, top, n, NULL); break;

        default: {
                Value dflt = ty->stack.items[--ty->stack.count];
                DoDictLiteral(ty, n - 1, &dflt);
                break;
        }
        }

        ty->stack.count = base + 1;
}

static void
comprehend(Ty *ty, Value *top, i32 op, i32 index, i32 count)
{
        ty->stack.count = top - ty->stack.items;

        if (op == INSTR_DICT_COMPR) {
                Dict *dict = vZ(ty->stack)[-2 * count - index - 1].dict;

                for (i32 i = 0; i < count; ++i) {
                        Value *end = vZ(ty->stack);
                        dict_put_value(ty, dict, end[-2 * i - 2], end[-2 * i - 1]);
                }

                ty->stack.count -= 2 * count;

                return;
        }

        count = ty->stack.count - vXx(ty->st->sps);

        if (op == INSTR_ARRAY_COMPR) {
                jit_rt_array_compr(ty, ty->stack.items + ty->stack.count, index, count);
        } else {
                DoSetCompr(ty, index, count);
        }
}

static void
target_member(Ty *ty, Value *top, i32 member, bool self)
{
        ty->stack.count = top - ty->stack.items;

        Value obj = self ? *vm_get_self(ty) : ty->stack.items[--ty->stack.count];

        vm_jit_target_member(ty, &obj, member);
}

static void
target_subscript(Ty *ty, Value *top)
{
        ty->stack.count = top - ty->stack.items;
        DoTargetSubscript(ty);
}

static void
count_member_set(BcLir *c)
{
#ifdef TY_PROFILER
        xinc(c, &jit_stats.member_set_fast);
#endif
}

static void
tick(BcLir *c, char const *ip)
{
#ifdef TY_PROFILER
        sync_sp(c);
        tycall(c, jit_profiler_tick, LT_VOID, pimm(ip));
#endif
}

static bool
member_assign(BcLir *c, BcLirNode const *node, char const *ip)
{
        bool self = (node->op == INSTR_TARGET_SELF_MEMBER);

        if (node->next >= c->size || (self && c->self_index < 0)) {
                return false;
        }

        BcLirNode const *next   = next_of(c, node);
        bool             assign = (next->op == INSTR_ASSIGN);

        if (!fusable_mutation(c, node, true) || next->sp != node->sp - !self) {
                return false;
        }

        i32      member = load_i32(ip + 1);
        LirLabel slow   = newlabel(c);
        LirLabel done   = newlabel(c);
        LirReg   obj    = self
                        ? addr(c, c->locals, vat(c->self_index))
                        : slot_of(c, c->sp - 1);
        Class   *class  = self
                        ? class_get(c->ctx, c->function->info[FUN_INFO_CLASS])
                        : hint_class(c, node - c->nodes);
        LirReg   slot   = any_field_slot(c, obj, class, member, true, slow);

        if (assign) {
                copy(c, slot, 0, c->ops, vat(next->sp - 1));
        } else {
                inline_mutation(c, next->op, slot, 0, next->sp - 1, slow, done);
        }

        count_member_set(c);
        jump(c, done);

        bind(c, slow);

        LirReg top = slot_of(c, c->sp);

        tycall(c, target_member, LT_VOID, preg(top), imm32(member), bimm(self));

        c->offset = next->next;

        if (assign) {
                LirReg value = slot_of(c, next->sp - 1);
                tycall(c, assign_value, LT_VOID, preg(value));
        } else {
                c->sp = next->sp;
                mutate(c, next->op);
        }

        bind(c, done);

        c->sp = next->sp;
        tick(c, c->code + node->next);

        return true;
}

static void
swap_top(BcLir *c)
{
        LirReg words[sizeof (Value) / 8];
        i32    a = vat(c->sp - 1);
        i32    b = vat(c->sp - 2);

        for (u32 i = 0; i < countof(words); ++i) {
                words[i] = ldq(c, c->ops, a + 8 * i);
        }

        copy(c, c->ops, a, c->ops, b);

        for (u32 i = 0; i < countof(words); ++i) {
                stq(c, c->ops, b + 8 * i, lir_r(words[i]));
        }
}

static void
push_self(BcLir *c)
{
        if (c->self_index >= 0) {
                local_load(c, c->self_index);
                return;
        }

        LirReg self = tycall(c, vm_get_self, LT_PTR);

        copy(c, c->ops, vat(c->sp++), self, 0);
}

static void
push_value(BcLir *c, u8 op, uptr value)
{
        if (op != INSTR_VALUE) {
                literal(c, (op == INSTR_REGEX) ? VALUE_REGEX : VALUE_TYPE, value);
                return;
        }

        LirReg p = vop(c, LIR_LI, LIR_PTR, lir_i(value));

        copy(c, c->ops, vat(c->sp++), p, 0);
}

static void
push_class_of(BcLir *c, LirReg last)
{
        LirReg class = ccall(c, ClassOf, LT_I32, preg(last));

        c->sp -= 1;
        literal(c, VALUE_CLASS, 0);

        i32 at = vat(c->sp - 1) + VOFF(class);
        stw(c, c->ops, at, lir_r(class));
}

static void
push_index(BcLir *c, i32 n)
{
        literal(c, VALUE_INDEX, 0);

        i32 at = vat(c->sp - 1) + VOFF(nt);
        stw(c, c->ops, at, lir_i(n));
}

static void
push_not(BcLir *c)
{
        LirReg truth = truthy(c);
        LirReg value = vop(c, LIR_SETCC, LIR_I64, lir_cc(LIR_EQ), lir_r(truth), lir_i(0));
        i32    at    = vat(c->sp - 1);

        for (u32 i = 0; i < sizeof (Value); i += 8) {
                stq(c, c->ops, at + i, lir_i(0));
        }

        stb(c, c->ops, at + VOFF(type), lir_i(VALUE_BOOLEAN));
        stq(c, c->ops, at + VOFF(boolean), lir_r(value));
}

static void
lower_misc(BcLir *c, BcLirNode const *node, char const *ip)
{
        LirReg top  = slot_of(c, c->sp);
        LirReg last = slot_of(c, c->sp - 1);
        u8     op   = node->op;
        i32    n    = 0;

        switch (op) {
        case INSTR_SELF:
                push_self(c);
                return;

        case INSTR_CLASS:
        case INSTR_TAG:
                n = load_i32(ip + 1);
                literal(c, (op == INSTR_CLASS) ? VALUE_CLASS : VALUE_TAG, n);
                return;

        case INSTR_REGEX:
        case INSTR_TYPE:
        case INSTR_VALUE:
                push_value(c, op, peek(u64, ip + 1));
                return;

        case INSTR_CLASS_OF:
                push_class_of(c, last);
                return;

        case INSTR_COUNT:
                tycall(c, jit_rt_count, LT_VOID, preg(last), preg(last));
                return;

        case INSTR_ARRAY_COMPR:
        case INSTR_SET_COMPR:
        case INSTR_DICT_COMPR: {
                BcArg index = imm32(load_i32(ip + 1));
                BcArg count = imm32((op == INSTR_DICT_COMPR) ? load_i32(ip + 5) : 0);
                tycall(c, comprehend, LT_VOID, preg(top), imm32(op), index, count);
                return;
        }

        case INSTR_PUSH_INDEX:
                push_index(c, load_i32(ip + 1));
                return;

        case INSTR_LOOP_ITER:
                tycall(c, jit_rt_loop_iter, LT_VOID, preg(top));
                return;

        case INSTR_LOOP_CHECK: {
                BcArg  member = imm32(node->member);
                LirReg r      = tycall(c, jit_rt_loop_check, LT_I32, member, preg(last));
                jnz(c, r, dest(c, node));
                return;
        }

        case INSTR_SPREAD_CHECK: {
                sync_sp(c);
                BcArg  member = bimm(node->member);
                LirReg r      = tycall(c, vm_jit_spread_check, LT_BOOL, member);
                jnz(c, r, dest(c, node));
                return;
        }

        case INSTR_ASSIGN_SUBSCRIPT:
                n = (u8)ip[1];
                if (n == 1) {
                        fast_assign_subscript(c);
                } else {
                        tycall(c, jit_rt_assign_subscript, LT_VOID, preg(top), imm32(n));
                        c->sp -= n + 1;
                }
                return;

        case INSTR_POP2:
                c->sp -= 2;
                return;

        case INSTR_SWAP:
                swap_top(c);
                return;

        case INSTR_DUP2_SWAP:
                copy(c, c->ops, vat(c->sp), c->ops, vat(c->sp - 1));
                copy(c, c->ops, vat(c->sp + 1), c->ops, vat(c->sp - 2));
                c->sp += 2;
                return;

        case INSTR_ARRAY:
        case INSTR_SET:
        case INSTR_DICT:
        case INSTR_GATHER_TUPLE:
        case INSTR_DEFAULT_DICT:
                tycall(c, aggregate, LT_VOID, preg(top), imm32(op));
                return;

        case INSTR_ARRAY0:
                tycall(c, jit_rt_array0, LT_VOID, preg(top));
                c->sp += 1;
                return;

        case INSTR_STRING:
                tycall(c, jit_rt_string, LT_VOID, preg(top), imm32(load_i32(ip + 1)));
                c->sp += 1;
                return;

        case INSTR_TUPLE: {
                BcArg ids = imm(LT_PTR, peek(u64, ip + 5));
                n = load_i32(ip + 1);
                tycall(c, jit_rt_tuple, LT_VOID, preg(top), imm32(n), ids);
                c->sp += 1 - n;
                return;
        }

        case INSTR_XTUPLE:
                n = load_i32(ip + 1);
                sync_sp(c);
                tycall(c, vm_jit_tuple_literal, LT_VOID, pimm(ip + 1));
                c->sp += 1 - n;
                return;

        case INSTR_CONCAT_STRINGS: {
                n = load_i32(ip + 1);
                LirReg base = slot_of(c, c->sp - n);
                tycall(c, jit_rt_concat_strings, LT_VOID, preg(base), preg(base), imm32(n));
                c->sp += 1 - n;
                return;
        }

        case INSTR_TARGET_MEMBER:
        case INSTR_TARGET_SELF_MEMBER: {
                bool self = (op == INSTR_TARGET_SELF_MEMBER);
                n = load_i32(ip + 1);
                tycall(c, target_member, LT_VOID, preg(top), imm32(n), bimm(self));
                c->sp -= !self;
                return;
        }

        case INSTR_TARGET_SUBSCRIPT:
                tycall(c, target_subscript, LT_VOID, preg(top));
                c->sp -= 2;
                return;

        case INSTR_MEMBER_ACCESS:
        case INSTR_SELF_MEMBER_ACCESS:
                lower_member(c, load_i32(ip + 1), op == INSTR_SELF_MEMBER_ACCESS);
                return;

        case INSTR_TRY_MEMBER_ACCESS:
        case INSTR_TAG_PUSH: {
                bool  tag = (op == INSTR_TAG_PUSH);
                void *fn  = tag ? (void *)jit_rt_tag_push : (void *)jit_rt_try_member;
                tycall(c, fn, LT_VOID, preg(tag ? last : top), imm32(load_i32(ip + 1)));
                return;
        }

        case INSTR_NOT:
                push_not(c);
                return;

        case INSTR_NEG:
                tycall(c, jit_rt_neg, LT_VOID, preg(last), preg(last));
                return;

        case INSTR_INC:
        case INSTR_DEC:
                fast_step(c, op == INSTR_INC);
                return;

        case INSTR_TO_STRING:
                tycall(c, jit_rt_to_string, LT_VOID, preg(last));
                return;

        case INSTR_SUBSCRIPT:
                fast_subscript(c);
                return;

        case INSTR_SAFE_SUBSCRIPT:
        case INSTR_GET_MEMBER:
        case INSTR_TRY_GET_MEMBER: {
                LirReg left = slot_of(c, c->sp - 2);
                void  *fn;

                switch (op) {
                case INSTR_SAFE_SUBSCRIPT: fn = (void *)jit_rt_safe_subscript; break;
                case INSTR_GET_MEMBER:     fn = (void *)jit_rt_get_member;     break;
                default:                   fn = (void *)jit_rt_try_get_member; break;
                }

                LirReg arg = (op == INSTR_SAFE_SUBSCRIPT) ? left : top;
                tycall(c, fn, LT_VOID, preg(arg));
                c->sp -= 1;
                return;
        }

        case INSTR_DIV:
                fast_div(c);
                return;

        default:
                break;
        }

        void *fn = (op < countof(BinaryHelpers)) ? BinaryHelpers[op] : NULL;

        if (fn == NULL) {
                c->ok = false;
                return;
        }

        LirReg left = slot_of(c, c->sp - 2);

        tycall(c, fn, LT_VOID, preg(left), preg(left), preg(last));

        c->sp -= 1;
}
