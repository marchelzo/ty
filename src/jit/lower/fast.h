static void
target_subscript(Ty *ty, Value *top);

static LirReg
array_slot(BcLir *c, i32 container, i32 index, LirLabel slow)
{
        expect(c, c->ops, vat(container), VALUE_ARRAY, slow);
        expect(c, c->ops, vat(index), VALUE_INTEGER, slow);

        LirReg i     = ldq(c, c->ops, vat(index) + VOFF(z));
        LirReg array = ldp(c, c->ops, vat(container) + VOFF(array));

        jcc(c, LIR_UGE, lir_r(i), lir_r(ldq(c, array, offsetof(Array, count))), slow);

        return elem(c, ldp(c, array, offsetof(Array, items)), i, 0);
}

static void
fast_subscript(BcLir *c)
{
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   slot = array_slot(c, c->sp - 2, c->sp - 1, slow);

        copy(c, c->ops, vat(c->sp - 2), slot, 0);
        jump(c, done);

        bind(c, slow);
        tycall(c, jit_rt_subscript, LT_VOID, preg(slot_of(c, c->sp - 2)));

        bind(c, done);
        c->sp -= 1;
}

static void
fast_assign_subscript(BcLir *c)
{
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   slot = array_slot(c, c->sp - 2, c->sp - 1, slow);

        copy(c, slot, 0, c->ops, vat(c->sp - 3));
        jump(c, done);

        bind(c, slow);
        tycall(
                c,
                jit_rt_assign_subscript,
                LT_VOID,
                preg(slot_of(c, c->sp)),
                imm32(1)
        );

        bind(c, done);
        c->sp -= 2;
}

static void
fast_step(BcLir *c, bool up)
{
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        i32      at   = vat(c->sp - 1);

        expect(c, c->ops, at, VALUE_INTEGER, slow);
        bump(c, c->ops, at + VOFF(z), up ? 1 : -1);
        jump(c, done);

        bind(c, slow);
        LirReg last = slot_of(c, c->sp - 1);
        tycall(c, up ? jit_rt_inc : jit_rt_dec, LT_VOID, preg(last));

        bind(c, done);
}

inline static bool
plain(BcLirNode const *node)
{
        return (node->label == LIR_NONE) && (node->sp >= 0);
}

static BcLirNode const *
successor(BcLir const *c, BcLirNode const *node)
{
        if (node->next >= c->size || !plain(next_of(c, node))) {
                return NULL;
        }

        return next_of(c, node);
}

static bool
fusable_mutation(BcLir *c, BcLirNode const *node, bool assign)
{
        BcLirNode const *next = successor(c, node);

        if (next == NULL) {
                return false;
        }

        switch (next->op) {
        case INSTR_ASSIGN:  return assign;
        case INSTR_MUT_ADD:
        case INSTR_MUT_SUB:
        case INSTR_MUT_MUL:
        case INSTR_MUT_DIV: return true;
        default:            return false;
        }
}

static void
mutate_real(BcLir *c, LirOp op, LirReg base, i32 at, i32 rhs, LirLabel done)
{
        LirReg a = ldf(c, base, at + VOFF(real));
        LirReg b = ldf(c, c->ops, rhs + VOFF(real));
        LirReg r = binop(c, op, LIR_F64, lir_r(a), lir_r(b));

        stf(c, base, at + VOFF(real), lir_r(r));
        stf(c, c->ops, rhs + VOFF(real), lir_r(r));
        jump(c, done);
}

static void
inline_mutation(
        BcLir *c,
        u8 op,
        LirReg base,
        i32 at,
        i32 value,
        LirLabel slow,
        LirLabel done
)
{
        i32    rhs = vat(value);
        LirReg lt  = tagat(c, base, at);
        LirReg rt  = tag_of(c, value);

        if (op == INSTR_MUT_DIV) {
                unless(c, lt, VALUE_REAL, slow);
                unless(c, rt, VALUE_REAL, slow);
                nonzero_real(c, c->ops, rhs, slow);
                mutate_real(c, LIR_FDIV, base, at, rhs, done);
                return;
        }

        LirOp iop;
        LirOp fop;

        switch (op) {
        case INSTR_MUT_ADD: iop = LIR_ADD; fop = LIR_FADD; break;
        case INSTR_MUT_SUB: iop = LIR_SUB; fop = LIR_FSUB; break;
        default:            iop = LIR_MUL; fop = LIR_FMUL; break;
        }

        LirLabel real = newlabel(c);

        unless(c, lt, VALUE_INTEGER, real);
        unless(c, rt, VALUE_INTEGER, real);

        LirReg a = ldq(c, base, at + VOFF(z));
        LirReg b = ldq(c, c->ops, rhs + VOFF(z));
        LirReg r = binop(c, iop, LIR_I64, lir_r(a), lir_r(b));

        stq(c, base, at + VOFF(z), lir_r(r));
        stq(c, c->ops, rhs + VOFF(z), lir_r(r));
        jump(c, done);

        bind(c, real);
        unless(c, lt, VALUE_REAL, slow);
        unless(c, rt, VALUE_REAL, slow);
        mutate_real(c, fop, base, at, rhs, done);
}

static bool
fuse_non_nil(BcLir *c, BcLirNode const *next, i32 slot)
{
        LirLabel target = c->nodes[next->target].label;

        if (next->op != INSTR_TRY_ASSIGN_NON_NIL || target == LIR_NONE) {
                return false;
        }

        i32 top = vat(c->sp - 1);

        c->offset = next->next;
        jcc(c, LIR_EQ, lir_r(tag_of(c, c->sp - 1)), lir_i(VALUE_NIL), target);
        copy(c, c->locals, vat(slot), c->ops, top);

        return true;
}

static bool
fuse_step(BcLir *c, BcLirNode const *node, BcLirNode const *next, char const *ip, i32 slot)
{
        bool inc  = (next->op == INSTR_PRE_INC) || (next->op == INSTR_POST_INC);
        bool dec  = (next->op == INSTR_PRE_DEC) || (next->op == INSTR_POST_DEC);
        bool post = (next->op == INSTR_POST_INC) || (next->op == INSTR_POST_DEC);

        if (c->compact || (!inc && !dec)) {
                return false;
        }

        i32      local = vat(slot);
        i32      top   = vat(c->sp);
        LirLabel slow  = newlabel(c);
        LirLabel done  = newlabel(c);

        expect(c, c->locals, local, VALUE_INTEGER, slow);

        LirReg old = ldq(c, c->locals, local + VOFF(z));
        LirReg now = plus(c, old, inc ? 1 : -1);

        stq(c, c->locals, local + VOFF(z), lir_r(now));
        stq(c, c->ops, top, lir_i(VALUE_INTEGER));
        stq(c, c->ops, top + VOFF(z), lir_r(post ? old : now));
        jump(c, done);

        bind(c, slow);
        lower_target(c, ip, INSTR_TARGET_LOCAL);
        state(c, next, c->code + node->next);

        bind(c, done);
        c->offset = next->next;

        return true;
}

static bool
fuse_mutation(BcLir *c, BcLirNode const *node, char const *ip, i32 slot)
{
        if (!fusable_mutation(c, node, true)) {
                return false;
        }

        BcLirNode const *next  = next_of(c, node);
        i32              local = vat(slot);

        c->offset = next->next;

        if (next->op == INSTR_ASSIGN) {
                copy(c, c->locals, local, c->ops, vat(c->sp - 1));
                return true;
        }

        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);

        inline_mutation(c, next->op, c->locals, local, c->sp - 1, slow, done);

        bind(c, slow);
        lower_target(c, ip, INSTR_TARGET_LOCAL);
        mutate(c, next->op);

        bind(c, done);

        return true;
}

static bool
fast_target_local(BcLir *c, BcLirNode const *node, char const *ip)
{
        BcLirNode const *next = c->dynamic ? NULL : successor(c, node);
        i32              slot = load_i32(ip + 1);

        if (
                (next != NULL)
             && (fuse_non_nil(c, next, slot) || fuse_step(c, node, next, ip, slot))
        ) {
                return true;
        }

        return fuse_mutation(c, node, ip, slot);
}

static bool
fast_target_subscript(BcLir *c, BcLirNode const *node)
{
        if (!fusable_mutation(c, node, false)) {
                return false;
        }

        BcLirNode const *next = next_of(c, node);
        LirLabel         slow = newlabel(c);
        LirLabel         done = newlabel(c);

        c->offset = next->next;

        LirReg slot = array_slot(c, c->sp - 2, c->sp - 1, slow);

        inline_mutation(c, next->op, slot, 0, c->sp - 3, slow, done);

        bind(c, slow);
        tycall(c, target_subscript, LT_VOID, preg(slot_of(c, c->sp)));
        c->sp -= 2;
        mutate(c, next->op);

        bind(c, done);

        return true;
}

static void
loop_slow(BcLir *c, BcLirNode const *check, i32 sp, LirLabel exit)
{
        tycall(c, jit_rt_loop_iter, LT_VOID, preg(slot_of(c, sp)));

        LirReg more = tycall(
                c,
                jit_rt_loop_check,
                LT_I32,
                imm32(check->member),
                preg(slot_of(c, sp + 1))
        );

        jnz(c, more, exit);
}

static bool
fast_loop(BcLir *c, BcLirNode const *node)
{
        if (c->dynamic || node->next >= c->size) {
                return false;
        }

        BcLirNode const *check = next_of(c, node);

        if (
                (check->op != INSTR_LOOP_CHECK)
             || (check->label != LIR_NONE)
             || (check->member < 1 || check->member > 2)
             || (c->nodes[check->target].label == LIR_NONE)
        ) {
                return false;
        }

        LirLabel exit = c->nodes[check->target].label;
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        i32      sp   = c->sp;

        c->offset = check->next;

        expect(c, c->ops, vat(sp - 1), VALUE_ARRAY, slow);

        LirReg array = ldp(c, c->ops, vat(sp - 1) + VOFF(array));
        LirReg i     = ldq(c, c->ops, vat(sp - 2) + VOFF(z));
        LirReg count = ldq(c, array, offsetof(Array, count));

        jcc(c, LIR_GE, lir_r(i), lir_r(count), exit);
        stq(c, c->ops, vat(sp - 2) + VOFF(z), lir_r(plus(c, i, 1)));
        put_scalar(c, sp, VALUE_SENTINEL, lir_i(0));

        if (check->member == 2) {
                put_scalar(c, sp + 1, VALUE_INTEGER, lir_r(i));
        }

        LirReg item = elem(c, ldp(c, array, offsetof(Array, items)), i, 0);

        copy(c, c->ops, vat(sp + check->member), item, 0);
        jump(c, done);

        bind(c, slow);
        loop_slow(c, check, sp, exit);

        bind(c, done);

        return true;
}

static void
fast_div(BcLir *c)
{
        i32      left  = vat(c->sp - 2);
        i32      right = vat(c->sp - 1);
        LirLabel real  = newlabel(c);
        LirLabel slow  = newlabel(c);
        LirLabel done  = newlabel(c);
        LirReg   at    = tag_of(c, c->sp - 2);
        LirReg   bt    = tag_of(c, c->sp - 1);

        unless(c, at, VALUE_INTEGER, real);
        unless(c, bt, VALUE_INTEGER, real);

        LirReg b = ldq(c, c->ops, right + VOFF(z));

        no_overflow_div(c, b, slow);

        LirReg a = ldq(c, c->ops, left + VOFF(z));

        stq(c, c->ops, left + VOFF(z), lir_r(binr(c, LIR_SDIV, LIR_I64, a, b)));
        jump(c, done);

        bind(c, real);
        unless(c, at, VALUE_REAL, slow);
        unless(c, bt, VALUE_REAL, slow);
        nonzero_real(c, c->ops, right, slow);

        LirReg fa = ldf(c, c->ops, left + VOFF(real));
        LirReg fb = ldf(c, c->ops, right + VOFF(real));

        stf(c, c->ops, left + VOFF(real), lir_r(binr(c, LIR_FDIV, LIR_F64, fa, fb)));
        jump(c, done);

        bind(c, slow);

        LirReg out = slot_of(c, c->sp - 2);
        LirReg rhs = slot_of(c, c->sp - 1);

        tycall(c, jit_rt_div, LT_VOID, preg(out), preg(out), preg(rhs));

        bind(c, done);
        c->sp -= 1;
}

static void
nil_unless_found(BcLir *c, bool required, LirLabel missing, LirLabel done)
{
        if (!required) {
                jump(c, done);
                bind(c, missing);
                put_scalar(c, c->sp, VALUE_NIL, lir_i(0));
        }

        bind(c, done);
}

static bool
fuse_tuple_local(BcLir *c, BcLirNode const *node, LirReg items, i32 n)
{
        BcLirNode const *next = successor(c, node);

        if (
                (node->op != INSTR_INDEX_TUPLE)
             || (next == NULL)
             || (next->op != INSTR_ASSIGN_LOCAL)
        ) {
                return false;
        }

        i32 slot = load_i32(c->code + node->next + 1);

        if (slot < 0 || slot >= c->bound || loop_reg(c, slot) != LIR_NONE) {
                return false;
        }

        copy(c, c->locals, vat(slot), items, vat(n));

        c->offset    = next->next;
        c->tuple_off = next->next;
        c->tuple_sp  = c->sp - 1;
        c->tuple_min = max(c->tuple_min, n + 1);

        return true;
}

static bool
index_tuple(BcLir *c, BcLirNode const *node, i32 n, LirLabel fail, bool *fused)
{
        if (n < 0) {
                return false;
        }

        i32      at       = vat(c->sp - 1);
        bool     required = (node->op == INSTR_INDEX_TUPLE);
        LirLabel missing  = required ? fail : newlabel(c);
        LirLabel done     = newlabel(c);
        bool     known    = (c->tuple_off == node - c->nodes)
                         && (c->tuple_sp == c->sp - 1)
                         && (node->label == LIR_NONE);

        if (!known) {
                expect(c, c->ops, at, VALUE_TUPLE, fail);
                c->tuple_min = 0;
        }

        if (!known || n >= c->tuple_min) {
                LirReg count = ldw(c, c->ops, at + VOFF(count));
                jcc(c, LIR_LE, lir_r(count), lir_i(n), missing);
        }

        LirReg items = ldp(c, c->ops, at + VOFF(items));

        c->tuple_off = -1;

        if (fuse_tuple_local(c, node, items, n)) {
                *fused = true;
                bind(c, done);
                return true;
        }

        copy(c, c->ops, at + sizeof (Value), items, vat(n));
        nil_unless_found(c, required, missing, done);

        return true;
}

static bool
fast_pattern(BcLir *c, BcLirNode const *node, char const *ip, bool *fused)
{
        i32      n    = (StepInstruction(ip) - ip >= 9) ? load_i32(ip + 5) : 0;
        LirLabel fail = dest(c, node);
        i32      at   = vat(c->sp - 1);

        switch (node->op) {
        case INSTR_ENSURE_LEN: {
                expect(c, c->ops, at, VALUE_ARRAY, fail);
                LirReg array = ldp(c, c->ops, at + VOFF(array));
                LirReg count = ldq(c, array, offsetof(Array, count));
                jcc(c, LIR_GT, lir_r(count), lir_i(n), fail);
                return true;
        }

        case INSTR_ENSURE_LEN_TUPLE: {
                expect(c, c->ops, at, VALUE_TUPLE, fail);
                LirReg count = ldw(c, c->ops, at + VOFF(count));
                jcc(c, LIR_GT, lir_r(count), lir_i(n), fail);
                c->tuple_off = node->next;
                c->tuple_sp  = c->sp - 1;
                c->tuple_min = 0;
                return true;
        }

        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE:
                return index_tuple(c, node, n, fail, fused);

        case INSTR_TRY_INDEX: {
                if (n < 0) {
                        return false;
                }

                bool     required = (u8)ip[9];
                LirLabel missing  = required ? fail : newlabel(c);
                LirLabel done     = newlabel(c);

                expect(c, c->ops, at, VALUE_ARRAY, fail);

                LirReg array = ldp(c, c->ops, at + VOFF(array));
                LirReg count = ldq(c, array, offsetof(Array, count));

                jcc(c, LIR_LE, lir_r(count), lir_i(n), missing);

                LirReg items = ldp(c, array, offsetof(Array, items));

                copy(c, c->ops, at + sizeof (Value), items, vat(n));
                nil_unless_found(c, required, missing, done);
                return true;
        }

        default:
                return false;
        }
}
