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

static LirReg
blob_slot(BcLir *c, i32 container, i32 index, LirLabel slow)
{
        expect(c, c->ops, vat(container), VALUE_BLOB, slow);
        expect(c, c->ops, vat(index), VALUE_INTEGER, slow);

        LirReg i     = ldq(c, c->ops, vat(index) + VOFF(z));
        LirReg blob  = ldp(c, c->ops, vat(container) + VOFF(blob));

        jcc(c, LIR_UGE, lir_r(i), lir_r(ldq(c, blob, offsetof(Blob, count))), slow);

        return lea(c, ldp(c, blob, offsetof(Blob, items)), i, 0);
}

static void
dict_lookup(BcLir *c, LirReg base, i32 at, i32 key, i32 out, LirLabel done)
{
        LirLabel missing = newlabel(c);
        LirReg   dict    = ldp(c, base, at + VOFF(dict));

        sync_sp(c);

        LirReg item = ccall(c, dict_get_value, LT_PTR, preg(c->ty), preg(dict), preg(slot_of(c, key)));

        jz(c, item, missing);
        copy(c, c->ops, vat(out), item, 0);
        jump(c, done);

        bind(c, missing);
        put_scalar(c, out, VALUE_NIL, lir_i(0));
        jump(c, done);
}

static i32
literal_key(BcLir const *c, BcLirNode const *node)
{
        i32 off = (i32)(node - c->nodes);

        if (node->label != LIR_NONE || off < 5) {
                return -1;
        }

        BcLirNode const *prev = &c->nodes[off - 5];

        return (prev->op == INSTR_STRING && prev->next == off) ? load_i32(c->code + off - 4) : -1;
}

static bool
keyed_subscript(BcLir *c, BcLirNode const *node)
{
        i32 id = literal_key(c, node);

        if (id < 0) {
                return false;
        }

        Value    key  = literal_string(id);
        i32      at   = vat(c->sp - 2);
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);

        expect(c, c->ops, at, VALUE_DICT, slow);

        LirReg dict = ldp(c, c->ops, at + VOFF(dict));
        LirReg item = ccall(
                c,
                dict_find_hashed,
                LT_PTR,
                preg(c->ty),
                preg(dict),
                preg(slot_of(c, c->sp - 1)),
                { LT_I64, lir_i((i64)value_hash(c->ctx, &key)) }
        );

        jz(c, item, slow);
        copy(c, c->ops, at, item, 0);
        jump(c, done);

        bind(c, slow);
        tycall(c, jit_rt_subscript, LT_VOID, preg(slot_of(c, c->sp - 2)));

        bind(c, done);
        c->sp -= 1;

        return true;
}

static void
fast_subscript(BcLir *c, BcLirNode const *node)
{
        if (keyed_subscript(c, node)) {
                return;
        }

        LirLabel slow  = newlabel(c);
        LirLabel bytes = newlabel(c);
        LirLabel dict  = newlabel(c);
        LirLabel done  = newlabel(c);
        LirReg   slot  = array_slot(c, c->sp - 2, c->sp - 1, bytes);

        copy(c, c->ops, vat(c->sp - 2), slot, 0);
        jump(c, done);

        bind(c, bytes);
        LirReg p = blob_slot(c, c->sp - 2, c->sp - 1, dict);
        put_scalar(c, c->sp - 2, VALUE_INTEGER, lir_r(ldx(c, LIR_LD_U8, LIR_I64, p, 0)));
        jump(c, done);

        bind(c, dict);
        unless(c, tag_of(c, c->sp - 2), VALUE_DICT, slow);
        dict_lookup(c, c->ops, vat(c->sp - 2), c->sp - 1, c->sp - 2, done);

        bind(c, slow);
        tycall(c, jit_rt_subscript, LT_VOID, preg(slot_of(c, c->sp - 2)));

        bind(c, done);
        c->sp -= 1;
}

static void
fast_assign_subscript(BcLir *c)
{
        LirLabel slow  = newlabel(c);
        LirLabel bytes = newlabel(c);
        LirLabel done  = newlabel(c);
        LirReg   slot  = array_slot(c, c->sp - 2, c->sp - 1, bytes);

        copy(c, slot, 0, c->ops, vat(c->sp - 3));
        jump(c, done);

        bind(c, bytes);
        LirReg p = blob_slot(c, c->sp - 2, c->sp - 1, slow);
        expect(c, c->ops, vat(c->sp - 3), VALUE_INTEGER, slow);
        stb(c, p, 0, lir_r(int_at(c, c->sp - 3)));
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
        case INSTR_MUT_DIV:
        case INSTR_MUT_AND:
        case INSTR_MUT_OR:
        case INSTR_MUT_XOR:
        case INSTR_MUT_SHL:
        case INSTR_MUT_SHR: return true;
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
mutate_mixed(BcLir *c, LirOp op, LirReg base, i32 at, i32 rhs, LirReg a, LirReg b, LirLabel done)
{
        LirReg r = binop(c, op, LIR_F64, lir_r(a), lir_r(b));

        put_real(c, base, at, r);
        put_real(c, c->ops, rhs, r);
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
        LirOp fop = LIR_NONE;

        switch (op) {
        case INSTR_MUT_ADD: iop = LIR_ADD; fop = LIR_FADD; break;
        case INSTR_MUT_SUB: iop = LIR_SUB; fop = LIR_FSUB; break;
        case INSTR_MUT_MUL: iop = LIR_MUL; fop = LIR_FMUL; break;
        case INSTR_MUT_AND: iop = LIR_AND;                 break;
        case INSTR_MUT_OR:  iop = LIR_OR;                  break;
        case INSTR_MUT_XOR: iop = LIR_XOR;                 break;
        case INSTR_MUT_SHL: iop = LIR_SHL;                 break;
        default:            iop = LIR_SAR;                 break;
        }

        LirLabel real = (fop == LIR_NONE) ? slow : newlabel(c);

        unless(c, lt, VALUE_INTEGER, real);
        unless(c, rt, VALUE_INTEGER, real);

        LirReg a = ldq(c, base, at + VOFF(z));
        LirReg b = ldq(c, c->ops, rhs + VOFF(z));

        if (iop == LIR_SHL || iop == LIR_SAR) {
                b = binop(c, LIR_AND, LIR_I64, lir_r(b), lir_i(63));
        }

        LirReg r = binop(c, iop, LIR_I64, lir_r(a), lir_r(b));

        stq(c, base, at + VOFF(z), lir_r(r));
        stq(c, c->ops, rhs + VOFF(z), lir_r(r));
        jump(c, done);

        if (fop == LIR_NONE) {
                return;
        }

        LirLabel both = newlabel(c);
        LirLabel lint = newlabel(c);
        LirLabel rint = newlabel(c);

        bind(c, real);
        unless(c, lt, VALUE_REAL, lint);
        unless(c, rt, VALUE_REAL, rint);

        bind(c, both);
        mutate_real(c, fop, base, at, rhs, done);

        bind(c, rint);
        unless(c, rt, VALUE_INTEGER, slow);
        mutate_mixed(
                c,
                fop,
                base,
                at,
                rhs,
                ldf(c, base, at + VOFF(real)),
                unop(c, LIR_I2F, LIR_F64, lir_r(ldq(c, c->ops, rhs + VOFF(z)))),
                done
        );

        bind(c, lint);
        unless(c, lt, VALUE_INTEGER, slow);
        unless(c, rt, VALUE_REAL, slow);
        mutate_mixed(
                c,
                fop,
                base,
                at,
                rhs,
                unop(c, LIR_I2F, LIR_F64, lir_r(ldq(c, base, at + VOFF(z)))),
                ldf(c, c->ops, rhs + VOFF(real)),
                done
        );
}

static bool
fuse_non_nil(BcLir *c, BcLirNode const *next, i32 slot)
{
        if (next->op != INSTR_TRY_ASSIGN_NON_NIL) {
                return false;
        }

        LirLabel target = exit_edge(c, next->target);

        if (target == LIR_NONE) {
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
        u32 next = c->offset;

        c->offset = check - c->nodes;
        tycall(c, jit_rt_loop_iter, LT_VOID, preg(slot_of(c, sp)));
        c->offset = next;

        LirReg more = tycall(
                c,
                jit_rt_loop_check,
                LT_I32,
                imm32(check->member | (check->pairs ? LOOP_PAIRS : 0)),
                preg(slot_of(c, sp + 1))
        );

        jnz(c, more, exit);
}

static void
iter_slow(BcLir *c, BcLirNode const *check, i32 sp, LirReg pin, LirReg cell, LirLabel exit)
{
        i32 iz = vat(sp - 2) + VOFF(z);

        if (pin != LIR_NONE) {
                stq(c, c->ops, iz, lir_r(pin));
        }

        loop_slow(c, check, sp, exit);

        if (pin != LIR_NONE) {
                vset(c, LIR_LD_I64, pin, mref(c->ops, iz));
        }

        if (cell != LIR_NONE) {
                mov(c, cell, lea(c, c->ops, LIR_NONE, vat(sp + 1)));
        }
}

static BcLirNode const *
loop_check_of(BcLir const *c, BcLirNode const *node)
{
        if (c->dynamic || node->op != INSTR_LOOP_ITER || node->next >= c->size) {
                return NULL;
        }

        BcLirNode const *check = next_of(c, node);

        if (
                (check->op != INSTR_LOOP_CHECK)
             || (check->label != LIR_NONE)
             || (check->member < 1 || check->member > 2)
             || (check->pairs && check->member != 2)
             || (c->nodes[check->target].label == LIR_NONE)
        ) {
                return NULL;
        }

        T2Type type  = (c->hints != NULL) ? find_type_hint(c->hints, node - c->nodes) : T2_TYPE_INVALID;
        Class *class = (type != T2_TYPE_INVALID) ? expected_class_of(c->ctx, type) : NULL;
        i32    id    = (class != NULL) ? class->i : -1;
        bool   other = check->pairs ? (id != CLASS_ARRAY && id != CLASS_DICT)
                                    : (id != CLASS_ARRAY && id != CLASS_STRING);

        return (id >= 0 && other) ? NULL : check;
}

static BcLirNode const *
iter_check(BcLir const *c, BcLirNode const *node)
{
        BcLirNode const *check = loop_check_of(c, node);

        return (check != NULL && !check->pairs) ? check : NULL;
}

inline static u64
odd_inverse(u64 d)
{
        u64 x = d;

        for (int i = 0; i < 5; ++i) {
                x *= 2 - d * x;
        }

        return x;
}

static LirReg
dict_off(BcLir *c, LirReg items, LirReg item)
{
        enum {
                SHIFT = __builtin_ctz(sizeof (DictItem)),
                ODD   = sizeof (DictItem) >> SHIFT
        };

        LirLabel done = newlabel(c);
        LirReg   off  = lir_reg(c->L, LIR_I64);
        LirReg   k    = binop(c, LIR_SHR, LIR_I64, lir_r(binr(c, LIR_SUB, LIR_I64, item, items)), lir_i(SHIFT));

        vset(c, LIR_LI, off, lir_i(PTRDIFF_MAX));
        jz(c, item, done);
        vset(c, LIR_MUL, off, lir_r(k), lir_i((i64)odd_inverse(ODD)));
        vset(c, LIR_ADD, off, lir_r(off), lir_i(1));
        bind(c, done);

        return off;
}

static void
sentinel_at(BcLir *c, i32 sp)
{
        if (c->vs != NULL) {
                c->vs[sp] = (BcSlot) { .kind = VS_CSENT };
        } else {
                stq(c, c->ops, vat(sp), lir_i(VALUE_SENTINEL));
        }
}

static void
pair_out(BcLir *c, i32 sp, LirReg first, LirReg second)
{
        copy(c, c->ops, vat(sp + 1), second, 0);
        copy(c, c->ops, vat(sp + 2), first, 0);
}

static void
fast_pairs(BcLir *c, BcLirNode const *check, i32 sp, LirLabel exit)
{
        i32      iz   = vat(sp - 2) + VOFF(z);
        i32      io   = vat(sp - 2) + offsetof(Value, off);
        LirLabel slow = coldlabel(c);
        LirLabel dict = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   tag  = tag_of(c, sp - 1);

        unless(c, tag, VALUE_ARRAY, dict);

        LirReg array = ldp(c, c->ops, vat(sp - 1) + VOFF(array));
        LirReg i     = ldq(c, c->ops, iz);

        jcc(c, LIR_GE, lir_r(i), lir_r(ldq(c, array, offsetof(Array, count))), exit);

        LirReg pair = elem(c, ldp(c, array, offsetof(Array, items)), i, 0);

        expect(c, pair, 0, VALUE_TUPLE, slow);
        unless(c, ldw(c, pair, VOFF(count)), 2, slow);
        stq(c, c->ops, iz, lir_r(plus(c, i, 1)));

        LirReg xs = ldp(c, pair, VOFF(items));

        pair_out(c, sp, xs, lea(c, xs, LIR_NONE, sizeof (Value)));
        jump(c, done);

        bind(c, dict);
        unless(c, tag, VALUE_DICT, slow);

        LirReg   d     = ldp(c, c->ops, vat(sp - 1) + VOFF(dict));
        LirReg   items = ldp(c, d, offsetof(Dict, items));
        LirReg   off   = lir_reg(c->L, LIR_I64);
        LirLabel ready = newlabel(c);

        vset(c, LIR_LD_I64, off, mref(c->ops, io));
        jnz(c, off, ready);
        mov(c, off, dict_off(c, items, ldp(c, d, offsetof(Dict, first))));
        bind(c, ready);

        jcc(c, LIR_GT, lir_r(off), lir_r(ldq(c, d, offsetof(Dict, size))), exit);

        LirReg item = lea(
                c,
                items,
                binop(c, LIR_MUL, LIR_I64, lir_r(off), lir_i(sizeof (DictItem))),
                -(i32)sizeof (DictItem)
        );

        stq(c, c->ops, io, lir_r(dict_off(c, items, ldp(c, item, offsetof(DictItem, next)))));
        pair_out(c, sp, lea(c, item, LIR_NONE, offsetof(DictItem, k)), lea(c, item, LIR_NONE, offsetof(DictItem, v)));
        jump(c, done);

        bind(c, slow);
        loop_slow(c, check, sp, exit);

        bind(c, done);
        sentinel_at(c, sp);
}

static void
step_index(BcLir *c, i32 sp, LirReg i, LirReg pin)
{
        i32 iz = vat(sp - 2) + VOFF(z);

        if (pin == LIR_NONE) {
                stq(c, c->ops, iz, lir_r(plus(c, i, 1)));
                return;
        }

        vset(c, LIR_ADD, pin, lir_r(pin), lir_i(1));

        if (!lazy_pinned(c, sp - 2)) {
                stq(c, c->ops, iz, lir_r(pin));
        }
}

static void
iter_text(BcLir *c, LirReg tag, i32 sp, LirReg pin, LirReg cell, LirLabel exit, LirLabel slow)
{
        i32 io = vat(sp - 2) + offsetof(Value, off);
        i32 at = vat(sp - 1);
        i32 to = vat(sp + 1);

        unless(c, tag, VALUE_STRING, slow);

        LirReg off = ldq(c, c->ops, io);

        jcc(c, LIR_GE, lir_r(off), lir_r(ldx(c, LIR_LD_U32, LIR_I64, c->ops, at + VOFF(bytes))), exit);

        LirReg p = lea(c, ldp(c, c->ops, at + VOFF(str)), off, 0);

        jcc(c, LIR_UGE, lir_r(ldx(c, LIR_LD_U8, LIR_I64, p, 0)), lir_i(0x80), slow);
        stq(c, c->ops, io, lir_r(plus(c, off, 1)));
        step_index(c, sp, (pin != LIR_NONE) ? pin : ldq(c, c->ops, vat(sp - 2) + VOFF(z)), pin);

        stq(c, c->ops, to, lir_i(VALUE_STRING));
        stq(c, c->ops, to + VOFF(str), lir_r(p));
        stw(c, c->ops, to + VOFF(bytes), lir_i(1));
        stb(c, c->ops, to + VOFF(ro), lir_r(ldx(c, LIR_LD_U8, LIR_I64, c->ops, at + VOFF(ro))));
        stq(c, c->ops, to + VOFF(str0), lir_r(ldq(c, c->ops, at + VOFF(str0))));

        if (cell != LIR_NONE) {
                mov(c, cell, slot_of(c, sp + 1));
        }
}

static bool
fast_loop(BcLir *c, BcLirNode const *node)
{
        BcLirNode const *check = loop_check_of(c, node);

        if (check == NULL) {
                return false;
        }

        if (check->pairs) {
                c->offset = check->next;
                fast_pairs(c, check, c->sp, exit_edge(c, check->target));
                return true;
        }

        i32              sp   = c->sp;
        BcLirNode const *next = next_of(c, check);
        LirReg const    *held = iter_held(c, c->at);
        LirReg           pin  = loop_pinned(c, sp - 2) ? c->spin[sp - 2] : LIR_NONE;
        LirLabel         exit = exit_edge(c, check->target);
        LirLabel         slow = (held == NULL) ? coldlabel(c) : LIR_NONE;
        LirLabel         text = (held == NULL && check->member == 1) ? newlabel(c) : slow;
        LirReg           cell = LIR_NONE;
        LirReg           tag  = LIR_NONE;
        LirReg           count;
        LirReg           items;

        if ((c->vs != NULL) && (check->member == 1) && (next->op == INSTR_ASSIGN_LOCAL)) {
                cell = lir_reg(c->L, LIR_PTR);
        }

        c->offset = check->next;

        if (held != NULL) {
                count = held[1];
                items = held[2];
        } else {
                tag = tag_of(c, sp - 1);
                unless(c, tag, VALUE_ARRAY, text);
                LirReg array = ldp(c, c->ops, vat(sp - 1) + VOFF(array));
                count = ldq(c, array, offsetof(Array, count));
                items = ldp(c, array, offsetof(Array, items));
        }

        LirReg i = (pin != LIR_NONE) ? pin : ldq(c, c->ops, vat(sp - 2) + VOFF(z));

        jcc(c, LIR_GE, lir_r(i), lir_r(count), exit);

        if (check->member == 2) {
                put_scalar(c, sp + 1, VALUE_INTEGER, lir_r(i));
        }

        LirReg item = elem(c, items, i, 0);

        if (cell != LIR_NONE) {
                mov(c, cell, item);
        } else {
                copy(c, c->ops, vat(sp + check->member), item, 0);
        }

        step_index(c, sp, i, pin);

        if (held == NULL) {
                LirLabel done = newlabel(c);

                jump(c, done);

                if (text != slow) {
                        bind(c, text);
                        iter_text(c, tag, sp, pin, cell, exit, slow);
                        jump(c, done);
                }

                bind(c, slow);
                iter_slow(c, check, sp, pin, cell, exit);
                bind(c, done);
        }

        sentinel_at(c, sp);

        if (cell != LIR_NONE) {
                c->vs[sp + 1] = (BcSlot) { .kind = VS_CELL, .r = cell };
        }

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

static i32
class_tag(i32 class)
{
        switch (class) {
        case CLASS_INT:    return VALUE_INTEGER;
        case CLASS_FLOAT:  return VALUE_REAL;
        case CLASS_STRING: return VALUE_STRING;
        case CLASS_BOOL:   return VALUE_BOOLEAN;
        case CLASS_ARRAY:  return VALUE_ARRAY;
        case CLASS_DICT:   return VALUE_DICT;
        case CLASS_BLOB:   return VALUE_BLOB;
        case CLASS_TUPLE:  return VALUE_TUPLE;
        default:           return -1;
        }
}

static bool
testable(BcLir const *c, i32 id)
{
        if (class_tag(id) >= 0) {
                return true;
        }

        return (id > CLASS_PRIMITIVE) && !class_get(c->ctx, id)->is_trait;
}

static void
instance_branch(BcLir *c, i32 slot, i32 id, LirLabel yes, LirLabel no)
{
        Class const *class = class_get(c->ctx, id);
        i32          at    = vat(slot);
        i32          want  = class_tag(id);
        LirLabel     slow  = newlabel(c);
        LirLabel     other = newlabel(c);
        LirReg       type  = tagat(c, c->ops, at);

        if (want >= 0) {
                jcc(c, LIR_EQ, lir_r(type), lir_i(want), yes);
        }

        unless(c, type, VALUE_OBJECT, other);

        if (want < 0) {
                jcc(c, LIR_EQ, lir_r(ldw(c, c->ops, at + VOFF(class))), lir_i(id), yes);
        }

        jnz(c, ldx(c, LIR_LD_U8, LIR_I64, pval(c, &class->extended), 0), slow);
        jump(c, no);

        bind(c, other);
        jcc(c, LIR_EQ, lir_r(type), lir_i(VALUE_JIT_FUNCTION), slow);
        jcc(c, LIR_UGE, lir_r(type), lir_i(VALUE_TAGGED), slow);
        jump(c, no);

        bind(c, slow);
        sync_sp(c);
        jnz(c, tycall(c, jit_rt_jii, LT_BOOL, preg(slot_of(c, slot)), imm32(id)), yes);
        jump(c, no);
}

static LirReg
tag_list(BcLir *c, LirReg tags)
{
        LirReg lists = pval(c, tags_lists());

        return ldp(c, lea(c, lists, binop(c, LIR_SHL, LIR_I64, lir_r(tags), lir_i(3)), 0), 0);
}

static void
pop_tag(BcLir *c, i32 at, i32 tag, LirLabel fail)
{
        LirLabel keep = newlabel(c);
        LirReg   tags = ldx(c, LIR_LD_U16, LIR_I64, c->ops, at + VOFF(tags));

        jz(c, tags, fail);

        LirReg list = tag_list(c, tags);

        jcc(c, LIR_NE, lir_r(ldw(c, list, offsetof(struct tags, tag))), lir_i(tag), fail);

        LirReg rest = ldw(c, ldp(c, list, offsetof(struct tags, next)), offsetof(struct tags, n));
        LirReg type = tagat(c, c->ops, at);

        store(c, LIR_ST16, c->ops, at + VOFF(tags), lir_r(rest));
        jnz(c, rest, keep);
        stb(c, c->ops, at + VOFF(type), lir_r(binop(c, LIR_AND, LIR_I64, lir_r(type), lir_i(~VALUE_TAGGED & 0xff))));

        bind(c, keep);
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

        case INSTR_TRY_TAG_POP:
                pop_tag(c, at, n, fail);
                return true;

        case INSTR_JII:
        case INSTR_JNI: {
                i32 id = (n < 0) ? -n : n;

                if (!testable(c, id)) {
                        return false;
                }

                LirLabel next = newlabel(c);

                if (node->op == INSTR_JII) {
                        instance_branch(c, c->sp - 1, id, fail, next);
                } else {
                        instance_branch(c, c->sp - 1, id, next, fail);
                }

                bind(c, next);
                return true;
        }

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
