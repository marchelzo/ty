inline static bool
lreal(BcLir const *c, i32 slot)
{
        return c->local_class[slot] == CLASS_FLOAT;
}

inline static bool
dead(BcLirNode const *n)
{
        return (n->next == 0) || (n->sp < 0);
}

inline static bool
inside(BcLoop const *loop, i32 off)
{
        return (off >= loop->head) && (off <= loop->end);
}

inline static bool
promoted(BcLoop const *loop)
{
        return (loop->nslots != 0) || loop->stack || (loop->narrays != 0);
}


static bool
backedge(BcLir const *c, i32 off)
{
        BcLirNode const *n = &c->nodes[off];

        return !dead(n)
            && n->branch
            && (n->target > 0)
            && (n->target <= off);
}

static LirReg
loop_reg(BcLir const *c, i32 slot)
{
        return (c->lreg != NULL && local_ok(c, slot)) ? c->lreg[slot] : LIR_NONE;
}

static bool
loop_pinned(BcLir const *c, i32 pos)
{
        return (c->spin != NULL) && (c->spin[pos] != LIR_NONE);
}

static bool
single_entry(BcLir const *c, BcLoop const *loop)
{
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n) || inside(loop, off)) {
                        continue;
                }

                if (n->branch && inside(loop, n->target)) {
                        return false;
                }

                each_arm(c, n, to) {
                        if (inside(loop, to)) {
                                return false;
                        }
                }
        }

        return true;
}

static bool
targetable(BcLir const *c, BcLirNode const *node, bool real)
{
        if (node->next <= 0 || node->next >= c->size) {
                return false;
        }

        BcLirNode const *next = next_of(c, node);

        if (next->label != LIR_NONE || next->sp < 0) {
                return false;
        }

        switch (next->op) {
        case INSTR_MUT_ADD:
        case INSTR_MUT_SUB:
        case INSTR_MUT_MUL:
        case INSTR_ASSIGN:
                return true;

        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC:
                return !real;

        default:
                return false;
        }
}

static bool
falls(u8 op)
{
        switch (op) {
        case INSTR_JUMP:
        case INSTR_RETURN:
        case INSTR_RETURN_PRESERVE_CTX:
        case INSTR_THROW:
        case INSTR_RETHROW:
        case INSTR_HALT:
                return false;

        default:
                return true;
        }
}

static u8
captured_bits(BcLir const *c, BcLoop const *loop, i32 off)
{
        u8 bits = 0;

        for (i32 k = 0; k < loop->nslots; ++k) {
                if (captures(c, off, loop->slots[k])) {
                        bits |= 1 << k;
                }
        }

        return bits;
}

static u8
touch(BcLir const *c, BcLoop const *loop, i32 off, bool *def)
{
        BcLirNode const *n = &c->nodes[off];

        *def = false;

        if (!local_op(n->op)) {
                return captured_bits(c, loop, off);
        }

        i32 slot = opslot(c, off);

        for (i32 k = 0; k < loop->nslots; ++k) {
                if (loop->slots[k] == slot) {
                        bool target = (n->op == INSTR_TARGET_LOCAL);
                        *def = (n->op == INSTR_ASSIGN_LOCAL)
                            || (target && c->nodes[n->next].op == INSTR_ASSIGN);
                        return 1 << k;
                }
        }

        return 0;
}

static u8
live_at(BcLoop const *loop, i32 off)
{
        return (loop->live != NULL && inside(loop, off)) ? loop->live[off - loop->head] : 0;
}

static void
liveness(BcLir const *c, BcLoop *loop)
{
        loop->live = new(c, u8, loop->end - loop->head + 1);

        for (bool changed = true; changed;) {
                changed = false;

                for (i32 off = loop->end; off >= loop->head; --off) {
                        BcLirNode const *n   = &c->nodes[off];
                        u8               out = 0;
                        bool             def;

                        if (dead(n)) {
                                continue;
                        }

                        if (falls(n->op)) {
                                out |= live_at(loop, n->next);
                        }

                        if (n->branch) {
                                out |= live_at(loop, n->target);
                        }

                        each_arm(c, n, to) {
                                out |= live_at(loop, to);
                        }

                        u8 bit = touch(c, loop, off, &def);
                        u8 in  = def ? (out & ~bit) : (out | bit);

                        if (in != loop->live[off - loop->head]) {
                                loop->live[off - loop->head] = in;
                                changed = true;
                        }
                }
        }
}

static u8
writers(BcLir const *c, BcLoop const *loop)
{
        u8 bits = 0;

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n)) {
                        continue;
                }

                bits |= captured_bits(c, loop, off);

                if (n->op != INSTR_ASSIGN_LOCAL && n->op != INSTR_TARGET_LOCAL) {
                        continue;
                }

                i32 slot = opslot(c, off);

                for (i32 k = 0; k < loop->nslots; ++k) {
                        if (loop->slots[k] == slot) {
                                bits |= 1 << k;
                        }
                }
        }

        return bits;
}

static u8
escapers(BcLir const *c, BcLoop const *loop)
{
        u8 bits = 0;

        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n) || inside(loop, off)) {
                        continue;
                }

                bits |= captured_bits(c, loop, off);

                if (!local_op(n->op)) {
                        continue;
                }

                i32 slot = opslot(c, off);

                for (i32 k = 0; k < loop->nslots; ++k) {
                        if (loop->slots[k] == slot) {
                                bits |= 1 << k;
                        }
                }
        }

        return bits;
}

static u8
written_within(BcLir const *c, BcLoop const *loop, BcLoop const *region)
{
        u8 bits = 0;

        for (i32 off = region->head; off <= region->end; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n)) {
                        continue;
                }

                bits |= captured_bits(c, loop, off);

                if (n->op != INSTR_ASSIGN_LOCAL && n->op != INSTR_TARGET_LOCAL) {
                        continue;
                }

                i32 slot = opslot(c, off);

                for (i32 k = 0; k < loop->nslots; ++k) {
                        if (loop->slots[k] == slot) {
                                bits |= 1 << k;
                        }
                }
        }

        return bits;
}

static i32
busiest(BcLir const *c, i32 const *score)
{
        i32 best = -1;

        for (i32 slot = 0; slot < c->bound; ++slot) {
                i32 class = c->local_class[slot];

                if (score[slot] <= 0 || (class != CLASS_INT && class != CLASS_FLOAT)) {
                        continue;
                }

                if (best < 0 || score[slot] > score[best]) {
                        best = slot;
                }
        }

        return best;
}

static void
exclude_captures(BcLir const *c, i32 off, i32 *score)
{
        i32 n = ncaptures(c, off);

        for (i32 i = 0; i < n; ++i) {
                i32 slot = capture_slot(c, off, i);

                if (local_ok(c, slot)) {
                        score[slot] = -1;
                }
        }
}

static void
choose(BcLir const *c, BcLoop *loop, i32 *score)
{
        memset(score, 0, c->bound * sizeof *score);

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n)) {
                        continue;
                }

                exclude_captures(c, off, score);

                if (!local_op(n->op)) {
                        continue;
                }

                i32 slot = opslot(c, off);

                if (!local_ok(c, slot) || score[slot] < 0) {
                        continue;
                }

                if (n->op == INSTR_TARGET_LOCAL && !targetable(c, n, lreal(c, slot))) {
                        score[slot] = -1;
                } else {
                        score[slot] += 1;
                }
        }

        loop->nslots = 0;

        while (loop->nslots < (i32)countof(loop->slots)) {
                i32 best = busiest(c, score);

                if (best < 0) {
                        break;
                }

                loop->slots[loop->nslots++] = best;
                score[best] = 0;
        }

        if (loop->nslots != 0) {
                liveness(c, loop);
                loop->written  = writers(c, loop);
                loop->escaping = escapers(c, loop);
        }
}

static i32
holdable(BcLir const *c, i32 slot)
{
        if (
                !local_ok(c, slot)
             || (c->local_type == NULL)
             || (slot == c->self_index)
             || (c->local_type[slot] == T2_TYPE_INVALID)
        ) {
                return -1;
        }

        Class *class = t2_class_of(c->ctx, c->local_type[slot]);

        if (
                (class == NULL)
             || (class->i != CLASS_ARRAY && class->i != CLASS_BLOB && class->i != CLASS_STRING)
        ) {
                return -1;
        }

        return class->i;
}

static bool
string_byte_at(BcLir const *c, i32 off)
{
        BcLirNode const *n = &c->nodes[off];

        return (n->op == INSTR_CALL_METHOD)
            && (n->argc == 1)
            && (n->nkw == 0)
            && (n->member == M_ID("byte"))
            && (off >= 5)
            && (c->nodes[off - 5].op == INSTR_LOAD_LOCAL)
            && (c->nodes[off - 5].next == off)
            && (holdable(c, opslot(c, off - 5)) == CLASS_STRING);
}

static bool
indexes(u8 op)
{
        return (op == INSTR_SUBSCRIPT) || (op == INSTR_ASSIGN_SUBSCRIPT) || (op == INSTR_COUNT);
}

static void
containers(BcLir const *c, BcLoop *loop, i32 *score)
{
        bool any = false;

        memset(score, 0, c->bound * sizeof *score);

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n)) {
                        continue;
                }

                bool bytes = string_byte_at(c, off);

                if (is_call(n->op) && !bytes) {
                        loop->narrays = 0;
                        return;
                }

                any = any || bytes || indexes(n->op);

                exclude_captures(c, off, score);

                if (!local_op(n->op)) {
                        continue;
                }

                i32 slot = opslot(c, off);

                if (!local_ok(c, slot)) {
                        continue;
                }

                if (n->op != INSTR_LOAD_LOCAL) {
                        score[slot] = -1;
                } else if (score[slot] >= 0 && holdable(c, slot) >= 0) {
                        score[slot] += 1;
                }
        }

        loop->narrays = 0;

        if (getenv("TY_JIT_NO_HOLD") != NULL) {
                return;
        }


        while (any && loop->narrays < (i32)countof(loop->arrays)) {
                i32 best = -1;

                for (i32 slot = 0; slot < c->bound; ++slot) {
                        if (
                                (score[slot] > 0)
                             && (score[slot] * 64 >= loop->end - loop->head)
                             && (best < 0 || score[slot] > score[best])
                        ) {
                                best = slot;
                        }
                }

                if (best < 0) {
                        break;
                }

                loop->akind[loop->narrays]    = holdable(c, best);
                loop->arrays[loop->narrays++] = best;
                score[best] = 0;

        }
}

static bool
breaks(BcLir const *c, BcLoop const *loop, BcLirNode const *n, i32 hs)
{
        if (n->op != INSTR_POP2 || n->sp != hs || n->next >= c->size) {
                return false;
        }

        BcLirNode const *jump = next_of(c, n);

        return (jump->op == INSTR_JUMP)
            && (jump->label == LIR_NONE)
            && !inside(loop, jump->target);
}

static bool
counted(BcLir const *c, BcLoop const *loop)
{
        BcLirNode const *head = &c->nodes[loop->head];
        BcLirNode const *back = &c->nodes[loop->end];
        i32              hs   = head->sp;
        i32              inc  = -1;

        if (head->op != INSTR_DUP2_SWAP || hs < 2 || back->op != INSTR_JUMP) {
                return false;
        }

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n)) {
                        continue;
                }

                if (breaks(c, loop, n, hs)) {
                        off = n->next;
                        continue;
                }

                if (n->sp < hs) {
                        return false;
                }

                if ((n->op == INSTR_SWAP || n->op == INSTR_DROP2) && n->sp <= hs + 2) {
                        return false;
                }

                if (n->op == INSTR_INC && n->next == loop->end && n->sp == hs) {
                        inc = off;
                        continue;
                }

                if (n->sp != hs || off == loop->end) {
                        continue;
                }

                BcLirNode const *next = (n->next < c->size) ? &c->nodes[n->next] : NULL;

                bool assigns = (n->op == INSTR_TARGET_LOCAL)
                            && (next != NULL)
                            && (next->op == INSTR_ASSIGN);

                bool grows = (next != NULL)
                          && (next->sp > hs)
                          && !n->branch;

                bool benign = (n->op == INSTR_JUMP)
                           || (n->op == INSTR_DUP2_SWAP)
                           || (n->op == INSTR_ASSIGN)
                           || assigns
                           || grows;

                if (!benign) {
                        return false;
                }
        }

        return inc >= 0;
}

static bool
tangled(BcLir const *c, i32 i)
{
        BcLoop const *loop = &c->loops[i];

        for (i32 j = 0; j < i; ++j) {
                BcLoop const *other = &c->loops[j];

                bool overlap = (other->head <= loop->end) && (loop->head <= other->end);
                bool nested  = (other->head <= loop->head && loop->end <= other->end)
                            || (loop->head <= other->head && other->end <= loop->end);

                if (overlap && !nested) {
                        return true;
                }
        }

        return false;
}

static BcLoop *
loop_at(BcLir *c, i32 head)
{
        for (i32 i = 0; i < c->nloops; ++i) {
                if (c->loops[i].head == head) {
                        return &c->loops[i];
                }
        }

        BcLoop *loop = &c->loops[c->nloops++];

        loop->head = head;

        return loop;
}

static bool
node_is(BcLir const *c, i32 off, u8 op, i32 next)
{
        return (off >= 0)
            && !dead(&c->nodes[off])
            && (c->nodes[off].op == op)
            && (c->nodes[off].next == next);
}

static i32
writes_of(BcLir const *c, BcLoop const *loop, i32 slot)
{
        i32 n = 0;

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (
                        !dead(node)
                     && (node->op == INSTR_TARGET_LOCAL || node->op == INSTR_ASSIGN_LOCAL)
                     && (opslot(c, off) == slot)
                ) {
                        n += 1;
                }

                if (!dead(node) && captures(c, off, slot)) {
                        n += 1;
                }
        }

        return n;
}

static void
ranged(BcLir const *c, BcLoop *loop)
{
        i32 h     = loop->head;
        i32 src   = h - 8;
        u8  shift = 0;

        loop->ivar = -1;

        if (
                !loop->stack
             || (h < 8)
             || !node_is(c, h - 2, INSTR_INT8, h)
             || (c->code[h - 1] != 0)
             || !node_is(c, h - 3, INSTR_COUNT, h - 2)
        ) {
                return;
        }

        if (h >= 13 && node_is(c, h - 8, INSTR_MEMBER_ACCESS, h - 3)) {
                Packed const *pk = packing(load_i32(c->code + h - 7));

                if (pk == NULL) {
                        return;
                }

                shift = pk->shift;
                src   = h - 13;
        }

        if (!node_is(c, src, INSTR_LOAD_LOCAL, src + 5)) {
                return;
        }

        i32  holder = opslot(c, src);
        bool held   = false;

        for (i32 k = 0; k < loop->narrays; ++k) {
                held |= (loop->arrays[k] == holder)
                     && (shift == 0 || loop->akind[k] == CLASS_BLOB);
        }

        BcLirNode const *head = &c->nodes[h];
        BcLirNode const *test = next_of(c, head);
        BcLirNode const *bind = next_of(c, test);

        if (
                !held
             || (test->op != INSTR_JGE)
             || (bind->op != INSTR_TARGET_LOCAL)
             || (bind->sp != head->sp)
             || (next_of(c, bind)->op != INSTR_ASSIGN)
        ) {
                return;
        }

        i32 ivar = opslot(c, bind - c->nodes);

        if (!local_ok(c, ivar) || writes_of(c, loop, ivar) != 1) {
                return;
        }

        loop->ivar   = ivar;
        loop->isrc   = holder;
        loop->ishift = shift;
}

static void
shape(BcLir *c, i32 i, i32 *score)
{
        BcLoop          *loop = &c->loops[i];
        BcLirNode const *head = &c->nodes[loop->head];

        if (
                (head->label == LIR_NONE)
             || (head->sp < 0)
             || !single_entry(c, loop)
             || tangled(c, i)
        ) {
                return;
        }

        loop->sp   = head->sp;
        loop->lazy = (c->nodes[loop->end].op == INSTR_JUMP) && (getenv("TY_JIT_NO_LAZY") == NULL);

        choose(c, loop, score);
        containers(c, loop, score);

        loop->stack = counted(c, loop);

        ranged(c, loop);

        if (promoted(loop)) {
                loop->deopt = coldlabel(c);
        }
}

static bool
loop_plan(BcLir *c)
{
        if (
                c->compact
             || !c->speculate
             || c->dynamic
             || c->has_try
             || (c->bound == 0)
             || (c->local_class == NULL)
             || (c->base_index == LIR_NONE)
             || (getenv("TY_JIT_NO_LOOP_REGS") != NULL)
        ) {
                return true;
        }

        i32 nloops = 0;

        for (i32 off = 0; off < c->size; ++off) {
                nloops += backedge(c, off);
        }

        if (nloops == 0) {
                return true;
        }

        c->loops  = new(c, BcLoop, nloops);
        c->held   = new(c, LirReg *, c->bound);
        c->hkind  = new(c, i32, c->bound);
        c->lreg   = nones(c, LirReg, c->bound);
        c->lowner = nones(c, i32, c->bound);
        c->cexits  = 2 * c->size + 16;
        c->exits   = new(c, BcExit, c->cexits);
        c->stubbed = new(c, bool, c->size);
        c->spin   = nones(c, LirReg, c->max_sp + 8);
        c->active = new(c, i32, nloops);

        for (i32 off = 0; off < c->size; ++off) {
                if (backedge(c, off)) {
                        loop_at(c, c->nodes[off].target)->end = off;
                }
        }

        i32 *score = new(c, i32, c->bound);

        for (i32 i = 0; i < c->nloops; ++i) {
                shape(c, i, score);
        }

        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop *outer = &c->loops[i];
                bool    leaf  = true;
                u8      busy  = 0;

                for (i32 j = 0; j < c->nloops; ++j) {
                        BcLoop const *inner = &c->loops[j];

                        if (i != j && inside(outer, inner->head) && inner->end <= outer->end && promoted(inner)) {
                                leaf  = false;
                                busy |= written_within(c, outer, inner);
                        }
                }

                outer->deferred = leaf ? 0xFF : busy;
        }

        return true;
}

static void
reload(BcLir *c, i32 slot, LirReg r, LirLabel fail, bool known)
{
        bool          real = lreal(c, slot);
        BcSlot const *v    = known ? vs_known(c, slot) : NULL;
        Spot          s    = lspot(c, slot);

        if (v != NULL && v->kind == (real ? VS_CREAL : VS_CINT)) {
                LirOpnd x = real ? lir_f(peek(double, &v->bits)) : lir_i((i64)v->bits);
                vset(c, real ? LIR_FLI : LIR_LI, r, x);
        } else if (v != NULL && v->kind == numkind(real)) {
                mov(c, r, v->r);
        } else {
                typecheck(c, s, numtag(real), fail);
                unbox_to(c, r, s, real);
        }
}

static void
retag(BcLir *c, i32 slot)
{
        stq(c, c->locals, vat(slot), lir_i(numtag(lreal(c, slot))));
}

static void
unstack(BcLir *c, i32 pos, LirReg r, LirLabel fail)
{
        Spot s = sspot(c, pos);

        typecheck(c, s, VALUE_INTEGER, fail);
        unbox_to(c, r, s, false);
}

static void
own(BcLir *c, BcLoop *loop, i32 k)
{
        i32 slot = loop->slots[k];

        if (c->lreg[slot] != LIR_NONE) {
                return;
        }

        LirReg r = lir_reg(c->L, numcls(lreal(c, slot)));

        if ((loop->live[0] >> k) & 1) {
                reload(c, slot, r, loop->deopt, true);
        } else {
                retag(c, slot);
                if (loop->lazy && ((loop->written & loop->escaping & loop->deferred) >> k) & 1) {
                        unbox_to(c, r, lspot(c, slot), lreal(c, slot));
                }
        }

        i32 n = loop->nowned++;

        c->lreg[slot]       = r;
        c->lowner[slot]     = (i32)(loop - c->loops);
        loop->owned_bit[n] = 1 << k;
        loop->owned[n]     = slot;
        loop->owned_reg[n] = r;
}

static void
refresh_as(BcLir *c, LirOp op, LirReg r, LirReg base, i32 disp)
{
        vset(c, op, r, mref(base, disp));
        vvL(c->L->insts)->flags |= LIR_REFRESH;
}

static void
refresh(BcLir *c, LirReg r, LirReg base, i32 disp)
{
        refresh_as(c, LIR_LD_I64, r, base, disp);
}

static void
view(BcLir *c, BcLoop const *loop, i32 k, LirLabel fail)
{
        Spot          s = lspot(c, loop->arrays[k]);
        LirReg const *r = loop->areg[k];

        if (loop->akind[k] == CLASS_STRING) {
                typecheck(c, s, VALUE_STRING, fail);
                refresh(c, r[0], s.base, s.at + VOFF(str));
                refresh_as(c, LIR_LD_U32, r[1], s.base, s.at + VOFF(bytes));
                refresh(c, r[2], s.base, s.at + VOFF(str));
                return;
        }

        if (loop->akind[k] == CLASS_BLOB) {
                typecheck(c, s, VALUE_BLOB, fail);
                refresh(c, r[0], s.base, s.at + VOFF(blob));
                refresh(c, r[1], r[0], offsetof(Blob, count));
                refresh(c, r[2], r[0], offsetof(Blob, items));
                return;
        }

        typecheck(c, s, VALUE_ARRAY, fail);
        refresh(c, r[0], s.base, s.at + VOFF(array));
        refresh(c, r[1], r[0], offsetof(Array, count));
        refresh(c, r[2], r[0], offsetof(Array, items));
}

static void
hold(BcLir *c, BcLoop *loop, i32 k)
{
        LirReg *r = loop->areg[k];

        if (c->held[loop->arrays[k]] != NULL) {
                r[0] = LIR_NONE;
                return;
        }

        r[0] = lir_reg(c->L, LIR_PTR);
        r[1] = lir_reg(c->L, LIR_I64);
        r[2] = lir_reg(c->L, LIR_PTR);

        view(c, loop, k, loop->deopt);

        c->held[loop->arrays[k]]  = r;
        c->hkind[loop->arrays[k]] = loop->akind[k];
}

static LirReg const *
held_any(BcLir const *c, i32 i)
{
        BcSlot const *s = &c->vs[i];

        if (s->kind != VS_LOCAL || c->held == NULL || !local_ok(c, (i32)s->bits)) {
                return NULL;
        }

        return c->held[(i32)s->bits];
}

static LirReg const *
held_kind(BcLir const *c, i32 i, i32 kind)
{
        LirReg const *r = held_any(c, i);

        return (r != NULL && c->hkind[(i32)c->vs[i].bits] == kind) ? r : NULL;
}

static LirReg const *
held_array(BcLir const *c, i32 i)
{
        return held_kind(c, i, CLASS_ARRAY);
}

static LirReg const *
held_blob(BcLir const *c, i32 i)
{
        return held_kind(c, i, CLASS_BLOB);
}

static LirReg const *
held_string(BcLir const *c, i32 i)
{
        return held_kind(c, i, CLASS_STRING);
}

static void
pin_pair(BcLir *c, BcLoop *loop)
{
        for (i32 k = 0; k < 2; ++k) {
                i32    pos = loop->sp - 2 + k;
                LirReg r   = lir_reg(c->L, LIR_I64);

                unstack(c, pos, r, loop->deopt);

                loop->sreg[k] = r;
                c->spin[pos]  = r;
                c->vs[pos]    = (BcSlot) { .kind = VS_INT, .r = r };
        }
}

static void
loop_enter(BcLir *c, i32 off)
{
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop *loop = &c->loops[i];

                if (loop->head != off || !promoted(loop)) {
                        continue;
                }

                loop->nowned = 0;

                for (i32 k = 0; k < loop->nslots; ++k) {
                        own(c, loop, k);
                }

                for (i32 k = 0; k < loop->narrays; ++k) {
                        hold(c, loop, k);
                }

                if (loop->stack) {
                        pin_pair(c, loop);
                }

                c->active[c->nactive++] = i;
        }
}

static void
local_stubs(BcLir *c, i32 index);

static void
loop_leave(BcLir *c, i32 off)
{
        while (c->nactive > 0 && c->loops[c->active[c->nactive - 1]].end < off) {
                i32           index = c->active[--c->nactive];
                BcLoop const *loop  = &c->loops[index];

                local_stubs(c, index);

                for (i32 k = 0; k < loop->nowned; ++k) {
                        c->lreg[loop->owned[k]] = LIR_NONE;
                }

                for (i32 k = 0; k < loop->narrays; ++k) {
                        if (loop->areg[k][0] != LIR_NONE) {
                                c->held[loop->arrays[k]] = NULL;
                        }
                }

                if (!loop->stack) {
                        continue;
                }

                for (i32 pos = loop->sp - 2; pos < loop->sp; ++pos) {
                        c->spin[pos]    = LIR_NONE;
                        c->vs[pos].kind = VS_MEM;
                }
        }
}

static u64
pack_slots(BcLir const *c, i32 const *slots, i32 n)
{
        u64 packed = 0;

        for (i32 i = 0; i < n && i < 4; ++i) {
                u64 e = (u64)(slots[i] + 1) & 0x7FFF;

                if (lreal(c, slots[i])) {
                        e |= 0x8000;
                }

                packed |= e << (16 * i);
        }

        return packed;
}

static void
loop_guard(BcLir *c, BcLoop const *loop, char const *what)
{
        char buf[384];
        int n = 0;

        if (!ProfMode) {
                return;
        }

        for (i32 k = 0; k < loop->nowned && n < (int)sizeof buf - 64; ++k) {
                n += snprintf(
                        buf + n,
                        sizeof buf - n,
                        "%s`%s`: %s",
                        (k > 0) ? ", " : "",
                        slot_label(c, loop->owned[k]),
                        lreal(c, loop->owned[k]) ? "Float" : "Int"
                );
        }

        if (loop->narrays > 0 && n < (int)sizeof buf - 64) {
                n += snprintf(buf + n, sizeof buf - n, "%s%d packed array view(s)", (n > 0) ? ", " : "", loop->narrays);
        }

        guard_note(c, "%s (unboxed: %s)", what, (n > 0) ? buf : "nothing");
}

static void
loop_osr(BcLir *c, i32 off, i32 sp)
{
        LirLabel fail  = LIR_NONE;
        u64      slots = 0;

        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop const *loop = &c->loops[i];

                if ((loop->nowned == 0 && !loop->stack && loop->narrays == 0) || !inside(loop, off)) {
                        continue;
                }

                if (fail == LIR_NONE) {
                        fail  = newlabel(c);
                        slots = pack_slots(c, loop->owned, loop->nowned);
                        loop_guard(c, loop, "entering the compiled loop requires its locals to have their loop types");
                }

                for (i32 k = 0; k < loop->narrays; ++k) {
                        if (loop->areg[k][0] != LIR_NONE) {
                                view(c, loop, k, fail);
                        }
                }

                if (loop->stack) {
                        unstack(c, loop->sp - 2, loop->sreg[0], fail);
                        unstack(c, loop->sp - 1, loop->sreg[1], fail);
                }

                for (i32 k = 0; k < loop->nowned; ++k) {
                        i32 slot = loop->owned[k];

                        if (live_at(loop, off) & loop->owned_bit[k]) {
                                reload(c, slot, loop->owned_reg[k], fail, false);
                        } else {
                                retag(c, slot);
                                if (loop->lazy && (loop->written & loop->escaping & loop->deferred & loop->owned_bit[k])) {
                                        unbox_to(c, loop->owned_reg[k], lspot(c, slot), lreal(c, slot));
                                }
                        }
                }
        }

        if (fail == LIR_NONE) {
                return;
        }

        LirLabel go = newlabel(c);

        jump(c, go);
        bind(c, fail);
        count_at(c, sp);
        deopt_why(c, JIT_WHY_LOOP_ENTRY, slots);
        bail(c, off);
        bind(c, go);
}

static void
loop_stubs(BcLir *c)
{
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop const *loop = &c->loops[i];

                if (promoted(loop)) {
                        bind(c, loop->deopt);
                        count_at(c, loop->sp);
                        loop_guard(c, loop, "a local the loop keeps unboxed changed type");
                        deopt_why(c, JIT_WHY_LOOP_TYPE, pack_slots(c, loop->owned, loop->nowned));
                        bail(c, loop->head);
                }
        }
}

static u8
slot_bit(BcLoop const *loop, i32 slot)
{
        for (i32 k = 0; k < loop->nslots; ++k) {
                if (loop->slots[k] == slot) {
                        return 1 << k;
                }
        }

        return 0;
}

static void
writeback(BcLir *c, i32 slot)
{
        BcLoop const *owner = &c->loops[c->lowner[slot]];

        if (!owner->lazy || !(owner->deferred & slot_bit(owner, slot))) {
                put(c, lspot(c, slot), c->lreg[slot], lreal(c, slot));
        }

        if (c->known_gen != NULL) {
                c->known_gen[slot] = 0;
        }
}

inline static bool
lazy_loop(BcLoop const *loop)
{
        return loop->lazy && ((loop->nowned != 0) || loop->stack);
}

static bool
lazy_pinned(BcLir const *c, i32 pos)
{
        for (i32 i = 0; i < c->nactive; ++i) {
                BcLoop const *loop = &c->loops[c->active[i]];

                if (lazy_loop(loop) && loop->stack && pos >= loop->sp - 2 && pos < loop->sp) {
                        return true;
                }
        }

        return false;
}

static bool
in_range(BcLir const *c, i32 idx, i32 cont, u8 shift)
{
        BcSlot const *x    = &c->vs[idx];
        BcSlot const *h    = &c->vs[cont];
        i32           slot = (x->kind == VS_LOCAL) ? (i32)x->bits : x->src - 1;

        if (slot < 0 || (x->kind != VS_LOCAL && x->off != 0) || h->kind != VS_LOCAL || getenv("TY_JIT_NO_RANGE") != NULL) {
                return false;
        }

        for (i32 i = 0; i < c->nactive; ++i) {
                BcLoop const *loop = &c->loops[c->active[i]];

                if (loop->ivar == slot && loop->isrc == (i32)h->bits && loop->ishift == shift) {
                        return true;
                }
        }

        return false;
}

static void
flush_pair(BcLir *c, BcLoop const *loop)
{
        for (i32 k = 0; loop->stack && k < 2; ++k) {
                put(c, sspot(c, loop->sp - 2 + k), loop->sreg[k], false);
        }
}

static void
flush_loop(BcLir *c, BcLoop const *loop, u8 mask)
{
        for (i32 k = 0; k < loop->nowned; ++k) {
                i32 slot = loop->owned[k];

                if (loop->written & loop->deferred & mask & loop->owned_bit[k]) {
                        put(c, lspot(c, slot), loop->owned_reg[k], lreal(c, slot));
                }
        }
}

static void
flush_active(BcLir *c)
{
        for (i32 i = 0; i < c->nactive; ++i) {
                BcLoop const *loop = &c->loops[c->active[i]];

                if (lazy_loop(loop)) {
                        flush_loop(c, loop, ProfMode ? 0xFF : loop->escaping | live_at(loop, c->at));
                        flush_pair(c, loop);
                }
        }
}

static void
flush_around(BcLir *c, i32 off)
{
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop const *loop = &c->loops[i];

                if (lazy_loop(loop) && inside(loop, off)) {
                        flush_loop(c, loop, loop->escaping | live_at(loop, off));
                        flush_pair(c, loop);
                }
        }
}

static LirLabel
exit_edge(BcLir *c, i32 to)
{
        if (to < 0 || to >= c->size) {
                return LIR_NONE;
        }

        LirLabel target = c->nodes[to].label;
        bool     leaves = false;

        for (i32 i = 0; i < c->nactive; ++i) {
                BcLoop const *loop = &c->loops[c->active[i]];
                leaves = leaves || (lazy_loop(loop) && !inside(loop, to));
        }

        if (target == LIR_NONE || !leaves) {
                return target;
        }

        i32 inner = c->active[c->nactive - 1];

        for (i32 i = 0; i < c->nexits; ++i) {
                if (c->exits[i].to == to && c->exits[i].inner == inner) {
                        return c->exits[i].stub;
                }
        }

        if (c->nexits == c->cexits) {
                c->ok = false;
                return target;
        }

        LirLabel stub = newlabel(c);

        c->exits[c->nexits++] = (BcExit) {
                .stub   = stub,
                .target = target,
                .to     = to,
                .inner  = inner
        };

        return stub;
}

static void
exit_stub(BcLir *c, BcExit *e)
{
        i32 from = c->loops[e->inner].head;

        e->done = true;
        bind(c, e->stub);

        for (i32 j = 0; j < c->nloops; ++j) {
                BcLoop const *loop = &c->loops[j];

                if (lazy_loop(loop) && inside(loop, from) && !inside(loop, e->to)) {
                        flush_loop(c, loop, loop->escaping);
                }
        }

        jump(c, e->target);
}

static void
local_stubs(BcLir *c, i32 index)
{
        BcLoop const *loop = &c->loops[index];

        if (!lazy_loop(loop)) {
                return;
        }

        LirLabel skip = newlabel(c);

        jump(c, skip);

        for (i32 i = 0; i < c->nexits; ++i) {
                if (!c->exits[i].done && c->exits[i].inner == index) {
                        exit_stub(c, &c->exits[i]);
                }
        }

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (node->deopt != LIR_NONE && reached(node) && !c->stubbed[off]) {
                        c->stubbed[off] = true;
                        bind(c, node->deopt);
                        flush_around(c, off);
                        deopt_why(c, JIT_WHY_POLL, 0);
                        leave(c, JIT_PACK(JIT_DEOPT, off));
                        tierup_stub(c, off);
                }
        }

        bind(c, skip);
}

static void
exit_stubs(BcLir *c)
{
        for (i32 i = 0; i < c->nexits; ++i) {
                BcExit *e = &c->exits[i];

                if (e->done) {
                        continue;
                }

                i32 from = c->loops[e->inner].head;

                e->done = true;
                bind(c, e->stub);

                for (i32 j = 0; j < c->nloops; ++j) {
                        BcLoop const *loop = &c->loops[j];

                        if (lazy_loop(loop) && inside(loop, from) && !inside(loop, e->to)) {
                                flush_loop(c, loop, loop->escaping);
                        }
                }

                jump(c, e->target);
        }
}

static LirReg
snap(BcLir *c, i32 slot)
{
        LirReg t = lir_reg(c->L, numcls(lreal(c, slot)));

        mov(c, t, c->lreg[slot]);

        return t;
}

static LirReg
lnum(BcLir *c, i32 i, bool real)
{
        u8 kind = c->vs[i].kind;

        if (!boxed(kind)) {
                LirReg r = vreg(c, i);
                return (real && !realish(kind)) ? vop(c, LIR_I2F, LIR_F64, lir_r(r)) : r;
        }

        Spot s = spot(c, i);

        guard_note(c, "assumed %s is %s inside the compiled loop", operand_label(c, i), NUM_LABEL(real));
        assume(c, s, numtag(real));

        return unbox(c, s, real);
}

static bool
accepts(BcSlot const *v, bool real, bool exact)
{
        if (boxed(v->kind)) {
                return true;
        }

        if (real) {
                return realish(v->kind) || (!exact && intish(v->kind));
        }

        return intish(v->kind);
}

static void
store_top(BcLir *c, i32 slot, bool real)
{
        BcSlot const *top = &c->vs[c->sp - 1];

        if (same_local(top, slot)) {
                return;
        }

        if (!accepts(top, real, true)) {
                guard_note(
                        c,
                        "`%s` is kept unboxed as %s in this loop, but the value assigned here is %s",
                        slot_label(c, slot),
                        NUM_LABEL(real),
                        kind_label(top->kind)
                );
                vs_deopt(c);
                return;
        }

        LirReg x = lnum(c, c->sp - 1, real);

        vs_release(c, slot);
        mov(c, c->lreg[slot], x);
        writeback(c, slot);
}

static bool
loop_step(BcLir *c, i32 slot, u8 op)
{
        bool   up   = (op == INSTR_PRE_INC) || (op == INSTR_POST_INC);
        bool   post = (op == INSTR_POST_INC) || (op == INSTR_POST_DEC);
        LirReg r    = c->lreg[slot];
        LirReg old  = post ? snap(c, slot) : LIR_NONE;

        vs_disown(c, slot);
        vset(c, LIR_ADD, r, lir_r(r), lir_i(up ? 1 : -1));
        writeback(c, slot);
        vs_push(c, VS_INT, post ? old : snap(c, slot), 0);

        return true;
}

static bool
loop_mutate(BcLir *c, i32 slot, u8 op, bool real)
{
        if (!accepts(&c->vs[c->sp - 1], real, false)) {
                guard_note(
                        c,
                        "`%s` is kept unboxed as %s in this loop, but it is updated with %s",
                        slot_label(c, slot),
                        NUM_LABEL(real),
                        kind_label(c->vs[c->sp - 1].kind)
                );
                vs_deopt(c);
                return true;
        }

        LirReg r = c->lreg[slot];
        LirReg x = lnum(c, c->sp - 1, real);

        vs_disown(c, slot);
        vset(c, mutop(op, real), r, lir_r(r), lir_r(x));
        writeback(c, slot);

        c->vs[c->sp - 1] = (BcSlot) { .kind = numkind(real), .r = snap(c, slot) };

        return true;
}

static bool
loop_target(BcLir *c, BcLirNode const *node, i32 slot, bool real)
{
        bool             ok   = targetable(c, node, real);
        BcLirNode const *next = next_of(c, node);

        if (!ok) {
                guard_note(c, "`%s` is kept unboxed as %s in this loop, but this assignment can't stay unboxed", slot_label(c, slot), NUM_LABEL(real));
                vs_deopt(c);
        }

        c->offset    = next->next;
        c->skip_next = true;

        if (!ok) {
                return true;
        }

        switch (next->op) {
        case INSTR_ASSIGN:
                store_top(c, slot, real);
                return true;

        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC:
                return loop_step(c, slot, next->op);

        default:
                return loop_mutate(c, slot, next->op, real);
        }
}

static bool
loop_lower(BcLir *c, BcLirNode const *node, char const *ip)
{
        i32 slot = load_i32(ip + 1);

        if (loop_reg(c, slot) == LIR_NONE) {
                return false;
        }

        bool real = lreal(c, slot);

        switch (node->op) {
        case INSTR_LOAD_LOCAL:
                vs_push(c, numkind(real), snap(c, slot), 0);
                c->vs[c->sp - 1].src = slot + 1;
                return true;

        case INSTR_ASSIGN_LOCAL:
                store_top(c, slot, real);
                vs_pop(c, 1);
                return true;

        case INSTR_TARGET_LOCAL:
                return loop_target(c, node, slot, real);

        default:
                return false;
        }
}
