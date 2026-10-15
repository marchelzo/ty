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
        return (loop->nslots != 0) || loop->stack;
}

inline static i32
opslot(BcLir const *c, i32 off)
{
        return load_i32(c->code + off + 1);
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
touch(BcLir const *c, BcLoop const *loop, i32 off, bool *def)
{
        BcLirNode const *n = &c->nodes[off];

        *def = false;

        if (!local_op(n->op)) {
                return 0;
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
        return inside(loop, off) ? loop->live[off - loop->head] : 0;
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
choose(BcLir const *c, BcLoop *loop, i32 *score)
{
        memset(score, 0, c->bound * sizeof *score);

        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (dead(n) || !local_op(n->op)) {
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
        }
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

        loop->sp = head->sp;

        choose(c, loop, score);

        loop->stack = counted(c, loop);

        if (promoted(loop)) {
                loop->deopt = newlabel(c);
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
        c->lreg   = nones(c, LirReg, c->bound);
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
        }

        i32 n = loop->nowned++;

        c->lreg[slot]       = r;
        loop->owned_bit[n] = 1 << k;
        loop->owned[n]     = slot;
        loop->owned_reg[n] = r;
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

                if (loop->stack) {
                        pin_pair(c, loop);
                }

                c->active[c->nactive++] = i;
        }
}

static void
loop_leave(BcLir *c, i32 off)
{
        while (c->nactive > 0 && c->loops[c->active[c->nactive - 1]].end < off) {
                BcLoop const *loop = &c->loops[c->active[--c->nactive]];

                for (i32 k = 0; k < loop->nowned; ++k) {
                        c->lreg[loop->owned[k]] = LIR_NONE;
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

static void
loop_osr(BcLir *c, i32 off, i32 sp)
{
        LirLabel fail = LIR_NONE;

        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop const *loop = &c->loops[i];

                if ((loop->nowned == 0 && !loop->stack) || !inside(loop, off)) {
                        continue;
                }

                if (fail == LIR_NONE) {
                        fail = newlabel(c);
                }

                if (loop->stack) {
                        unstack(c, loop->sp - 2, loop->sreg[0], fail);
                        unstack(c, loop->sp - 1, loop->sreg[1], fail);
                }

                for (i32 k = 0; k < loop->nowned; ++k) {
                        if (live_at(loop, off) & loop->owned_bit[k]) {
                                reload(c, loop->owned[k], loop->owned_reg[k], fail, false);
                        } else {
                                retag(c, loop->owned[k]);
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
                        bail(c, loop->head);
                }
        }
}

static void
writeback(BcLir *c, i32 slot)
{
        put(c, lspot(c, slot), c->lreg[slot], lreal(c, slot));

        if (c->known_gen != NULL) {
                c->known_gen[slot] = 0;
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

        vset(c, LIR_ADD, r, lir_r(r), lir_i(up ? 1 : -1));
        writeback(c, slot);
        vs_push(c, VS_INT, post ? old : snap(c, slot), 0);

        return true;
}

static bool
loop_mutate(BcLir *c, i32 slot, u8 op, bool real)
{
        if (!accepts(&c->vs[c->sp - 1], real, false)) {
                vs_deopt(c);
                return true;
        }

        LirReg r = c->lreg[slot];
        LirReg x = lnum(c, c->sp - 1, real);

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
