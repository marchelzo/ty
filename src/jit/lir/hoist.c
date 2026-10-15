#include "impl.h"

#define new(T, n)  stA(T, (n))
#define new0(T, n) stA0(T, (n))
#define nones(n)   ((u32 *)memset(new(u32, (n)), 0xff, (usize)(n) * sizeof (u32)))

enum {
        MAX_LOOPS = 64
};

typedef struct {
        LirReg root;
        i64    off;
} Addr;

typedef struct {
        i64 lo;
        i64 hi;
} Span;

typedef struct {
        Ty           *ty;
        Lir          *L;
        LirCFG        cfg;
        u32           n;
        u32           nregs;
        u32          *defs;
        Addr         *addr;
        bool         *body;
        bool         *latch;
        u32           header;
        bool          hotcall;
        bool         *moved;
        bool         *fresh;
        bool         *invariant;
        u32          *order;
        u32           norder;
        bool          unknown_store;
        bool          polls;
        LirReg        frame;
        i64           floor;
        vec(Span)     stores[LIR_MAX_PINS + 1];
        LirReg        roots[LIR_MAX_PINS + 1];
        u32           nroots;
} Hoist;

inline static LirInst *
at(Hoist const *h, u32 pc)
{
        return v_(h->L->insts, pc);
}

static void
count_defs(Hoist *h)
{
        Ty *ty = h->ty;

        h->defs = new0(u32, h->nregs + 1);

        for (u32 r = 0; r < h->nregs; ++r) {
                h->defs[r] += (v__(h->L->regs, r).param != LIR_NONE);
        }

        for (u32 pc = 0; pc < h->n; ++pc) {
                LirInst const *in = at(h, pc);
                each_write(in, r) {
                        h->defs[r] += 1;
                }
        }
}

static bool
resolved(Hoist const *h, LirReg r)
{
        return h->addr[r].root != LIR_NONE;
}

static void
addresses(Hoist *h)
{
        Ty        *ty      = h->ty;
        Lir const *L       = h->L;
        bool       changed = true;

        h->addr = new(Addr, h->nregs + 1);

        for (u32 r = 0; r < h->nregs; ++r) {
                LirRegInfo const *ri    = v_(L->regs, r);
                bool              stack = (ri->pin < 8) && ((L->stack_pins >> ri->pin) & 1);
                h->addr[r] = (Addr) { (stack && ri->param != LIR_NONE) ? r : LIR_NONE, 0 };
        }

        while (changed) {
                changed = false;

                for (u32 pc = 0; pc < h->n; ++pc) {
                        LirInst const *in = at(h, pc);
                        LirOpnd const *a  = in->args;
                        LirReg         d  = in->dst;
                        Addr           x  = { LIR_NONE, 0 };

                        if (d == LIR_NONE || h->defs[d] != 1 || resolved(h, d)) {
                                continue;
                        }

                        if (
                                (in->op == LIR_LEA)
                             && (a[0].mem.index == LIR_NONE)
                             && resolved(h, a[0].mem.base)
                        ) {
                                x = h->addr[a[0].mem.base];
                                x.off += a[0].mem.disp;
                        } else if (
                                (in->op == LIR_MOV)
                             && (a[0].kind == LO_REG)
                             && resolved(h, a[0].reg)
                        ) {
                                x = h->addr[a[0].reg];
                        } else if (
                                (in->op == LIR_ADD)
                             && (a[0].kind == LO_REG)
                             && (a[1].kind == LO_IMM)
                             && resolved(h, a[0].reg)
                        ) {
                                x = h->addr[a[0].reg];
                                x.off += a[1].imm;
                        }

                        if (x.root != LIR_NONE) {
                                h->addr[d] = x;
                                changed    = true;
                        }
                }
        }

        for (u32 r = 0; r < h->nregs; ++r) {
                LirRegInfo const *ri = v_(L->regs, r);
                if (!resolved(h, r) && (ri->pin < 8) && ((L->stack_pins >> ri->pin) & 1)) {
                        h->addr[r] = (Addr) { r, 0 };
                }
        }
}

static u32
root_index(Hoist *h, LirReg root)
{
        for (u32 k = 0; k < h->nroots; ++k) {
                if (h->roots[k] == root) {
                        return k;
                }
        }

        if (h->nroots == LIR_MAX_PINS) {
                return LIR_NONE;
        }

        h->roots[h->nroots] = root;

        return h->nroots++;
}

static bool
stackish(Hoist const *h, LirReg r)
{
        return resolved(h, r);
}

static void
note_store(Hoist *h, LirMem m, u32 size)
{
        Ty *ty = h->ty;
        u32 k  = stackish(h, m.base) ? root_index(h, h->addr[m.base].root) : LIR_NONE;

        if (m.index != LIR_NONE || k == LIR_NONE) {
                h->unknown_store = true;
                return;
        }

        i64 lo = h->addr[m.base].off + m.disp;

        svP(h->stores[k], ((Span) { lo, lo + size }));
}

static u32
op_size(LirOp op)
{
        return lir_type_size(LirOps[op].type);
}

static bool
writes_memory(Hoist *h, LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_ST:
                note_store(h, in->args[0].mem, op_size(in->op));
                return false;

        case LF_COPY:
                note_store(h, in->args[0].mem, 32);
                return false;

        case LF_CAS:
        case LF_ATOMIC:
                note_store(h, in->args[0].mem, 8);
                return true;

        case LF_POLL:
                h->polls = true;
                return false;

        case LF_RAW:
                h->unknown_store = true;
                return true;

        default:
                return false;
        }
}

static bool
frame_load(Hoist const *h, LirInst const *in)
{
        if (LirOps[in->op].form != LF_LD) {
                return false;
        }

        LirMem m = in->args[0].mem;

        if (m.index != LIR_NONE || !stackish(h, m.base) || h->unknown_store) {
                return false;
        }

        Addr a  = h->addr[m.base];
        i64  lo = a.off + m.disp;
        i64  hi = lo + op_size(in->op);

        if (h->polls && (a.root != h->frame || lo < 0 || hi > h->floor)) {
                return false;
        }

        for (u32 k = 0; k < h->nroots; ++k) {
                if (h->roots[k] != a.root) {
                        continue;
                }
                for (u32 j = 0; j < vN(h->stores[k]); ++j) {
                        Span s = v__(h->stores[k], j);
                        if (s.lo < hi && lo < s.hi) {
                                return false;
                        }
                }
        }

        return true;
}

static bool
pure(LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_MOV:
                return in->args[0].kind != LO_VSLOT;

        case LF_LI:
        case LF_FLI:
        case LF_LEA:
        case LF_IBINARY:
        case LF_IUNARY:
        case LF_FBINARY:
        case LF_FUNARY:
        case LF_FMA:
        case LF_I2F:
        case LF_F2I:
        case LF_FEXT:
        case LF_FTRUNC:
        case LF_BITCAST:
        case LF_SETCC:
        case LF_FSETCC:
        case LF_SELECT:
        case LF_FSELECT:
                return true;

        default:
                return false;
        }
}

static bool
operands_invariant(Hoist const *h, LirInst const *in)
{
        for (u32 j = 0; j < in->nargs; ++j) {
                LirReg rs[2];
                for (u32 k = 0, m = reads_at(in, j, rs); k < m; ++k) {
                        if (!h->invariant[rs[k]]) {
                                return false;
                        }
                }
        }

        return true;
}

static bool
barrier(LirInst const *in)
{
        return (in->op == LIR_RAW)
            || (in->op == LIR_ENTRY)
            || (in->flags & LIR_RETURNS_TWICE);
}

typedef struct {
        u32  header;
        bool done;
} Loop;

static u32
loops(Hoist *h, Loop *out)
{
        Ty           *ty    = h->ty;
        LirCFG const *g     = &h->cfg;
        u32           nb    = g->nblocks;
        u8           *state = new0(u8, nb + 1);
        u32          *stack = new(u32, nb + 1);
        u32          *edge  = new(u32, nb + 1);
        u32           n     = 0;

        h->latch = new0(bool, nb + 1);

        for (u32 root = 0; root < nb; ++root) {
                LirBlock const *r = &g->blocks[root];

                if (state[root] != 0 || !r->reachable || (root != 0 && !r->entry)) {
                        continue;
                }

                u32 sp = 0;

                stack[sp]   = root;
                edge[sp++]  = 0;
                state[root] = 1;

                while (sp != 0) {
                        u32             b = stack[sp - 1];
                        LirBlock const *x = &g->blocks[b];

                        if (edge[sp - 1] == x->nsucc) {
                                state[b] = 2;
                                sp      -= 1;
                                continue;
                        }

                        u32 t = x->succ[edge[sp - 1]++];

                        if (state[t] == 0) {
                                state[t]   = 1;
                                stack[sp]  = t;
                                edge[sp++] = 0;
                                continue;
                        }

                        if (state[t] != 1 || t > b) {
                                continue;
                        }

                        h->latch[b] = true;

                        bool dup = false;

                        for (u32 k = 0; k < n && !dup; ++k) {
                                dup = (out[k].header == t);
                        }

                        if (!dup && n < MAX_LOOPS) {
                                out[n++] = (Loop) { .header = t };
                        }
                }
        }

        return n;
}

static bool
collect(Hoist *h, u32 hb, u32 **preds, u32 *npreds)
{
        Ty           *ty    = h->ty;
        LirCFG const *g     = &h->cfg;
        u32          *queue = new(u32, g->nblocks + 1);
        u32           head  = 0;
        u32           tail  = 0;

        memset(h->body, 0, g->nblocks + 1);
        h->body[hb] = true;

        for (u32 j = 0; j < npreds[hb]; ++j) {
                u32 p = preds[hb][j];
                if (p >= hb && h->latch[p] && !h->body[p]) {
                        h->body[p] = true;
                        queue[tail++] = p;
                }
        }

        while (head < tail) {
                u32 b = queue[head++];
                for (u32 j = 0; j < npreds[b]; ++j) {
                        u32 p = preds[b][j];
                        if (p < hb) {
                                return false;
                        }
                        if (!h->body[p]) {
                                h->body[p] = true;
                                queue[tail++] = p;
                        }
                }
        }

        u32 outside = 0;

        for (u32 j = 0; j < npreds[hb]; ++j) {
                outside += !h->body[preds[hb][j]];
        }

        if (outside == 0 || g->blocks[hb].entry) {
                return false;
        }

        if (hb > 0) {
                LirBlock const *prev = &g->blocks[hb - 1];
                LirInst const  *last = (prev->first < prev->end) ? at(h, prev->end - 1) : NULL;
                bool            fall = (last != NULL)
                                    && (last->op != LIR_JMP)
                                    && (last->op != LIR_SWITCH)
                                    && (last->op != LIR_RET)
                                    && (last->op != LIR_TAILCALL)
                                    && !(last->flags & LIR_NORETURN);
                if (fall && h->body[hb - 1]) {
                        return false;
                }
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (h->body[b] && b != hb && g->blocks[b].entry) {
                        return false;
                }
        }

        return true;
}

static bool
refreshes_after(LirInst const *in)
{
        return (in->op == LIR_CALL) && !(in->flags & LIR_NORETURN);
}

static bool
costly(LirInst const *in)
{
        switch (in->op) {
        case LIR_SDIV:
        case LIR_UDIV:
        case LIR_SREM:
        case LIR_UREM:
        case LIR_MULHS:
        case LIR_MULHU:
        case LIR_FDIV:
        case LIR_FSQRT:
        case LIR_FMA:
        case LIR_I2F:
        case LIR_U2F:
        case LIR_F2I:
                return true;

        default:
                return LirOps[in->op].form == LF_LD;
        }
}

static bool
likely(Hoist const *h, u32 pb, u32 sb)
{
        LirBlock const *P  = &h->cfg.blocks[pb];
        LirBlock const *S  = &h->cfg.blocks[sb];
        LirInst const  *in = at(h, P->end - 1);

        return (S->first <= P->first)
            || (in->op == LIR_JMP)
            || (in->op == LIR_SWITCH)
            || ((S->first == P->end) && (in->op != LIR_RET));
}

static bool
hot_call(Hoist *h, u32 **preds, u32 *npreds)
{
        Ty           *ty  = h->ty;
        LirCFG const *g   = &h->cfg;
        bool         *hot = new0(bool, g->nblocks + 1);

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (!h->body[b]) {
                        continue;
                }

                hot[b] = (b == h->header);

                for (u32 j = 0; !hot[b] && j < npreds[b]; ++j) {
                        u32 p = preds[b][j];
                        hot[b] = h->body[p] && (p < b) && hot[p] && likely(h, p, b);
                }

                for (u32 pc = g->blocks[b].first; hot[b] && pc < g->blocks[b].end; ++pc) {
                        if (refreshes_after(at(h, pc))) {
                                return true;
                        }
                }
        }

        return false;
}

static void
prune(Hoist *h)
{
        Ty   *ty   = h->ty;
        bool *keep = new0(bool, h->n + 1);
        u32  *def  = nones(h->nregs + 1);
        u32   n    = 0;

        for (u32 o = 0; o < h->norder; ++o) {
                u32 pc = h->order[o];
                def[at(h, pc)->dst] = pc;
                keep[pc] = costly(at(h, pc)) && !(h->fresh[pc] && h->hotcall);
        }

        for (u32 o = h->norder; o-- > 0;) {
                LirInst const *in = at(h, h->order[o]);

                if (!keep[h->order[o]]) {
                        continue;
                }

                for (u32 j = 0; j < in->nargs; ++j) {
                        LirReg rs[2];
                        for (u32 k = 0, m = reads_at(in, j, rs); k < m; ++k) {
                                if (def[rs[k]] != LIR_NONE) {
                                        keep[def[rs[k]]] = true;
                                }
                        }
                }
        }

        for (u32 o = 0; o < h->norder; ++o) {
                u32 pc = h->order[o];
                if (keep[pc]) {
                        h->order[n++] = pc;
                } else {
                        h->moved[pc] = false;
                        h->fresh[pc] = false;
                }
        }

        h->norder = n;
}

static void
select_candidates(Hoist *h)
{
        Ty           *ty = h->ty;
        LirCFG const *g  = &h->cfg;

        h->invariant = new(bool, h->nregs + 1);
        h->moved     = new0(bool, h->n + 1);
        h->fresh     = new0(bool, h->n + 1);
        h->order     = new(u32, h->n + 1);
        h->norder    = 0;

        for (u32 r = 0; r < h->nregs; ++r) {
                h->invariant[r] = true;
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (!h->body[b]) {
                        continue;
                }
                for (u32 pc = g->blocks[b].first; pc < g->blocks[b].end; ++pc) {
                        each_write(at(h, pc), r) {
                                h->invariant[r] = false;
                        }
                }
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (!h->body[b]) {
                        continue;
                }

                for (u32 pc = g->blocks[b].first; pc < g->blocks[b].end; ++pc) {
                        LirInst const *in = at(h, pc);
                        LirReg         d  = in->dst;

                        if (
                                (d == LIR_NONE)
                             || (in->raw.nout != 0)
                             || (h->defs[d] != 1)
                             || !operands_invariant(h, in)
                        ) {
                                continue;
                        }

                        bool load = frame_load(h, in);

                        if (!load && !pure(in)) {
                                continue;
                        }

                        bool stale = load;

                        for (u32 j = 0; j < in->nargs && !stale; ++j) {
                                LirReg rs[2];
                                for (u32 k = 0, m = reads_at(in, j, rs); k < m; ++k) {
                                        for (u32 o = 0; o < h->norder; ++o) {
                                                LirInst const *x = at(h, h->order[o]);
                                                stale = stale || (h->fresh[h->order[o]] && x->dst == rs[k]);
                                        }
                                }
                        }

                        h->invariant[d]   = true;
                        h->moved[pc]      = true;
                        h->fresh[pc]      = stale;
                        h->order[h->norder++] = pc;
                }
        }

        prune(h);
}

static bool
summarize(Hoist *h)
{
        LirCFG const *g = &h->cfg;

        h->unknown_store = false;
        h->polls         = false;
        h->nroots        = 0;

        for (u32 k = 0; k <= LIR_MAX_PINS; ++k) {
                v0(h->stores[k]);
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (!h->body[b]) {
                        continue;
                }

                for (u32 pc = g->blocks[b].first; pc < g->blocks[b].end; ++pc) {
                        LirInst const *in = at(h, pc);

                        if (barrier(in)) {
                                return false;
                        }

                        writes_memory(h, in);
                }
        }

        return true;
}

static void
frame_floor(Hoist *h)
{
        Lir const *L   = h->L;
        LirReg     fr  = L->pins[LIR_PIN_1];
        LirReg     ops = L->pins[LIR_PIN_3];
        u8         m   = (1 << LIR_PIN_1) | (1 << LIR_PIN_3);

        h->frame = LIR_NONE;
        h->floor = 0;

        if (
                ((L->stack_pins & m) == m)
             && (fr != LIR_NONE)
             && (ops != LIR_NONE)
             && (h->addr[ops].root == fr)
             && (h->addr[ops].off > 0)
        ) {
                h->frame = fr;
                h->floor = h->addr[ops].off;
        }
}

static bool
header_label(Hoist const *h, LirLabel l, u32 first)
{
        return v__(h->L->labels, l).pos == first;
}

static void
retarget(Hoist const *h, LirInst *in, u32 first, LirLabel pre)
{
        for (u32 j = 0; j < in->nargs; ++j) {
                if (in->args[j].kind == LO_LABEL && header_label(h, in->args[j].label, first)) {
                        in->args[j].label = pre;
                }
        }

        for (u32 j = 0; j < in->ntargets; ++j) {
                if (header_label(h, in->targets[j], first)) {
                        in->targets[j] = pre;
                }
        }
}

static void
rebuild(Hoist *h, u32 hb)
{
        Ty           *ty      = h->ty;
        Lir          *L       = h->L;
        LirCFG const *g       = &h->cfg;
        u32           first   = g->blocks[hb].first;
        LirInst      *old     = vv(L->insts);
        u32           n       = h->n;
        u32           nlabels = vN(L->labels);
        u32          *pos     = new(u32, n + 1);
        u32           nfresh  = 0;
        LirLabel      pre;

        for (u32 o = 0; o < h->norder; ++o) {
                nfresh += h->fresh[h->order[o]];
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (h->body[b]) {
                        continue;
                }
                for (u32 pc = g->blocks[b].first; pc < g->blocks[b].end; ++pc) {
                        retarget(h, &old[pc], first, nlabels);
                }
        }

        xvP(L->labels, ((LirLabelInfo) { .pos = LIR_NONE }));
        pre = nlabels;

        LirInst *moved = new(LirInst, h->norder + 1);

        for (u32 o = 0; o < h->norder; ++o) {
                moved[o] = old[h->order[o]];
        }

        v00(L->insts);

        for (u32 pc = 0; pc < n; ++pc) {
                if (pc == first) {
                        v_(L->labels, pre)->pos = vN(L->insts);
                        for (u32 o = 0; o < h->norder; ++o) {
                                xvP(L->insts, moved[o]);
                        }
                }

                pos[pc] = vN(L->insts);

                if (h->moved[pc]) {
                        continue;
                }

                xvP(L->insts, old[pc]);

                if (nfresh != 0 && h->body[g->block_at[pc]] && refreshes_after(&old[pc])) {
                        for (u32 o = 0; o < h->norder; ++o) {
                                if (h->fresh[h->order[o]]) {
                                        xvP(L->insts, moved[o]);
                                }
                        }
                }
        }

        pos[n] = vN(L->insts);

        for (u32 i = 0; i < nlabels; ++i) {
                LirLabelInfo *l = v_(L->labels, i);
                if (l->pos != LIR_NONE) {
                        l->pos = pos[l->pos];
                }
        }

        xmF(old);
}

static bool
hoist_one(Hoist *h, Loop *loops, u32 nloops)
{
        Ty           *ty     = h->ty;
        LirCFG const *g      = &h->cfg;
        u32          *npreds = new0(u32, g->nblocks + 1);
        u32         **preds  = new(u32 *, g->nblocks + 1);

        for (u32 b = 0; b < g->nblocks; ++b) {
                LirBlock const *x = &g->blocks[b];
                for (u32 j = 0; x->reachable && j < x->nsucc; ++j) {
                        npreds[x->succ[j]] += 1;
                }
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                preds[b]  = new(u32, npreds[b] + 1);
                npreds[b] = 0;
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                LirBlock const *x = &g->blocks[b];
                for (u32 j = 0; x->reachable && j < x->nsucc; ++j) {
                        u32 t = x->succ[j];
                        preds[t][npreds[t]++] = b;
                }
        }

        h->body = new(bool, g->nblocks + 1);

        for (;;) {
                u32 best = LIR_NONE;
                u32 size = UINT32_MAX;

                for (u32 k = 0; k < nloops; ++k) {
                        if (loops[k].done) {
                                continue;
                        }

                        if (!collect(h, loops[k].header, preds, npreds)) {
                                loops[k].done = true;
                                continue;
                        }

                        u32 n = 0;

                        for (u32 b = 0; b < g->nblocks; ++b) {
                                n += h->body[b];
                        }

                        if (n < size) {
                                size = n;
                                best = k;
                        }
                }

                if (best == LIR_NONE) {
                        return false;
                }

                loops[best].done = true;

                collect(h, loops[best].header, preds, npreds);

                if (!summarize(h)) {
                        continue;
                }

                h->header  = loops[best].header;
                h->hotcall = hot_call(h, preds, npreds);

                select_candidates(h);

                if (h->norder != 0) {
                        rebuild(h, loops[best].header);
                        return true;
                }
        }
}

static LirLabel
header_of(Hoist const *h, u32 hb)
{
        u32 first = h->cfg.blocks[hb].first;

        for (u32 l = 0; l < vN(h->L->labels); ++l) {
                if (v__(h->L->labels, l).pos == first) {
                        return l;
                }
        }

        return LIR_NONE;
}

bool
lir_hoist(Ty *ty, Lir *L, LirError *err)
{
        if (getenv("TY_JIT_NO_HOIST") != NULL) {
                return true;
        }

        ty = lir_scratch(ty);

        SCRATCH_SAVE();

        Hoist    h      = { .ty = ty, .L = L };
        LirLabel done[MAX_LOOPS];
        u32      ndone  = 0;
        bool     ok     = true;

        for (u32 round = 0; ok && round < MAX_LOOPS; ++round) {
                h.n     = vN(L->insts);
                h.nregs = vN(L->regs);

                if (!lir_cfg(ty, L, &h.cfg, err)) {
                        ok = false;
                        break;
                }

                count_defs(&h);
                addresses(&h);
                frame_floor(&h);

                Loop     all[MAX_LOOPS];
                LirLabel names[MAX_LOOPS];
                u32      nloops = loops(&h, all);
                u32      before = 0;

                for (u32 k = 0; k < nloops; ++k) {
                        names[k] = header_of(&h, all[k].header);
                        for (u32 j = 0; j < ndone; ++j) {
                                all[k].done = all[k].done || (done[j] == names[k]);
                        }
                        all[k].done = all[k].done || (names[k] == LIR_NONE);
                        before     += !all[k].done;
                }

                if (before == 0 || !hoist_one(&h, all, nloops)) {
                        break;
                }

                for (u32 k = 0; k < nloops && ndone < MAX_LOOPS; ++k) {
                        bool seen = false;
                        for (u32 j = 0; j < ndone; ++j) {
                                seen = seen || (done[j] == names[k]);
                        }
                        if (all[k].done && !seen && names[k] != LIR_NONE) {
                                done[ndone++] = names[k];
                        }
                }
        }

        SCRATCH_RESTORE();

        if (ok && ndone != 0 && getenv("TY_JIT_VALIDATE") != NULL) {
                bool trusted = L->trusted;
                L->trusted   = false;
                ok           = lir_validate(ty, L, err);
                L->trusted   = trusted;
        }

        return ok;
}
