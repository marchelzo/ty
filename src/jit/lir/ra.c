#include <string.h>
#include <stdlib.h>

#include "ty.h"
#include "jit/lir.h"

#define new(T, n)  ((T *)smA((usize)(n) * sizeof (T)))
#define new0(T, n) ((T *)smA0((usize)(n) * sizeof (T)))
#define nones(n)   ((u32 *)memset(new(u32, (n)), 0xff, (usize)(n) * sizeof (u32)))

#define cfor(c, x, k) for (u32 c = (x)->at[(k)]; c != LIR_NONE; c = v__((x)->next, c))
#define kids(c, s, r) for (u32 c = (r); c != LIR_NONE; c = iv((s), c)->next)

enum {
        MUST = 1,
        DEF  = 2
};

enum {
        BEST_HINT   = 0,
        BEST_FREE   = 1,
        BEST_SAVED  = 2,
        BEST_OTHER  = 3
};

static u64 const Never = UINT64_MAX;

typedef struct {
        u32 pos;
        u32 weight;
        u8  flags;
} Use;

typedef struct {
        u32 reg;
        u32 pos;
        u32 weight;
        u8  flags;
} Rec;

typedef struct {
        u32 reg;
        u32 start;
        u32 end;
} Span;

typedef struct {
        LirRange *r;
        u32       nr;
        Use      *u;
        u32       nu;
        u32      *defs;
        u32       ndefs;
} Group;

typedef struct {
        u32       rep;
        LirRange *r;
        u32       nr;
        Use      *u;
        u32       nu;
        u32       prev;
        u32       next;
        u32       cut;
        u8        phys;
        bool      stack;
        bool      clobbered;
        bool      resume;
        bool      calm;
} Iv;

typedef struct {
        u32 pos;
        u32 owner;
} Fix;

typedef struct {
        u32 pc;
        u32 weight;
} Copy;

typedef vec(u32) Ids;
typedef vec(Fix) Fixes;

typedef struct {
        u32     *at;
        u32     *last;
        vec(u32) next;
} Index;

typedef struct {
        Ty                 *ty;
        Lir const          *L;
        LirCFG const       *cfg;
        LirTarget const    *target;
        LirAlloc           *alloc;
        u32                 nregs;
        u32                 ninsts;
        u32                *parent;
        u32                *depth;
        u32                *weight;
        u32               **preds;
        u32                *npreds;
        Group                *sets;
        Use               **uses;
        u32                *nuses;
        u32                *remat;
        bool               *refresh;
        bool                stale;
        u8                 *phint;
        u32                *vhint;
        u32                *hpos;
        u32                *hweight;
        u32                *calls;
        u32                 ncalls;
        u64                 used[2];
        bool                trace;
        Index               index;
        vec(Iv)             ivs;
        Ids                 heap;
        Ids                 active;
        Ids                 inactive;
        Fixes               fixed[2][LIR_MAX_PHYS];
        vec(LirMove)        moves;
        vec(LirConstraint)  cons;
} Scan;

static bool
fail(LirError *err, u32 op, char const *why)
{
        return lir_fail(err, LE_TARGET, op, (LirSpan) {0}, "%s", why);
}

inline static u64
bit(u32 n)
{
        return (u64)1 << n;
}

inline static u32
least(u32 a, u32 b)
{
        return (a < b) ? a : b;
}

inline static u32
most(u32 a, u32 b)
{
        return (a > b) ? a : b;
}

inline static u64
alignup(u64 n, u64 a)
{
        return (n + a - 1) & ~(a - 1);
}

inline static u32
floor4(u32 pos)
{
        return pos & ~(u32)3;
}

inline static LirInst const *
inst(Scan const *s, u32 pc)
{
        return v_(s->L->insts, pc);
}

inline static LirClass
cls(Scan const *s, LirReg r)
{
        return v__(s->L->regs, r).cls;
}

inline static bool
fpreg(Scan const *s, LirReg r)
{
        return isfloat(cls(s, r));
}

inline static LirRegPool const *
pool(Scan const *s, bool f)
{
        return f ? &s->target->fpr : &s->target->gpr;
}

inline static Iv *
iv(Scan const *s, u32 i)
{
        return v_(s->ivs, i);
}

inline static u32
ivstart(Iv const *c)
{
        return c->r[0].start;
}

inline static u32
ivend(Iv const *c)
{
        return c->r[c->nr - 1].end;
}

inline static bool
ivbank(Scan const *s, Iv const *c)
{
        return fpreg(s, c->rep);
}

inline static LirInterval *
info(Scan const *s, LirReg r)
{
        return &s->alloc->intervals[r];
}

inline static u32
block_of(Scan const *s, u32 pos)
{
        u32 pc = least(pos / 4, s->ninsts);
        return s->cfg->block_at[pc];
}

inline static bool
starts_block(Scan const *s, u32 pos)
{
        return (pos % 4 == 0)
            && (pos / 4 < s->ninsts)
            && (s->cfg->blocks[block_of(s, pos)].first == pos / 4);
}

static u32
find(Scan *s, u32 r)
{
        while (s->parent[r] != r) {
                s->parent[r] = s->parent[s->parent[r]];
                r = s->parent[r];
        }

        return r;
}

static bool
isexit(LirInst const *in)
{
        return (in->op == LIR_RET)
            || (in->op == LIR_TAILCALL)
            || (in->flags & LIR_NORETURN);
}

static bool
isbranch(LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_CHECKED:
        case LF_BR:
        case LF_FBR:
        case LF_BRZ:
        case LF_JMP:
        case LF_SWITCH:
        case LF_POLL:   return true;
        default:        return false;
        }
}

static bool
falls(LirInst const *in)
{
        return !isexit(in) && (in->op != LIR_JMP) && (in->op != LIR_SWITCH);
}

inline static bool
iscall(LirOp op)
{
        return (op == LIR_CALL) || (op == LIR_TAILCALL);
}

static bool
may_gc(LirInst const *in)
{
        return (in->flags & (LIR_MAY_GC | LIR_MAY_THROW)) || (in->op == LIR_POLL);
}

static u32
regs_of(LirOpnd a, LirReg rs[2])
{
        switch (a.kind) {
        case LO_REG:
                rs[0] = a.reg;
                return 1;

        case LO_MEM:
                rs[0] = a.mem.base;
                rs[1] = a.mem.index;
                return (a.mem.index != LIR_NONE) ? 2 : 1;

        default:
                return 0;
        }
}

static u32
lower(u32 const *xs, u32 n, u32 x)
{
        u32 lo = 0;
        u32 hi = n;

        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (xs[mid] < x) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        return lo;
}

static bool
covers(LirRange const *r, u32 n, u32 pos)
{
        if (n == 0 || pos < r[0].start || pos >= r[n - 1].end) {
                return false;
        }

        u32 lo = 0;
        u32 hi = n;

        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (r[mid].start <= pos) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        return pos < r[lo - 1].end;
}

static u32
meet(LirRange const *a, u32 na, LirRange const *b, u32 nb)
{
        u32 i = 0;
        u32 j = 0;

        while (i < na && j < nb) {
                u32 lo = most(a[i].start, b[j].start);

                if (lo < a[i].end && lo < b[j].end) {
                        return lo;
                }

                if (a[i].end <= b[j].end) {
                        i += 1;
                } else {
                        j += 1;
                }
        }

        return LIR_NONE;
}

static LirRange *
unite(Ty *ty, LirRange const *a, u32 na, LirRange const *b, u32 nb, u32 *out)
{
        LirRange *r = new(LirRange, na + nb + 1);
        u32       i = 0;
        u32       j = 0;
        u32       n = 0;

        while (i < na || j < nb) {
                LirRange x = (j == nb || (i < na && a[i].start <= b[j].start)) ? a[i++] : b[j++];

                if (n != 0 && x.start <= r[n - 1].end) {
                        r[n - 1].end = most(r[n - 1].end, x.end);
                } else {
                        r[n++] = x;
                }
        }

        *out = n;

        return r;
}

static Use *
weave(Ty *ty, Use const *a, u32 na, Use const *b, u32 nb, u32 *out)
{
        Use *u = new(Use, na + nb + 1);
        u32  i = 0;
        u32  j = 0;
        u32  n = 0;

        while (i < na || j < nb) {
                Use x = (j == nb || (i < na && a[i].pos <= b[j].pos)) ? a[i++] : b[j++];

                if (n != 0 && x.pos == u[n - 1].pos) {
                        u[n - 1].flags  |= x.flags;
                        u[n - 1].weight  = most(u[n - 1].weight, x.weight);
                } else {
                        u[n++] = x;
                }
        }

        *out = n;

        return u;
}

static u32 *
merge_defs(Ty *ty, u32 const *a, u32 na, u32 const *b, u32 nb, u32 *out)
{
        u32 *d = new(u32, na + nb + 1);
        u32  i = 0;
        u32  j = 0;
        u32  n = 0;

        while (i < na || j < nb) {
                d[n++] = (j == nb || (i < na && a[i] <= b[j])) ? a[i++] : b[j++];
        }

        *out = n;

        return d;
}

static void
hook(Index *x, u32 key, u32 c)
{
        if (x->last[key] == LIR_NONE) {
                x->at[key] = c;
        } else {
                v__(x->next, x->last[key]) = c;
        }

        x->last[key] = c;
}

static Index
chain(Scan const *s)
{
        Ty   *ty = s->ty;
        u32   n  = s->ninsts;
        u32   nc = vN(s->cons);
        Index x  = {
                .at   = nones(n + 1),
                .last = nones(n + 1),
                .next = { .items = nones(nc + 1), .count = nc, .capacity = nc + 1 }
        };

        for (u32 c = 0; c < nc; ++c) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->op < n) {
                        hook(&x, con->op, c);
                }
        }

        return x;
}

static bool
constrained(Scan const *s, u32 pc, LirReg r, bool output)
{
        cfor (c, &s->index, pc) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->reg == r && con->output == output && con->phys != LIR_PHYS_NONE) {
                        return true;
                }
        }

        return false;
}

static bool
likely(Scan const *s, u32 pb, u32 sb)
{
        LirBlock const *P  = &s->cfg->blocks[pb];
        LirBlock const *S  = &s->cfg->blocks[sb];
        LirInst const  *in = inst(s, P->end - 1);

        if (
                (S->first <= P->first)
             || (s->depth[sb] < s->depth[pb])
             || (in->op == LIR_JMP)
             || (in->op == LIR_SWITCH)
             || !isbranch(in)
        ) {
                return true;
        }

        return falls(in) && (S->first == P->end);
}

static void
graph(Scan *s)
{
        Ty           *ty  = s->ty;
        LirCFG const *cfg = s->cfg;
        u32           nb  = cfg->nblocks;
        u32          *at  = new0(u32, nb + 1);

        s->preds  = new(u32 *, nb + 1);
        s->npreds = new0(u32, nb + 1);
        s->depth  = new0(u32, nb + 1);
        s->weight = new(u32, nb + 1);

        for (u32 b = 0; b < nb; ++b) {
                LirBlock const *x = &cfg->blocks[b];
                for (u32 j = 0; x->reachable && j < x->nsucc; ++j) {
                        at[x->succ[j]] += 1;
                }
        }

        for (u32 b = 0; b < nb; ++b) {
                s->preds[b] = new(u32, at[b] + 1);
        }

        for (u32 b = 0; b < nb; ++b) {
                LirBlock const *x = &cfg->blocks[b];
                for (u32 j = 0; x->reachable && j < x->nsucc; ++j) {
                        u32 t = x->succ[j];
                        s->preds[t][s->npreds[t]++] = b;
                }
        }

        u8  *state = new0(u8, nb + 1);
        u32 *stack = new(u32, nb + 1);
        u32 *edge  = new(u32, nb + 1);
        u32 *mark  = new0(u32, nb + 1);
        u32 *queue = new(u32, nb + 1);
        u32 *tails = new(u32, nb + 1);
        u32 *ntail = new0(u32, nb + 1);
        u32 *heads = new(u32, nb + 1);
        u32  nhead = 0;
        u32 *tbase = new0(u32, nb + 1);
        vec(u32) back = {0};

        for (u32 root = 0; root < nb; ++root) {
                LirBlock const *r = &cfg->blocks[root];

                if (state[root] != 0 || !r->reachable || (root != 0 && !r->entry)) {
                        continue;
                }

                u32 sp = 0;

                stack[sp] = root;
                edge[sp]  = 0;
                sp       += 1;
                state[root] = 1;

                while (sp != 0) {
                        u32             b = stack[sp - 1];
                        LirBlock const *x = &cfg->blocks[b];

                        if (edge[sp - 1] == x->nsucc) {
                                state[b] = 2;
                                sp      -= 1;
                                continue;
                        }

                        u32 t = x->succ[edge[sp - 1]++];

                        if (state[t] == 1) {
                                svP(back, b);
                                svP(back, t);
                        } else if (state[t] == 0) {
                                state[t]  = 1;
                                stack[sp] = t;
                                edge[sp]  = 0;
                                sp       += 1;
                        }
                }
        }

        for (u32 k = 0; k < vN(back); k += 2) {
                u32 h = v__(back, k + 1);
                if (ntail[h]++ == 0) {
                        heads[nhead++] = h;
                }
        }

        for (u32 k = 0, off = 0; k < nhead; ++k) {
                tbase[heads[k]] = off;
                off += ntail[heads[k]];
                ntail[heads[k]] = 0;
        }

        for (u32 k = 0; k < vN(back); k += 2) {
                u32 h = v__(back, k + 1);
                tails[tbase[h] + ntail[h]++] = v__(back, k);
        }

        for (u32 k = 0; k < nhead; ++k) {
                u32 h    = heads[k];
                u32 head = 0;
                u32 tail = 0;

                mark[h] = h + 1;
                s->depth[h] += 1;

                for (u32 j = 0; j < ntail[h]; ++j) {
                        u32 t = tails[tbase[h] + j];
                        if (mark[t] != h + 1) {
                                mark[t] = h + 1;
                                s->depth[t] += 1;
                                queue[tail++] = t;
                        }
                }

                while (head < tail) {
                        u32 b = queue[head++];
                        for (u32 j = 0; j < s->npreds[b]; ++j) {
                                u32 p = s->preds[b][j];
                                if (mark[p] != h + 1 && p > h) {
                                        mark[p] = h + 1;
                                        s->depth[p] += 1;
                                        queue[tail++] = p;
                                }
                        }
                }
        }

        bool *hot = new0(bool, nb + 1);

        for (u32 b = 0; b < nb; ++b) {
                LirBlock const *x = &cfg->blocks[b];

                hot[b] = (b == 0) && x->reachable;

                for (u32 j = 0; !hot[b] && j < s->npreds[b]; ++j) {
                        u32 p = s->preds[b][j];
                        hot[b] = (p < b) && hot[p] && likely(s, p, b);
                }

                s->weight[b] = 1u << (3 * (least(s->depth[b], 6) + hot[b]));
        }
}

static u32
weight_at(Scan const *s, u32 pos)
{
        return s->weight[block_of(s, pos)];
}

static u8
use_flags(Scan const *s, LirInst const *in, u32 pc, u32 j, LirReg r)
{
        if (constrained(s, pc, r, false)) {
                return 0;
        }

        if (j >= in->nargs) {
                return 0;
        }

        switch (in->op) {
        case LIR_CALL:
        case LIR_TAILCALL:
        case LIR_RET:
        case LIR_POLL:
                return 0;

        default:
                return MUST;
        }
}

static u8
def_flags(Scan const *s, LirInst const *in, u32 pc, LirReg r)
{
        if (in->op == LIR_CALL || constrained(s, pc, r, true) || r != in->dst) {
                return DEF;
        }

        return DEF | MUST;
}

typedef struct {
        vec(Span) spans;
        vec(Rec)  recs;
        u32      *ends;
        vec(u32)  touched;
} Live;

static void
span(Scan *s, Live *l, LirReg r, u32 start, u32 end)
{
        Ty *ty = s->ty;

        if (start < end) {
                svP(l->spans, ((Span) { r, start, end }));
        }
}

static void
use(Scan *s, Live *l, LirReg r, u32 pos, u8 flags)
{
        Ty *ty = s->ty;

        if (l->ends[r] == LIR_NONE) {
                l->ends[r] = pos + 1;
                svP(l->touched, r);
        }

        svP(l->recs, ((Rec) { r, pos, s->weight[block_of(s, pos)], flags }));
}

static void
def(Scan *s, Live *l, LirReg r, u32 pos, u8 flags)
{
        Ty *ty  = s->ty;
        u32 end = (l->ends[r] == LIR_NONE) ? pos + 1 : l->ends[r];

        l->ends[r] = LIR_NONE;
        span(s, l, r, pos, end);
        svP(l->recs, ((Rec) { r, pos, s->weight[block_of(s, pos)], flags }));
}

static void
operands(Scan *s, Live *l, LirInst const *in, u32 pc)
{
        LirReg rs[2];

        for (u32 j = 0; j < in->nargs + in->ncall_args; ++j) {
                LirOpnd a = (j < in->nargs) ? in->args[j] : in->call_args[j - in->nargs];
                for (u32 k = 0, n = regs_of(a, rs); k < n; ++k) {
                        u8 f = (a.kind == LO_MEM && !constrained(s, pc, rs[k], false))
                             ? MUST
                             : use_flags(s, in, pc, j, rs[k]);
                        use(s, l, rs[k], LIR_IN(pc), f);
                }
        }

        for (u32 j = 0; j < in->raw.nin; ++j) {
                use(s, l, in->raw.in[j].reg, LIR_IN(pc), 0);
        }
}

static void
build(Scan *s)
{
        Ty           *ty  = s->ty;
        LirCFG const *cfg = s->cfg;
        Live          l   = { .ends = nones(s->nregs + 1) };

        for (u32 b = cfg->nblocks; b-- > 0;) {
                LirBlock const *block = &cfg->blocks[b];

                v0(l.touched);

                for (u32 w = 0; w < cfg->nwords; ++w) {
                        for (u64 bits = block->live_out[w]; bits != 0; bits &= bits - 1) {
                                u32 r = cfg->globals[w * 64 + __builtin_ctzll(bits)];
                                l.ends[r] = LIR_IN(block->end);
                                svP(l.touched, r);
                        }
                }

                for (u32 pc = block->end; pc-- > block->first;) {
                        LirInst const *in = inst(s, pc);

                        if (in->dst != LIR_NONE) {
                                def(s, &l, in->dst, LIR_OUT(pc), def_flags(s, in, pc, in->dst));
                        }

                        for (u32 j = 0; j < in->raw.nout; ++j) {
                                def(s, &l, in->raw.out[j].reg, LIR_OUT(pc), DEF);
                        }

                        operands(s, &l, in, pc);
                }

                for (u32 t = 0; t < vN(l.touched); ++t) {
                        u32 r = v__(l.touched, t);
                        if (l.ends[r] != LIR_NONE) {
                                span(s, &l, r, LIR_IN(block->first), l.ends[r]);
                                l.ends[r] = LIR_NONE;
                        }
                }
        }

        u32 *nr = new0(u32, s->nregs + 1);
        u32 *nu = new0(u32, s->nregs + 1);
        u32 *nd = new0(u32, s->nregs + 1);

        vfor(l.spans, nr[it->reg] += 1);
        vfor(l.recs, nu[it->reg] += 1; nd[it->reg] += (it->flags & DEF) != 0);

        s->sets = new0(Group, s->nregs + 1);

        for (u32 r = 0; r < s->nregs; ++r) {
                Group *x = &s->sets[r];
                x->r    = new(LirRange, nr[r] + 1);
                x->u    = new(Use, nu[r] + 1);
                x->defs = new(u32, nd[r] + 2);

                if (v__(s->L->regs, r).param != LIR_NONE) {
                        x->defs[x->ndefs++] = 0;
                }
        }

        for (u32 k = vN(l.spans); k-- > 0;) {
                Span const *x = v_(l.spans, k);
                Group      *t = &s->sets[x->reg];
                t->r[t->nr++] = (LirRange) { x->start, x->end };
        }

        for (u32 k = vN(l.recs); k-- > 0;) {
                Rec const *x = v_(l.recs, k);
                Group     *t = &s->sets[x->reg];
                t->u[t->nu++] = (Use) { x->pos, x->weight, x->flags };
                if (x->flags & DEF) {
                        t->defs[t->ndefs++] = x->pos;
                }
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                Group *x = &s->sets[r];
                u32    n = 0;

                x->r  = unite(ty, x->r, x->nr, NULL, 0, &n);
                x->nr = n;
                x->u  = weave(ty, x->u, x->nu, NULL, 0, &n);
                x->nu = n;

                info(s, r)->ranges  = x->r;
                info(s, r)->nranges = x->nr;
        }
}

static bool
derived(Lir const *L, bool const *stackish, LirInst const *in)
{
        LirOpnd const    *a = in->args;
        LirRegInfo const *r = vv(L->regs);

        switch (in->op) {
        case LIR_LEA:
                return (a[0].kind == LO_MEM)
                    && stackish[a[0].mem.base]
                    && (a[0].mem.index == LIR_NONE || r[a[0].mem.index].cls != LIR_PTR);

        case LIR_MOV:
                return (a[0].kind == LO_REG) && stackish[a[0].reg];

        case LIR_ADD:
        case LIR_SUB:
                return (a[0].kind == LO_REG)
                    && stackish[a[0].reg]
                    && (
                               (a[1].kind == LO_IMM)
                            || (a[1].kind == LO_REG && r[a[1].reg].cls == LIR_I64)
                       );

        default:
                return false;
        }
}

static void
classify(Scan *s)
{
        Ty        *ty      = s->ty;
        Lir const *L       = s->L;
        bool      *x       = new(bool, s->nregs + 1);
        bool       changed = true;

        for (u32 r = 0; r < s->nregs; ++r) {
                LirRegInfo const *ri = v_(L->regs, r);
                if (ri->pin != LIR_NONE) {
                        x[r] = (ri->pin < 8) && ((L->stack_pins >> ri->pin) & 1);
                } else {
                        x[r] = (ri->cls == LIR_PTR) && (ri->param == LIR_NONE);
                }
        }

        while (changed) {
                changed = false;
                for (u32 pc = 0; pc < s->ninsts; ++pc) {
                        LirInst const *in = inst(s, pc);

                        for (u32 j = 0; j < in->raw.nout; ++j) {
                                u32 r = in->raw.out[j].reg;
                                if (x[r] && v__(L->regs, r).pin == LIR_NONE) {
                                        x[r]    = false;
                                        changed = true;
                                }
                        }

                        if (
                                (in->dst == LIR_NONE)
                             || !x[in->dst]
                             || (v__(L->regs, in->dst).pin != LIR_NONE)
                             || derived(L, x, in)
                        ) {
                                continue;
                        }

                        x[in->dst] = false;
                        changed    = true;
                }
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                info(s, r)->stackish = x[r];
        }
}

static int
copycmp(void const *a, void const *b)
{
        Copy const *x = a;
        Copy const *y = b;

        if (x->weight != y->weight) {
                return (x->weight > y->weight) ? -1 : 1;
        }

        return (x->pc < y->pc) ? -1 : (x->pc != y->pc);
}

static bool
joinable(Scan const *s, LirReg d, LirReg r)
{
        LirRegInfo const *a = v_(s->L->regs, d);
        LirRegInfo const *b = v_(s->L->regs, r);

        return (d != r)
            && (a->cls == b->cls)
            && (info(s, d)->stackish == info(s, r)->stackish);
}

static bool
clashes(Group const *x, Group const *y, u32 skip)
{
        for (u32 k = 0; k < x->ndefs; ++k) {
                if (x->defs[k] != skip && covers(y->r, y->nr, x->defs[k])) {
                        return true;
                }
        }

        return false;
}

static void
coalesce(Scan *s)
{
        Ty  *ty = s->ty;
        u32  n  = 0;

        s->parent = new(u32, s->nregs + 1);

        for (u32 r = 0; r < s->nregs; ++r) {
                s->parent[r] = r;
        }

        Copy *copies = new(Copy, s->ninsts + 1);

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirInst const *in = inst(s, pc);
                if (
                        (in->op == LIR_MOV)
                     && (in->dst != LIR_NONE)
                     && (in->args[0].kind == LO_REG)
                     && joinable(s, in->dst, in->args[0].reg)
                ) {
                        copies[n++] = (Copy) { pc, weight_at(s, LIR_IN(pc)) };
                }
        }

        qsort(copies, n, sizeof *copies, copycmp);

        for (u32 k = 0; k < n; ++k) {
                LirInst const *in = inst(s, copies[k].pc);
                u32            x  = find(s, in->dst);
                u32            y  = find(s, in->args[0].reg);

                if (x == y) {
                        continue;
                }

                Group *a = &s->sets[x];
                Group *b = &s->sets[y];

                if (clashes(a, b, LIR_OUT(copies[k].pc)) || clashes(b, a, LIR_NONE)) {
                        continue;
                }

                u32 nr;
                u32 nu;
                u32 nd;

                a->r     = unite(ty, a->r, a->nr, b->r, b->nr, &nr);
                a->u     = weave(ty, a->u, a->nu, b->u, b->nu, &nu);
                a->defs  = merge_defs(ty, a->defs, a->ndefs, b->defs, b->ndefs, &nd);
                a->nr    = nr;
                a->nu    = nu;
                a->ndefs = nd;

                s->parent[y] = x;
        }
}

static bool
rematerializable(LirInst const *in)
{
        switch (in->op) {
        case LIR_LI:
        case LIR_FLI:
                return true;

        case LIR_MOV:
                return (in->args[0].kind == LO_CONST) || (in->args[0].kind == LO_REFCONST);

        default:
                return false;
        }
}

static bool
same_load(Scan *s, LirInst const *a, LirInst const *b)
{
        LirMem x = a->args[0].mem;
        LirMem y = b->args[0].mem;

        return (a->op == b->op)
            && (x.index == LIR_NONE)
            && (y.index == LIR_NONE)
            && (x.disp == y.disp)
            && (find(s, x.base) == find(s, y.base));
}

static bool
spans(Group const *outer, Group const *inner)
{
        u32 j = 0;

        for (u32 k = 0; k < inner->nr; ++k) {
                LirRange x = inner->r[k];

                while (j < outer->nr && outer->r[j].end <= x.start) {
                        j += 1;
                }

                if (j == outer->nr || outer->r[j].start > x.start || outer->r[j].end < x.end) {
                        return false;
                }
        }

        return true;
}

static bool
refreshable(Scan *s, u32 r)
{
        Group const   *x   = &s->sets[r];
        LirInst const *def = NULL;

        for (u32 k = 0; k < x->ndefs; ++k) {
                LirInst const *in = inst(s, x->defs[k] / 4);

                if (in->op == LIR_MOV && in->args[0].kind == LO_REG && find(s, in->args[0].reg) == r) {
                        continue;
                }

                if (
                        (LirOps[in->op].form != LF_LD)
                     || !(in->flags & LIR_REFRESH)
                     || (def != NULL && !same_load(s, def, in))
                ) {
                        return false;
                }

                if (def == NULL) {
                        def = in;
                        s->remat[r] = x->defs[k] / 4;
                }
        }

        return def != NULL;
}

static void
refreshes(Scan *s)
{
        Ty *ty = s->ty;

        s->refresh = new0(bool, s->nregs + 1);

        for (u32 r = 0; r < s->nregs; ++r) {
                if (find(s, r) == r && s->remat[r] == LIR_NONE && refreshable(s, r)) {
                        s->refresh[r] = true;
                }
        }

        for (bool changed = true; changed;) {
                changed = false;

                for (u32 r = 0; r < s->nregs; ++r) {
                        if (!s->refresh[r]) {
                                continue;
                        }

                        LirReg b = find(s, inst(s, s->remat[r])->args[0].mem.base);

                        if (s->refresh[b] || spans(&s->sets[b], &s->sets[r])) {
                                continue;
                        }

                        s->refresh[r] = false;
                        s->remat[r]   = LIR_NONE;
                        s->stale      = true;
                        changed       = true;
                }
        }
}

static void
remats(Scan *s)
{
        Ty *ty = s->ty;

        s->remat = nones(s->nregs + 1);

        for (u32 r = 0; r < s->nregs; ++r) {
                if (find(s, r) != r) {
                        continue;
                }

                Group const *x    = &s->sets[r];
                u32          def  = LIR_NONE;
                u32          ndef = 0;

                for (u32 k = 0; k < x->ndefs; ++k) {
                        u32            pc = x->defs[k] / 4;
                        LirInst const *in = inst(s, pc);
                        if (
                                (in->op == LIR_MOV)
                             && (in->args[0].kind == LO_REG)
                             && (find(s, in->args[0].reg) == r)
                        ) {
                                continue;
                        }
                        def   = pc;
                        ndef += 1;
                }

                if (ndef == 1 && rematerializable(inst(s, def))) {
                        s->remat[r] = def;
                }
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                if (v__(s->L->regs, r).param != LIR_NONE) {
                        s->remat[find(s, r)] = LIR_NONE;
                }
        }

        refreshes(s);
}

static void
fix(Scan *s, bool f, u8 phys, u32 pos, LirReg owner)
{
        Ty *ty = s->ty;

        if (phys < LIR_MAX_PHYS) {
                svP(s->fixed[f][phys], ((Fix) { pos, (owner == LIR_NONE) ? LIR_NONE : find(s, owner) }));
        }
}

static int
fixcmp(void const *a, void const *b)
{
        Fix const *x = a;
        Fix const *y = b;

        return (x->pos < y->pos) ? -1 : (x->pos != y->pos);
}

static void
blocks(Scan *s)
{
        Ty *ty = s->ty;

        s->calls = new(u32, s->ninsts + 1);

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirInst const *in = inst(s, pc);

                if (iscall(in->op)) {
                        s->calls[s->ncalls++] = LIR_TMP(pc);
                }

                for (u64 m = in->raw.gpr_clobber; m != 0; m &= m - 1) {
                        fix(s, false, __builtin_ctzll(m), LIR_TMP(pc), LIR_NONE);
                }

                for (u64 m = in->raw.fpr_clobber; m != 0; m &= m - 1) {
                        fix(s, true, __builtin_ctzll(m), LIR_TMP(pc), LIR_NONE);
                }

                for (u32 j = 0; j < in->raw.nin; ++j) {
                        LirRawBinding b = in->raw.in[j];
                        fix(s, fpreg(s, b.reg), b.phys, LIR_IN(pc), b.reg);
                }

                for (u32 j = 0; j < in->raw.nout; ++j) {
                        LirRawBinding b = in->raw.out[j];
                        fix(s, fpreg(s, b.reg), b.phys, LIR_OUT(pc), b.reg);
                }
        }

        for (u32 c = 0; c < vN(s->cons); ++c) {
                LirConstraint const *con = v_(s->cons, c);

                if (con->phys == LIR_PHYS_NONE) {
                        continue;
                }

                if (con->reg == LIR_NONE) {
                        fix(s, con->fpr, con->phys, LIR_TMP(con->op), LIR_NONE);
                } else {
                        u32 pos = con->output ? LIR_OUT(con->op) : LIR_IN(con->op);
                        fix(s, fpreg(s, con->reg), con->phys, pos, con->reg);
                }
        }

        for (u32 f = 0; f < 2; ++f) {
                for (u32 p = 0; p < LIR_MAX_PHYS; ++p) {
                        if (vN(s->fixed[f][p]) > 1) {
                                qsort(vv(s->fixed[f][p]), vN(s->fixed[f][p]), sizeof (Fix), fixcmp);
                        }
                }
        }
}

static void
hint_rel(Scan *s, LirReg a, LirReg b, u32 pos, u32 w)
{
        u32 x = find(s, a);
        u32 y = find(s, b);

        if (x != y && fpreg(s, x) == fpreg(s, y) && (s->vhint[x] == LIR_NONE || w > s->hweight[x])) {
                s->vhint[x]   = y;
                s->hpos[x]    = pos;
                s->hweight[x] = w;
        }
}

static void
hint_phys(Scan *s, LirReg r, u8 phys)
{
        u32 x = find(s, r);

        if (s->phint[x] == LIR_PHYS_NONE && phys < LIR_MAX_PHYS) {
                s->phint[x] = phys;
        }
}

static bool
dies(Scan *s, LirReg r, u32 pc)
{
        Group const *x = &s->sets[find(s, r)];
        return !covers(x->r, x->nr, LIR_OUT(pc));
}

static void
hint_call(Scan *s, LirInst const *in, u32 pc)
{
        u32 next[2] = {0};

        for (u32 p = 0; p < in->ncall_args; ++p) {
                bool    f   = isfloat(lir_type_class(in->sig.params[p]));
                u32     a   = next[f]++;
                LirOpnd arg = in->call_args[p];

                if (
                        (s->target->abi == LIR_ABI_APPLE_ARM64)
                     && in->sig.variadic
                     && (p >= in->sig.nfixed)
                ) {
                        continue;
                }

                if (arg.kind == LO_REG && a < pool(s, f)->nargs && dies(s, arg.reg, pc)) {
                        hint_phys(s, arg.reg, pool(s, f)->args[a]);
                }
        }

        if (in->dst != LIR_NONE) {
                hint_phys(s, in->dst, pool(s, fpreg(s, in->dst))->ret);
        }
}

static bool
two_address(LirForm form)
{
        switch (form) {
        case LF_IBINARY:
        case LF_IUNARY:
        case LF_FBINARY:
        case LF_FUNARY:
        case LF_I2F:
        case LF_F2I:
        case LF_FEXT:
        case LF_FTRUNC:
        case LF_BITCAST:
                return true;

        default:
                return false;
        }
}

static void
hints(Scan *s)
{
        Ty        *ty      = s->ty;
        Lir const *L       = s->L;
        u32        next[2] = {0};

        s->phint   = memset(new(u8, s->nregs + 1), LIR_PHYS_NONE, s->nregs + 1);
        s->vhint   = nones(s->nregs + 1);
        s->hpos    = nones(s->nregs + 1);
        s->hweight = new0(u32, s->nregs + 1);

        for (u32 c = 0; c < vN(s->cons); ++c) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->reg != LIR_NONE) {
                        hint_phys(s, con->reg, con->phys);
                }
        }

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirInst const *in = inst(s, pc);
                for (u32 j = 0; j < in->raw.nin; ++j) {
                        hint_phys(s, in->raw.in[j].reg, in->raw.in[j].phys);
                }
                for (u32 j = 0; j < in->raw.nout; ++j) {
                        hint_phys(s, in->raw.out[j].reg, in->raw.out[j].phys);
                }
        }

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirInst const *in = inst(s, pc);
                u32            w  = weight_at(s, LIR_IN(pc));

                if (in->op == LIR_RET && in->nargs == 1 && in->args[0].kind == LO_REG) {
                        hint_phys(s, in->args[0].reg, pool(s, fpreg(s, in->args[0].reg))->ret);
                }

                if (iscall(in->op)) {
                        hint_call(s, in, pc);
                }

                if (in->dst == LIR_NONE || in->nargs == 0 || in->args[0].kind != LO_REG) {
                        continue;
                }

                LirReg a = in->args[0].reg;

                if (in->op == LIR_MOV) {
                        hint_rel(s, in->dst, a, LIR_IN(pc), 2 * w);
                        hint_rel(s, a, in->dst, LIR_OUT(pc), 2 * w);
                } else if (two_address(LirOps[in->op].form) && dies(s, a, pc)) {
                        hint_rel(s, in->dst, a, LIR_IN(pc), w);
                        hint_rel(s, a, in->dst, LIR_OUT(pc), w);
                }
        }

        for (u32 p = 0; p < L->sig.nparams; ++p) {
                bool f = isfloat(lir_type_class(L->sig.params[p]));
                u32  a = next[f]++;

                for (u32 r = 0; r < s->nregs && a < pool(s, f)->nargs; ++r) {
                        if (v__(L->regs, r).param == p) {
                                hint_phys(s, r, pool(s, f)->args[a]);
                        }
                }
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                u32 p = v__(L->regs, r).pin;
                if (p < s->target->npins) {
                        hint_phys(s, r, s->target->pins[p]);
                }
        }
}

static bool
earlier(Scan const *s, u32 a, u32 b)
{
        u32 x = ivstart(iv(s, a));
        u32 y = ivstart(iv(s, b));

        return (x < y) || (x == y && a < b);
}

static void
push(Scan *s, u32 c)
{
        Ty  *ty = s->ty;
        u32 *h;
        u32  k;

        svP(s->heap, c);

        h = vv(s->heap);
        k = vN(s->heap) - 1;

        while (k > 0 && earlier(s, h[k], h[(k - 1) / 2])) {
                SWAP(u32, h[k], h[(k - 1) / 2]);
                k = (k - 1) / 2;
        }
}

static u32
pop(Scan *s)
{
        u32 *h   = vv(s->heap);
        u32  top = h[0];
        u32  n   = --vN(s->heap);
        u32  k   = 0;

        h[0] = h[n];

        for (;;) {
                u32 l = 2 * k + 1;
                u32 m = k;

                if (l < n && earlier(s, h[l], h[m])) {
                        m = l;
                }

                if (l + 1 < n && earlier(s, h[l + 1], h[m])) {
                        m = l + 1;
                }

                if (m == k) {
                        break;
                }

                SWAP(u32, h[k], h[m]);
                k = m;
        }

        return top;
}

static u32
firstmust(Iv const *c, u32 from)
{
        for (u32 k = 0; k < c->nu; ++k) {
                if (c->u[k].pos >= from && (c->u[k].flags & MUST)) {
                        return c->u[k].pos;
                }
        }

        return LIR_NONE;
}

static u32
lastmust(Iv const *c, u32 before)
{
        u32 last = LIR_NONE;

        for (u32 k = 0; k < c->nu && c->u[k].pos < before; ++k) {
                if (c->u[k].flags & MUST) {
                        last = c->u[k].pos;
                }
        }

        return last;
}

static u64
usecost(Iv const *c, u32 from, u32 to)
{
        u64 cost = 0;

        for (u32 k = 0; k < c->nu; ++k) {
                if (c->u[k].pos >= from && c->u[k].pos < to && (c->u[k].flags & MUST)) {
                        cost += c->u[k].weight;
                }
        }

        return cost;
}

static u32
firstcall(Scan const *s, Iv const *c)
{
        for (u32 k = 0; k < c->nr; ++k) {
                u32 i = lower(s->calls, s->ncalls, c->r[k].start);
                if (i < s->ncalls && s->calls[i] < c->r[k].end) {
                        return s->calls[i];
                }
        }

        return LIR_NONE;
}

static u64
callcost(Scan const *s, Iv const *c, u32 from, u32 to)
{
        u64 cost = 0;

        for (u32 k = 0; k < c->nr; ++k) {
                for (
                        u32 i = lower(s->calls, s->ncalls, most(c->r[k].start, from));
                        i < s->ncalls && s->calls[i] < least(c->r[k].end, to);
                        ++i
                ) {
                        cost += 2 * (u64)weight_at(s, s->calls[i]);
                }
        }

        return cost;
}

static u64
displace(Scan const *s, Iv const *c, u32 from, u32 to)
{
        u64 calls = callcost(s, c, from, to);
        u64 uses  = usecost(c, from, to);
        u64 cost  = ((calls < uses) ? calls : uses) + weight_at(s, from);

        return (s->remat[c->rep] != LIR_NONE) ? (cost + 1) / 2 : cost;
}

static u32
firstfix(Scan const *s, bool f, u8 p, Iv const *c)
{
        Fixes const    *x  = &s->fixed[f][p];
        u32             lo = 0;
        u32             hi = vN(*x);
        u32             st = ivstart(c);
        u32             en = ivend(c);

        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (v_(*x, mid)->pos < st) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        for (u32 k = lo; k < vN(*x) && v_(*x, k)->pos < en; ++k) {
                Fix const *fx = v_(*x, k);
                if (fx->owner != c->rep && covers(c->r, c->nr, fx->pos)) {
                        return fx->pos;
                }
        }

        return LIR_NONE;
}

static u32
limit(Scan const *s, Iv const *c, bool f, u8 p, u32 call)
{
        u32 lim = firstfix(s, f, p, c);

        if (call != LIR_NONE && !(pool(s, f)->callee_saved & bit(p))) {
                lim = least(lim, call);
        }

        return lim;
}

static u64
bcost(Scan const *s, u32 b)
{
        u32 blk = block_of(s, b);

        if (!starts_block(s, b) || s->npreds[blk] == 0) {
                return s->weight[blk];
        }

        u32 w     = 0;
        u32 first = s->cfg->blocks[blk].first;

        for (u32 j = 0; j < s->npreds[blk]; ++j) {
                u32 p = s->preds[blk][j];
                if (s->cfg->blocks[p].first < first) {
                        w = most(w, s->weight[p]);
                }
        }

        return (w == 0) ? s->weight[blk] : w;
}

static u32
boundary(Scan const *s, u32 lo, u32 hi, bool late)
{
        u32 best = hi;
        u64 cost = bcost(s, hi);

        if (hi / 4 >= s->ninsts) {
                return hi;
        }

        for (
                u32 b = block_of(s, lo + 1);
                b < s->cfg->nblocks && LIR_IN(s->cfg->blocks[b].first) <= hi;
                ++b
        ) {
                u32 at = LIR_IN(s->cfg->blocks[b].first);

                if (at <= lo || at == hi) {
                        continue;
                }

                u64 c = bcost(s, at);

                if (c < cost || (c == cost && !late && at < best)) {
                        best = at;
                        cost = c;
                }
        }

        return best;
}

static u32
split(Scan *s, u32 c, u32 b)
{
        Ty *ty = s->ty;
        Iv *x  = iv(s, c);
        u32 k  = 0;
        u32 m  = 0;

        while (k < x->nr && x->r[k].end <= b) {
                k += 1;
        }

        if (k == x->nr) {
                return LIR_NONE;
        }

        while (m < x->nu && x->u[m].pos < b) {
                m += 1;
        }

        Iv t = {
                .rep   = x->rep,
                .r     = new(LirRange, x->nr - k),
                .nr    = x->nr - k,
                .u     = x->u + m,
                .nu    = x->nu - m,
                .prev  = c,
                .next  = x->next,
                .cut   = b,
                .phys  = LIR_PHYS_NONE,
                .calm  = x->calm
        };

        memcpy(t.r, x->r + k, t.nr * sizeof *t.r);
        t.r[0].start = most(t.r[0].start, b);

        if (x->r[k].start < b) {
                x->r[k].end = b;
                x->nr       = k + 1;
        } else {
                x->nr = k;
        }

        x->nu = m;

        u32 next = x->next;
        u32 at   = vN(s->ivs);

        svP(s->ivs, t);

        if (next != LIR_NONE) {
                iv(s, next)->prev = at;
        }

        iv(s, c)->next = at;

        return at;
}

static void
drop(Ids *list, u32 c)
{
        for (u32 k = 0; k < vN(*list); ++k) {
                if (v__(*list, k) == c) {
                        v__(*list, k) = v__(*list, vN(*list) - 1);
                        vN(*list) -= 1;
                        return;
                }
        }
}

static u8
hint(Scan *s, u32 c)
{
        Iv const *x = iv(s, c);

        for (u32 p = x->prev; p != LIR_NONE; p = iv(s, p)->prev) {
                if (iv(s, p)->phys != LIR_PHYS_NONE) {
                        return iv(s, p)->phys;
                }
        }

        u32 partner = s->vhint[x->rep];

        if (partner != LIR_NONE) {
                kids (k, s, partner) {
                        Iv const *y = iv(s, k);
                        if (y->nr != 0 && y->phys != LIR_PHYS_NONE && covers(y->r, y->nr, s->hpos[x->rep])) {
                                return y->phys;
                        }
                }
        }

        return s->phint[x->rep];
}

static void
assign(Scan *s, u32 c, u8 p)
{
        Iv *x = iv(s, c);

        x->phys = p;
        s->used[ivbank(s, x)] |= bit(p);
}

static void
free_until(Scan *s, u32 c, u32 until[LIR_MAX_PHYS], u32 call)
{
        Iv const *cur   = iv(s, c);
        bool      f     = ivbank(s, cur);
        u64       avail = pool(s, f)->available;

        for (u32 p = 0; p < LIR_MAX_PHYS; ++p) {
                until[p] = (avail & bit(p)) ? LIR_NONE : 0;
        }

        vfor(s->active, {
                Iv const *a = iv(s, *it);
                if (ivbank(s, a) == f) {
                        until[a->phys] = 0;
                }
        });

        vfor(s->inactive, {
                Iv const *a = iv(s, *it);
                if (ivbank(s, a) == f && until[a->phys] != 0) {
                        until[a->phys] = least(until[a->phys], meet(a->r, a->nr, cur->r, cur->nr));
                }
        });

        u64 clobbered = (call == LIR_NONE) ? 0 : (avail & ~pool(s, f)->callee_saved);

        for (u64 m = avail; m != 0; m &= m - 1) {
                u32 p = __builtin_ctzll(m);

                if (until[p] == 0) {
                        continue;
                }

                if ((clobbered >> p) & 1) {
                        until[p] = least(until[p], call);
                }

                if (vN(s->fixed[f][p]) != 0) {
                        until[p] = least(until[p], firstfix(s, f, p, cur));
                }
        }
}

static u32
rank(Scan const *s, bool f, u8 p, u8 h, bool crossing)
{
        bool saved = (pool(s, f)->callee_saved & bit(p)) != 0;

        if (p == h) {
                return BEST_HINT;
        }

        if (!saved) {
                return crossing ? BEST_OTHER : BEST_FREE;
        }

        return (s->used[f] & bit(p)) ? BEST_SAVED : BEST_OTHER;
}

static bool
whole(Scan *s, u32 c, u32 until[LIR_MAX_PHYS], u32 call)
{
        Iv const *cur  = iv(s, c);
        bool      f    = ivbank(s, cur);
        u32       end  = ivend(cur);
        u8        h    = hint(s, c);
        u8        best = LIR_PHYS_NONE;
        u32       rk   = UINT32_MAX;

        for (u8 p = 0; p < LIR_MAX_PHYS; ++p) {
                if (until[p] == 0 || until[p] < end) {
                        continue;
                }

                u32 r = rank(s, f, p, h, call != LIR_NONE);

                if (r < rk) {
                        rk   = r;
                        best = p;
                }
        }

        if (best == LIR_PHYS_NONE) {
                return false;
        }

        assign(s, c, best);

        return true;
}

static bool
evictable_active(Iv const *a, u32 ws)
{
        u32 m = firstmust(a, floor4(ws));

        return (m == LIR_NONE) || (floor4(m) > ws);
}

static u32
evict_inactive_at(Scan const *s, Iv const *a, u32 ws, u32 x)
{
        u32 lo = lastmust(a, x);
        u32 hi = floor4(x);
        u32 at = (ws + 3) & ~(u32)3;

        lo = (lo == LIR_NONE) ? ivstart(a) : most(lo, ivstart(a));

        if (at > lo + 1) {
                lo = at - 1;
        }

        return (hi > lo) ? boundary(s, lo, hi, true) : LIR_NONE;
}

static u64
evictcost(Scan *s, u32 c, u8 p, u32 we)
{
        Iv const *cur = iv(s, c);
        bool      f   = ivbank(s, cur);
        u32       ws  = ivstart(cur);
        u64       sum = 0;

        for (u32 k = 0; k < vN(s->active); ++k) {
                Iv const *a = iv(s, v__(s->active, k));

                if (ivbank(s, a) != f || a->phys != p) {
                        continue;
                }

                if (!evictable_active(a, ws)) {
                        return Never;
                }

                sum += displace(s, a, ws, least(we, ivend(a)));
        }

        for (u32 k = 0; k < vN(s->inactive); ++k) {
                Iv const *a = iv(s, v__(s->inactive, k));

                if (ivbank(s, a) != f || a->phys != p) {
                        continue;
                }

                u32 x = meet(a->r, a->nr, cur->r, cur->nr);

                if (x == LIR_NONE || x >= we) {
                        continue;
                }

                if (evict_inactive_at(s, a, ws, x) == LIR_NONE) {
                        return Never;
                }

                sum += displace(s, a, x, least(we, ivend(a)));
        }

        return sum;
}

static void
spill_head(Scan *s, u32 c, u32 from)
{
        Iv  *x     = iv(s, c);
        u32  m     = firstmust(x, from);
        bool early = x->clobbered && !x->calm;

        x->phys  = LIR_PHYS_NONE;
        x->stack = true;

        if (m == LIR_NONE) {
                return;
        }

        u32 b = early ? least(LIR_IN(s->cfg->blocks[block_of(s, from)].end), floor4(m))
                      : boundary(s, from, floor4(m), true);
        u32 t = split(s, c, b);

        if (t != LIR_NONE) {
                iv(s, t)->resume = early;
                iv(s, t)->calm   = iv(s, c)->calm && (b < floor4(m));
                push(s, t);
        }
}

static void
trace_evict(Scan const *s, u32 c, u8 p, u32 we)
{
        Iv const *cur = iv(s, c);
        bool      f   = ivbank(s, cur);
        u32       ws  = ivstart(cur);

        fprintf(stderr, "ra:   r%u evicts %c%u over [%u.%u,%u.%u):", cur->rep, f ? 'f' : 'g', p, ws / 4, ws % 4, we / 4, we % 4);

        vfor(s->active, {
                if (ivbank(s, iv(s, *it)) == f && iv(s, *it)->phys == p) {
                        fprintf(stderr, " r%u", iv(s, *it)->rep);
                }
        });

        vfor(s->inactive, {
                if (ivbank(s, iv(s, *it)) == f && iv(s, *it)->phys == p) {
                        fprintf(stderr, " (r%u)", iv(s, *it)->rep);
                }
        });

        fputc('\n', stderr);
}

static void
evict(Scan *s, u32 c, u8 p, u32 we)
{
        Iv const *cur = iv(s, c);
        bool      f   = ivbank(s, cur);
        u32       ws  = ivstart(cur);
        Ty       *ty  = s->ty;
        Ids       hit = {0};

        if (s->trace) {
                trace_evict(s, c, p, we);
        }

        vfor(s->active, {
                Iv const *a = iv(s, *it);
                if (ivbank(s, a) == f && a->phys == p) {
                        svP(hit, *it);
                }
        });

        for (u32 k = 0; k < vN(hit); ++k) {
                u32 a  = v__(hit, k);
                u32 b0 = floor4(ws);
                u32 lo = lastmust(iv(s, a), b0);
                u32 st = ivstart(iv(s, a));
                u32 t;

                if (st >= b0) {
                        drop(&s->active, a);
                        iv(s, a)->calm = (s->remat[iv(s, a)->rep] != LIR_NONE);
                        spill_head(s, a, ws);
                        continue;
                }

                lo = (lo == LIR_NONE) ? st : most(lo, st);
                t  = split(s, a, boundary(s, lo, b0, true));

                if (t != LIR_NONE) {
                        iv(s, t)->calm = (s->remat[iv(s, t)->rep] != LIR_NONE);
                        spill_head(s, t, ws);
                }
        }

        v0(hit);

        vfor(s->inactive, {
                Iv const *a = iv(s, *it);
                if (ivbank(s, a) == f && a->phys == p) {
                        svP(hit, *it);
                }
        });

        for (u32 k = 0; k < vN(hit); ++k) {
                u32 a = v__(hit, k);
                Iv *y = iv(s, a);
                u32 x = meet(y->r, y->nr, iv(s, c)->r, iv(s, c)->nr);

                if (x == LIR_NONE || x >= we) {
                        continue;
                }

                u32 t = split(s, a, evict_inactive_at(s, y, ws, x));

                if (t != LIR_NONE) {
                        iv(s, t)->calm = (s->remat[iv(s, t)->rep] != LIR_NONE);
                        push(s, t);
                }
        }
}

static void
take(Scan *s, u32 c, u8 p, u32 lim, u32 call)
{
        assign(s, c, p);

        Iv const *cur = iv(s, c);

        if (lim == LIR_NONE || lim >= ivend(cur)) {
                return;
        }

        u32 hi = floor4(lim);
        u32 lo = lastmust(cur, hi);

        lo = (lo == LIR_NONE) ? ivstart(cur) : most(lo, ivstart(cur));

        u32 t = split(s, c, boundary(s, lo, hi, true));

        if (t != LIR_NONE) {
                iv(s, t)->clobbered = (lim == call);
                push(s, t);
        }
}

static bool
partial(Scan *s, u32 c, u32 until[LIR_MAX_PHYS], u32 call)
{
        Iv const *cur = iv(s, c);
        bool      f   = ivbank(s, cur);
        u32       u   = firstmust(cur, ivstart(cur));
        u8        h   = hint(s, c);
        u8        bp  = LIR_PHYS_NONE;

        if (
                cur->resume
             && (h < LIR_MAX_PHYS)
             && (until[h] != 0)
             && (floor4(until[h]) > ivstart(cur))
             && (u == LIR_NONE || floor4(until[h]) <= u)
        ) {
                u32 lim = until[h];
                take(s, c, h, lim, call);
                return true;
        }

        if (u == LIR_NONE) {
                return false;
        }

        for (u8 p = 0; p < LIR_MAX_PHYS; ++p) {
                if (until[p] == 0 || until[p] == LIR_NONE || floor4(until[p]) <= u) {
                        continue;
                }

                if (
                        (bp == LIR_PHYS_NONE)
                     || (until[p] > until[bp])
                     || (
                                (until[p] == until[bp])
                             && (rank(s, f, p, h, call != LIR_NONE) < rank(s, f, bp, h, call != LIR_NONE))
                        )
                ) {
                        bp = p;
                }
        }

        if (bp == LIR_PHYS_NONE) {
                return false;
        }

        take(s, c, bp, until[bp], call);

        return true;
}

static bool
blocked(Scan *s, u32 c, u32 call)
{
        Iv const *cur = iv(s, c);
        bool      f   = ivbank(s, cur);
        u32       st  = ivstart(cur);
        u32       u   = firstmust(cur, st);
        u8        h   = hint(s, c);
        u64       best = Never;
        u8        bp   = LIR_PHYS_NONE;
        u32       blim = LIR_NONE;

        if (u == LIR_NONE || floor4(u) > st) {
                spill_head(s, c, st);
                return true;
        }

        for (u8 p = 0; p < LIR_MAX_PHYS; ++p) {
                if (!(pool(s, f)->available & bit(p))) {
                        continue;
                }

                u32 lim = limit(s, cur, f, p, call);

                if (lim != LIR_NONE && floor4(lim) <= u) {
                        continue;
                }

                u64 cost = evictcost(s, c, p, least(lim, ivend(cur)));

                if (cost < best || (cost == best && cost != Never && p == h)) {
                        best = cost;
                        bp   = p;
                        blim = lim;
                }
        }

        if (bp == LIR_PHYS_NONE || best == Never) {
                return false;
        }

        evict(s, c, bp, least(blim, ivend(cur)));
        take(s, c, bp, blim, call);

        return true;
}

static void
rotate(Scan *s, u32 pos)
{
        Ty *ty   = s->ty;
        u32 keep = 0;

        for (u32 k = 0; k < vN(s->active); ++k) {
                u32       a = v__(s->active, k);
                Iv const *x = iv(s, a);

                if (x->phys == LIR_PHYS_NONE || ivend(x) <= pos) {
                        continue;
                }

                if (covers(x->r, x->nr, pos)) {
                        v__(s->active, keep++) = a;
                } else {
                        svP(s->inactive, a);
                }
        }

        vN(s->active) = keep;
        keep          = 0;

        for (u32 k = 0; k < vN(s->inactive); ++k) {
                u32       a = v__(s->inactive, k);
                Iv const *x = iv(s, a);

                if (x->phys == LIR_PHYS_NONE || ivend(x) <= pos) {
                        continue;
                }

                if (covers(x->r, x->nr, pos)) {
                        svP(s->active, a);
                } else {
                        v__(s->inactive, keep++) = a;
                }
        }

        vN(s->inactive) = keep;
}

static void
trace_place(Scan const *s, u32 c, u32 st, u32 en, char const *how)
{
        Iv const *x = iv(s, c);

        fprintf(
                stderr,
                "ra: r%u [%u.%u,%u.%u) %s -> ",
                x->rep,
                st / 4,
                st % 4,
                en / 4,
                en % 4,
                (how == NULL) ? "failed" : how
        );

        if (x->stack) {
                fprintf(stderr, "stack");
        } else {
                fprintf(stderr, "%c%u", ivbank(s, x) ? 'f' : 'g', x->phys);
        }

        fprintf(stderr, " until %u.%u\n", ivend(x) / 4, ivend(x) % 4);
}

static bool
place(Scan *s, u32 c)
{
        Ty *ty = s->ty;
        u32 until[LIR_MAX_PHYS];
        u32         call = firstcall(s, iv(s, c));
        u32         st   = ivstart(iv(s, c));
        u32         en   = ivend(iv(s, c));
        char const *how  = NULL;

        free_until(s, c, until, call);

        if (whole(s, c, until, call)) {
                how = "whole";
        } else if (partial(s, c, until, call)) {
                how = "partial";
        } else if (blocked(s, c, call)) {
                how = "blocked";
        }

        if (s->trace) {
                trace_place(s, c, st, en, how);
        }

        if (how != NULL && iv(s, c)->phys != LIR_PHYS_NONE) {
                svP(s->active, c);
        }

        return how != NULL;
}

typedef struct {
        u32 iv;
        u64 gain;
} Claim;

static int
claimcmp(void const *a, void const *b)
{
        Claim const *x = a;
        Claim const *y = b;

        if (x->gain != y->gain) {
                return (x->gain > y->gain) ? -1 : 1;
        }

        return (x->iv < y->iv) ? -1 : (x->iv != y->iv);
}

static u64
gain(Scan const *s, Iv const *c)
{
        u64 calls = callcost(s, c, 0, LIR_NONE);
        u64 uses  = 0;

        for (u32 k = 0; k < c->nu; ++k) {
                uses += (c->u[k].flags & MUST) ? c->u[k].weight : c->u[k].weight / 2;
        }

        return (calls < uses) ? calls : uses;
}

static void
reserve(Scan *s)
{
        Ty    *ty     = s->ty;
        Claim *claims = new(Claim, s->nregs + 1);
        u32    n      = 0;

        for (u32 r = 0; r < s->nregs; ++r) {
                Iv const *c = iv(s, r);
                if (
                        (c->nr != 0)
                     && (find(s, r) == r)
                     && (s->remat[r] == LIR_NONE)
                     && (firstcall(s, c) != LIR_NONE)
                ) {
                        claims[n++] = (Claim) { r, gain(s, c) };
                }
        }

        qsort(claims, n, sizeof *claims, claimcmp);

        LirRange *held[2][LIR_MAX_PHYS] = {0};
        u32       nheld[2][LIR_MAX_PHYS] = {0};

        for (u32 k = 0; k < n; ++k) {
                Iv  *c    = iv(s, claims[k].iv);
                bool f    = ivbank(s, c);
                u64  keep = pool(s, f)->callee_saved & pool(s, f)->available;
                u8   h    = s->phint[c->rep];
                u8   best = LIR_PHYS_NONE;

                if (claims[k].gain < 4) {
                        break;
                }

                for (u32 j = 0; j <= LIR_MAX_PHYS && best == LIR_PHYS_NONE; ++j) {
                        u8 p = (j == 0) ? h : (u8)(j - 1);

                        if (
                                (p >= LIR_MAX_PHYS)
                             || !(keep & bit(p))
                             || (firstfix(s, f, p, c) != LIR_NONE)
                             || (meet(held[f][p], nheld[f][p], c->r, c->nr) != LIR_NONE)
                        ) {
                                continue;
                        }

                        best = p;
                }

                if (best == LIR_PHYS_NONE) {
                        continue;
                }

                held[f][best] = unite(ty, held[f][best], nheld[f][best], c->r, c->nr, &nheld[f][best]);
                assign(s, claims[k].iv, best);
                svP(s->inactive, claims[k].iv);

                if (s->trace) {
                        fprintf(stderr, "ra: reserve r%u gain %llu -> %s%u\n", c->rep, (unsigned long long)claims[k].gain, f ? "f" : "r", best);
                }
        }
}

static bool
scan(Scan *s)
{
        Ty *ty = s->ty;

        s->ivs = (typeof (s->ivs)) {0};
        svR(s->ivs, 2 * s->nregs + 16);
        s->ivs.count = s->nregs;

        for (u32 r = 0; r < s->nregs; ++r) {
                Group const *x = &s->sets[r];
                bool       rep = (find(s, r) == r);

                *iv(s, r) = (Iv) {
                        .rep  = r,
                        .r    = rep ? new(LirRange, x->nr + 1) : NULL,
                        .nr   = rep ? x->nr : 0,
                        .u    = x->u,
                        .nu   = rep ? x->nu : 0,
                        .prev = LIR_NONE,
                        .next = LIR_NONE,
                        .cut  = LIR_NONE,
                        .phys = LIR_PHYS_NONE
                };

                if (rep && x->nr != 0) {
                        memcpy(iv(s, r)->r, x->r, x->nr * sizeof *x->r);
                }
        }

        reserve(s);

        for (u32 r = 0; r < s->nregs; ++r) {
                if (iv(s, r)->nr != 0 && iv(s, r)->phys == LIR_PHYS_NONE) {
                        push(s, r);
                }
        }

        while (vN(s->heap) != 0) {
                u32 c = pop(s);

                rotate(s, ivstart(iv(s, c)));

                if (!place(s, c)) {
                        return false;
                }
        }

        return true;
}

static u32
slot(Scan *s)
{
        u32 at = s->alloc->spill_size;
        s->alloc->spill_size += 8;
        return at;
}

static u32
home(Scan *s, LirReg rep)
{
        LirInterval *i = info(s, rep);

        if (i->spill == LIR_NONE) {
                i->spill = slot(s);
        }

        return i->spill;
}

static void
publish_pieces(Scan *s)
{
        Ty *ty = s->ty;

        for (u32 r = 0; r < s->nregs; ++r) {
                LirInterval *i = info(s, r);

                i->rep   = find(s, r);
                i->remat = s->remat[i->rep];

                if (i->rep != r || iv(s, r)->nr == 0) {
                        continue;
                }

                u32  n     = 0;
                bool stack = false;

                kids (k, s, r) {
                        n     += (iv(s, k)->nr != 0);
                        stack  = stack || iv(s, k)->stack;
                }

                if (stack && s->remat[r] == LIR_NONE) {
                        home(s, r);
                }

                i->ranges  = s->sets[r].r;
                i->nranges = s->sets[r].nr;
                i->pieces  = new(LirPiece, n + 1);

                kids (k, s, r) {
                        Iv const *x = iv(s, k);
                        if (x->nr != 0) {
                                i->pieces[i->npieces++] = (LirPiece) {
                                        .start = ivstart(x),
                                        .end   = ivend(x),
                                        .phys  = x->phys
                                };
                        }
                }

                i->phys = i->pieces[0].phys;
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                LirInterval *i = info(s, r);
                if (i->rep != r) {
                        i->spill   = info(s, i->rep)->spill;
                        i->pieces  = info(s, i->rep)->pieces;
                        i->npieces = info(s, i->rep)->npieces;
                        i->phys    = info(s, i->rep)->phys;
                }
        }
}

LirLoc
lir_where(LirAlloc const *alloc, LirReg reg, u32 pos)
{
        LirLoc             none = { LIR_NONE, LIR_NONE, LIR_PHYS_NONE };
        LirInterval const *i;

        if (reg >= alloc->nintervals) {
                return none;
        }

        i = &alloc->intervals[alloc->intervals[reg].rep];

        if (i->npieces == 0) {
                return none;
        }

        u32 lo = 0;
        u32 hi = i->npieces;

        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (i->pieces[mid].start <= pos) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        LirPiece const *p = &i->pieces[(lo == 0) ? 0 : lo - 1];

        if (p->phys != LIR_PHYS_NONE) {
                return (LirLoc) { LIR_NONE, LIR_NONE, p->phys };
        }

        if (i->remat != LIR_NONE) {
                return (LirLoc) { LIR_NONE, i->remat, LIR_PHYS_NONE };
        }

        return (LirLoc) { i->spill, LIR_NONE, LIR_PHYS_NONE };
}

static bool
same(LirLoc a, LirLoc b)
{
        return (a.phys == b.phys) && (a.slot == b.slot) && (a.remat == b.remat);
}

static bool
nowhere(LirLoc l)
{
        return (l.phys == LIR_PHYS_NONE) && (l.slot == LIR_NONE) && (l.remat == LIR_NONE);
}

static void
move(Scan *s, LirMove m)
{
        Ty *ty = s->ty;
        svP(s->moves, m);
}

static void
transfer(Scan *s, LirReg rep, LirLoc from, LirLoc to, u32 op, LirMovePhase phase, u32 edge)
{
        if (
                same(from, to)
             || nowhere(from)
             || nowhere(to)
             || (to.remat != LIR_NONE)
        ) {
                return;
        }

        move(s, (LirMove) {
                .op        = op,
                .kind      = LIR_MOVE_COPY,
                .phase     = phase,
                .from      = rep,
                .to        = rep,
                .from_slot = from.slot,
                .to_slot   = to.slot,
                .remat     = from.remat,
                .edge      = edge,
                .stub      = LIR_NONE,
                .from_phys = from.phys,
                .to_phys   = to.phys,
                .cls       = cls(s, rep)
        });
}

static LirLoc
where(Scan const *s, LirReg r, u32 pos)
{
        return lir_where(s->alloc, r, pos);
}

static void
splits(Scan *s)
{
        for (u32 r = 0; r < s->nregs; ++r) {
                if (find(s, r) != r) {
                        continue;
                }

                kids (k, s, r) {
                        Iv const *n = iv(s, k);
                        Iv const *p = (n->prev == LIR_NONE) ? NULL : iv(s, n->prev);

                        if (
                                (p == NULL)
                             || (n->nr == 0)
                             || (ivstart(n) != n->cut)
                             || (n->cut % 4 != 0)
                             || starts_block(s, n->cut)
                        ) {
                                continue;
                        }

                        transfer(s, r, where(s, r, n->cut - 1), where(s, r, n->cut), n->cut / 4, LIR_MOVE_BEFORE, LIR_NONE);
                }
        }
}

static u32
pred_edges(Scan const *s, u32 b)
{
        return s->npreds[b];
}

static void
edge(Scan *s, u32 pb, u32 sb, bool taken, u32 *stamp, u32 id, u32 *nstub)
{
        LirCFG const   *cfg = s->cfg;
        LirBlock const *P   = &cfg->blocks[pb];
        LirBlock const *S   = &cfg->blocks[sb];
        u32             op  = P->end - 1;
        LirInst const  *in  = inst(s, op);
        u32             at  = vN(s->moves);
        LirMovePhase    ph;
        u32             key;

        if (!taken || in->op == LIR_JMP) {
                ph  = LIR_MOVE_EDGE_OUT;
                key = op;
        } else if (pred_edges(s, sb) == 1) {
                ph  = LIR_MOVE_EDGE_IN;
                key = S->first;
        } else {
                ph  = LIR_MOVE_STUB;
                key = op;
        }

        for (u32 w = 0; w < cfg->nwords; ++w) {
                for (u64 bits = S->live_in[w]; bits != 0; bits &= bits - 1) {
                        u32 r = find(s, cfg->globals[w * 64 + __builtin_ctzll(bits)]);

                        if (stamp[r] == id) {
                                continue;
                        }

                        stamp[r] = id;

                        transfer(
                                s,
                                r,
                                where(s, r, LIR_IN(P->end) - 1),
                                where(s, r, LIR_IN(S->first)),
                                key,
                                ph,
                                S->first
                        );
                }
        }

        if (ph == LIR_MOVE_STUB && vN(s->moves) != at) {
                for (u32 k = at; k < vN(s->moves); ++k) {
                        v_(s->moves, k)->stub = *nstub;
                }
                *nstub += 1;
        }
}

static void
resolve(Scan *s)
{
        Ty           *ty    = s->ty;
        LirCFG const *cfg   = s->cfg;
        u32          *stamp = new0(u32, s->nregs + 1);
        u32          *seen  = new0(u32, cfg->nblocks + 1);
        u32           nstub = 0;
        u32           id    = 0;

        for (u32 pb = 0; pb < cfg->nblocks; ++pb) {
                LirBlock const *P = &cfg->blocks[pb];

                if (!P->reachable || P->first == P->end) {
                        continue;
                }

                LirInst const *in = inst(s, P->end - 1);
                u32            nt = 0;

                if (isbranch(in)) {
                        nt = (in->op == LIR_SWITCH) ? in->ntargets + 1 : 1;
                }

                for (u32 j = 0; j < nt; ++j) {
                        LirLabel l  = (j == 0) ? in->args[in->nargs - 1].label : in->targets[j - 1];
                        u32      sb = cfg->block_at[v__(s->L->labels, l).pos];

                        if (seen[sb] == pb + 1) {
                                continue;
                        }

                        seen[sb] = pb + 1;
                        edge(s, pb, sb, true, stamp, ++id, &nstub);
                }

                if (falls(in) && P->end < s->ninsts) {
                        edge(s, pb, cfg->block_at[P->end], false, stamp, ++id, &nstub);
                }
        }

        s->alloc->nstubs = nstub;
}

static void
pins(Scan *s)
{
        for (u32 c = 0; c < vN(s->cons); ++c) {
                LirConstraint const *con = v_(s->cons, c);

                if (con->reg == LIR_NONE || con->phys == LIR_PHYS_NONE) {
                        continue;
                }

                LirLoc fixed = { LIR_NONE, LIR_NONE, con->phys };
                LirReg r     = find(s, con->reg);

                if (con->output) {
                        transfer(s, r, fixed, where(s, r, LIR_OUT(con->op)), con->op, LIR_MOVE_AFTER, LIR_NONE);
                } else {
                        transfer(s, r, where(s, r, LIR_IN(con->op)), fixed, con->op, LIR_MOVE_PIN, LIR_NONE);
                }
        }

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirRaw const *raw = &inst(s, pc)->raw;

                for (u32 j = 0; j < raw->nin; ++j) {
                        LirReg r     = find(s, raw->in[j].reg);
                        LirLoc fixed = { LIR_NONE, LIR_NONE, raw->in[j].phys };
                        transfer(s, r, where(s, r, LIR_IN(pc)), fixed, pc, LIR_MOVE_PIN, LIR_NONE);
                }

                for (u32 j = 0; j < raw->nout; ++j) {
                        LirReg r     = find(s, raw->out[j].reg);
                        LirLoc fixed = { LIR_NONE, LIR_NONE, raw->out[j].phys };
                        transfer(s, r, fixed, where(s, r, LIR_OUT(pc)), pc, LIR_MOVE_AFTER, LIR_NONE);
                }
        }
}

typedef struct {
        u32  nwords;
        u32 *ptrs;
        u32  nptrs;
        u32 *index;
        u64 *in;
        u64 *out;
        bool *seen;
        u32 *at;
        u32 *next;
        bool *dead;
} Prune;

inline static bool
store_move(LirMove const *m)
{
        return (m->kind == LIR_MOVE_COPY)
            && !m->slow
            && (m->to_slot != LIR_NONE)
            && (m->remat == LIR_NONE)
            && (m->from_slot == LIR_NONE);
}

static void
stores(Scan *s, Prune *x, u64 *v, u32 pc, LirMovePhase ph, u32 edge, bool commit)
{
        for (u32 i = x->at[pc]; i != LIR_NONE; i = x->next[i]) {
                LirMove const *m = v_(s->moves, i);
                u32            k = x->index[m->from];

                if (m->phase != ph || (edge != LIR_NONE && m->edge != edge) || !store_move(m) || k == LIR_NONE) {
                        continue;
                }

                if ((v[k / 64] >> (k % 64)) & 1) {
                        if (commit) {
                                x->dead[i] = true;
                        }
                } else {
                        v[k / 64] |= (u64)1 << (k % 64);
                }
        }
}

static void
kill_def(Scan *s, Prune *x, u64 *v, u32 pc, LirReg r)
{
        u32            rep = find(s, r);
        u32            k   = x->index[rep];
        LirInst const *in  = inst(s, pc);

        if (k == LIR_NONE) {
                return;
        }

        if (in->op == LIR_MOV && in->args[0].kind == LO_REG && find(s, in->args[0].reg) == rep) {
                return;
        }

        if (where(s, rep, LIR_OUT(pc)).slot != LIR_NONE) {
                v[k / 64] |= (u64)1 << (k % 64);
        } else {
                v[k / 64] &= ~((u64)1 << (k % 64));
        }
}

static void
kill_moved(Scan *s, Prune *x, u64 *v, u32 pc)
{
        for (u32 j = 0; j < x->nptrs; ++j) {
                u32 r = x->ptrs[j];
                u32 k = x->index[r];
                if (where(s, r, LIR_OUT(pc)).slot == LIR_NONE) {
                        v[k / 64] &= ~((u64)1 << (k % 64));
                }
        }
}

static void
prune_block(Scan *s, Prune *x, u32 b, u64 *v, bool commit)
{
        LirBlock const *B = &s->cfg->blocks[b];

        for (u32 pc = B->first; pc < B->end; ++pc) {
                LirInst const *in = inst(s, pc);

                stores(s, x, v, pc, LIR_MOVE_BEFORE, LIR_NONE, commit);

                if (iscall(in->op) || in->op == LIR_POLL) {
                        kill_moved(s, x, v, pc);
                }

                if (in->dst != LIR_NONE) {
                        kill_def(s, x, v, pc, in->dst);
                }

                for (u32 j = 0; j < in->raw.nout; ++j) {
                        kill_def(s, x, v, pc, in->raw.out[j].reg);
                }
        }
}

static void
prune_edge(Scan *s, Prune *x, u32 pb, u32 sb, u64 *v, bool taken, bool commit)
{
        LirBlock const *P  = &s->cfg->blocks[pb];
        LirBlock const *S  = &s->cfg->blocks[sb];
        u32             op = P->end - 1;

        if (!taken || inst(s, op)->op == LIR_JMP) {
                stores(s, x, v, op, LIR_MOVE_EDGE_OUT, S->first, commit);
        } else {
                stores(s, x, v, op, LIR_MOVE_STUB, S->first, commit);
                stores(s, x, v, S->first, LIR_MOVE_EDGE_IN, S->first, commit);
        }
}

static bool
prune_flow(Scan *s, Prune *x, u32 pb, u64 *tmp, bool commit, u32 *work, u32 *nwork, bool *queued)
{
        LirCFG const   *cfg = s->cfg;
        LirBlock const *P   = &cfg->blocks[pb];
        LirInst const  *in  = inst(s, P->end - 1);
        u32             nt  = isbranch(in) ? ((in->op == LIR_SWITCH) ? in->ntargets + 1 : 1) : 0;
        u64            *out = &x->out[(usize)pb * x->nwords];

        for (u32 j = 0; j <= nt; ++j) {
                bool taken = (j < nt);
                u32  sb;

                if (taken) {
                        LirLabel l = (j == 0) ? in->args[in->nargs - 1].label : in->targets[j - 1];
                        sb = cfg->block_at[v__(s->L->labels, l).pos];
                } else if (falls(in) && P->end < s->ninsts) {
                        sb = cfg->block_at[P->end];
                } else {
                        continue;
                }

                memcpy(tmp, out, x->nwords * sizeof *tmp);
                prune_edge(s, x, pb, sb, tmp, taken, commit);

                if (commit) {
                        continue;
                }

                u64 *in_s    = &x->in[(usize)sb * x->nwords];
                bool changed = !x->seen[sb];

                for (u32 w = 0; w < x->nwords; ++w) {
                        u64 nv = x->seen[sb] ? (in_s[w] & tmp[w]) : tmp[w];
                        changed = changed || (nv != in_s[w]);
                        in_s[w] = nv;
                }

                x->seen[sb] = true;

                if (changed && !queued[sb]) {
                        queued[sb] = true;
                        work[(*nwork)++] = sb;
                }
        }

        return true;
}

static void
prune(Scan *s)
{
        Ty           *ty  = s->ty;
        LirCFG const *cfg = s->cfg;
        u32           nb  = cfg->nblocks;
        u32           m   = 0;
        Prune         x   = { .index = nones(s->nregs + 1) };

        for (u32 r = 0; r < s->nregs; ++r) {
                if (find(s, r) == r && info(s, r)->spill != LIR_NONE && s->remat[r] == LIR_NONE) {
                        x.index[r] = m++;
                }
        }

        if (m == 0 || vN(s->moves) == 0) {
                return;
        }

        x.ptrs = new(u32, m + 1);

        for (u32 r = 0; r < s->nregs; ++r) {
                if (x.index[r] != LIR_NONE && cls(s, r) == LIR_PTR) {
                        x.ptrs[x.nptrs++] = r;
                }
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                x.index[r] = x.index[find(s, r)];
        }

        x.nwords = (m + 63) / 64;
        x.in     = new0(u64, (usize)nb * x.nwords + 1);
        x.out    = new0(u64, (usize)nb * x.nwords + 1);
        x.seen   = new0(bool, nb + 1);
        x.at     = nones(s->ninsts + 1);
        x.next   = nones(vN(s->moves) + 1);
        x.dead   = new0(bool, vN(s->moves) + 1);

        for (u32 i = vN(s->moves); i-- > 0;) {
                u32 op = v_(s->moves, i)->op;
                if (op < s->ninsts) {
                        x.next[i]  = x.at[op];
                        x.at[op]   = i;
                }
        }

        u32  *work   = new(u32, nb + 1);
        bool *queued = new0(bool, nb + 1);
        u64  *tmp    = new(u64, x.nwords + 1);
        u32   nwork  = 0;

        if (nb != 0 && cfg->blocks[0].reachable) {
                x.seen[0]    = true;
                queued[0]    = true;
                work[nwork++] = 0;
        }

        while (nwork != 0) {
                u32 b = work[--nwork];

                queued[b] = false;

                if (cfg->blocks[b].first == cfg->blocks[b].end) {
                        continue;
                }

                u64 *out = &x.out[(usize)b * x.nwords];

                memcpy(out, &x.in[(usize)b * x.nwords], x.nwords * sizeof *out);
                prune_block(s, &x, b, out, false);
                prune_flow(s, &x, b, tmp, false, work, &nwork, queued);
        }

        for (u32 b = 0; b < nb; ++b) {
                if (!x.seen[b] || cfg->blocks[b].first == cfg->blocks[b].end) {
                        continue;
                }

                u64 *v = &x.out[(usize)b * x.nwords];

                memcpy(v, &x.in[(usize)b * x.nwords], x.nwords * sizeof *v);
                prune_block(s, &x, b, v, true);
                prune_flow(s, &x, b, tmp, true, work, &nwork, queued);
        }

        u32 keep = 0;

        for (u32 i = 0; i < vN(s->moves); ++i) {
                if (!x.dead[i]) {
                        *v_(s->moves, keep++) = *v_(s->moves, i);
                }
        }

        vN(s->moves) = keep;
}

static bool
live_across(Scan const *s, LirReg rep, u32 pc)
{
        LirInterval const *i = info(s, rep);
        LirInst const     *in = inst(s, pc);

        if (in->dst != LIR_NONE && info(s, in->dst)->rep == rep) {
                return false;
        }

        for (u32 o = 0; o < in->raw.nout; ++o) {
                if (info(s, in->raw.out[o].reg)->rep == rep) {
                        return false;
                }
        }

        return covers(i->ranges, i->nranges, LIR_IN(pc))
            && covers(i->ranges, i->nranges, LIR_OUT(pc));
}

static void
root(Scan *s, LirReg r, u32 pc, bool slow)
{
        LirInterval *i   = info(s, r);
        LirLoc       loc = where(s, r, LIR_IN(pc));

        if (i->root_slot == LIR_NONE) {
                i->root_slot = s->alloc->nvslots++;
        }

        move(s, (LirMove) {
                .op        = pc,
                .kind      = LIR_MOVE_ROOT,
                .phase     = LIR_MOVE_BEFORE,
                .from      = r,
                .to        = LIR_NONE,
                .cls       = LIR_REF,
                .from_slot = loc.slot,
                .from_phys = loc.phys,
                .remat     = loc.remat,
                .edge      = LIR_NONE,
                .stub      = LIR_NONE,
                .to_slot   = i->root_slot,
                .to_phys   = LIR_PHYS_NONE,
                .slow      = slow
        });
}

static void
refresh_after(Scan *s, LirReg r, u32 pc, bool slow)
{
        LirLoc in  = where(s, r, LIR_IN(pc));
        LirLoc out = where(s, r, LIR_OUT(pc));
        LirLoc re  = { LIR_NONE, s->remat[r], LIR_PHYS_NONE };

        if (in.phys == LIR_PHYS_NONE || !same(in, out)) {
                return;
        }

        transfer(s, r, re, out, pc, LIR_MOVE_AFTER, LIR_NONE);
        v_(s->moves, vN(s->moves) - 1)->slow = slow;
}

static void
poll_save(Scan *s, LirReg r, u32 pc)
{
        LirLoc loc = where(s, r, LIR_IN(pc));
        bool   f   = fpreg(s, r);

        if (s->refresh[r]) {
                refresh_after(s, r, pc, true);
                return;
        }

        if (loc.phys == LIR_PHYS_NONE || (pool(s, f)->callee_saved & bit(loc.phys))) {
                return;
        }

        if (s->remat[r] != LIR_NONE) {
                LirLoc re = { LIR_NONE, s->remat[r], LIR_PHYS_NONE };
                transfer(s, r, re, loc, pc, LIR_MOVE_AFTER, LIR_NONE);
                v_(s->moves, vN(s->moves) - 1)->slow = true;
                return;
        }

        LirLoc mem = { home(s, r), LIR_NONE, LIR_PHYS_NONE };

        transfer(s, r, loc, mem, pc, LIR_MOVE_BEFORE, LIR_NONE);
        v_(s->moves, vN(s->moves) - 1)->slow = true;
        transfer(s, r, mem, loc, pc, LIR_MOVE_AFTER, LIR_NONE);
        v_(s->moves, vN(s->moves) - 1)->slow = true;
}

static void
safepoints(Scan *s)
{
        Ty  *ty = s->ty;
        u32 *at = new(u32, s->ninsts + 1);
        u32  n  = 0;

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirInst const *in = inst(s, pc);
                if (iscall(in->op) || may_gc(in)) {
                        at[n++] = pc;
                }
        }

        if (n == 0) {
                return;
        }

        for (u32 r = 0; r < s->nregs; ++r) {
                LirInterval *i = info(s, r);

                if (find(s, r) != r || i->nranges == 0) {
                        continue;
                }

                bool ref = (cls(s, r) == LIR_REF) && (s->remat[r] == LIR_NONE);

                for (u32 k = 0; k < i->nranges; ++k) {
                        LirRange x = i->ranges[k];

                        for (u32 j = lower(at, n, x.start / 4); j < n && LIR_IN(at[j]) < x.end; ++j) {
                                u32            pc   = at[j];
                                LirInst const *in   = inst(s, pc);
                                bool           poll = (in->op == LIR_POLL);
                                bool           call = iscall(in->op) || poll;

                                if (call && live_across(s, r, pc)) {
                                        i->crosses_call = true;
                                        if (poll) {
                                                poll_save(s, r, pc);
                                        } else if (s->refresh[r]) {
                                                refresh_after(s, r, pc, false);
                                        }
                                }

                                if (ref && may_gc(in) && covers(i->ranges, i->nranges, LIR_IN(pc))) {
                                        root(s, r, pc, poll);
                                }
                        }
                }
        }
}

static void
preserve(Scan *s, bool f, u64 mask)
{
        u64 *saved = f ? &s->alloc->saved_fpr : &s->alloc->saved_gpr;
        *saved |= mask & pool(s, f)->callee_saved;
}

static bool
frame(Scan *s)
{
        LirAlloc *alloc = s->alloc;
        u64       size  = alloc->spill_size;
        u32       align = s->target->stack_align;

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirInst const *in = inst(s, pc);

                if (in->op != LIR_ALLOCA) {
                        continue;
                }

                u32 a = in->args[1].imm;
                size = alignup(size, a);

                if (size > UINT32_MAX) {
                        return false;
                }

                alloc->alloca_offsets[pc] = size;
                size  += in->args[0].imm;
                align  = most(align, a);
        }

        size = alignup(size, align);

        if (size > INT32_MAX) {
                return false;
        }

        alloc->frame_size  = size;
        alloc->frame_align = align;

        preserve(s, false, s->used[0]);
        preserve(s, true, s->used[1]);

        for (u32 c = 0; c < vN(s->cons); ++c) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->phys != LIR_PHYS_NONE) {
                        bool f = (con->reg < s->nregs) ? fpreg(s, con->reg) : con->fpr;
                        preserve(s, f, bit(con->phys));
                }
        }

        for (u32 pc = 0; pc < s->ninsts; ++pc) {
                LirRaw const *raw = &inst(s, pc)->raw;

                preserve(s, false, raw->gpr_clobber);
                preserve(s, true, raw->fpr_clobber);

                for (u32 b = 0; b < raw->nin; ++b) {
                        preserve(s, fpreg(s, raw->in[b].reg), bit(raw->in[b].phys));
                }

                for (u32 b = 0; b < raw->nout; ++b) {
                        preserve(s, fpreg(s, raw->out[b].reg), bit(raw->out[b].phys));
                }
        }

        return true;
}

static bool
target_valid(LirTarget const *t)
{
        return (t != NULL)
            && (t->stack_align != 0)
            && ((t->stack_align & (t->stack_align - 1)) == 0)
            && (t->npins <= LIR_MAX_PINS)
            && ((t->gpr.available >> LIR_MAX_PHYS) == 0)
            && ((t->fpr.available >> LIR_MAX_PHYS) == 0);
}

static bool
constraint_valid(Scan const *s, LirConstraint const *con)
{
        return (con->op < s->ninsts)
            && (con->reg == LIR_NONE || con->reg < s->nregs)
            && (con->phys == LIR_PHYS_NONE || con->phys < LIR_MAX_PHYS)
            && (con->tied == LIR_NONE || con->tied < s->nregs);
}

static void
trace_blocks(Scan const *s)
{
        for (u32 b = 0; b < s->cfg->nblocks; ++b) {
                LirBlock const *x = &s->cfg->blocks[b];
                fprintf(stderr, "ra: block %u [%u,%u) depth %u weight %u\n", b, x->first, x->end, s->depth[b], s->weight[b]);
        }
}

static bool
allocate(Scan *s, LirError *err)
{
        Ty        *ty    = s->ty;
        Lir const *L     = s->L;
        LirAlloc  *alloc = s->alloc;

        alloc->intervals      = new0(LirInterval, s->nregs + 1);
        alloc->alloca_offsets = new0(u32, s->ninsts + 1);
        alloc->nintervals     = s->nregs;
        alloc->nvslots        = L->nvslots;

        for (u32 r = 0; r < s->nregs; ++r) {
                *info(s, r) = (LirInterval) {
                        .reg       = r,
                        .rep       = r,
                        .spill     = LIR_NONE,
                        .remat     = LIR_NONE,
                        .root_slot = LIR_NONE,
                        .phys      = LIR_PHYS_NONE
                };

                u32 p = v__(L->regs, r).pin;

                if (p != LIR_NONE && (p >= s->target->npins || s->target->pins[p] >= LIR_MAX_PHYS)) {
                        return fail(err, LIR_NONE, "pin is unavailable on this target");
                }
        }

        for (u32 c = 0; c < vN(s->cons); ++c) {
                if (!constraint_valid(s, v_(s->cons, c))) {
                        return fail(err, v_(s->cons, c)->op, "invalid fixed-register constraint");
                }
        }

        char const *trace = getenv("TY_RA_TRACE");

        s->index = chain(s);
        s->trace = (trace != NULL) && (L->name != NULL) && (strstr(L->name, trace) != NULL);

        graph(s);

        if (s->trace) {
                trace_blocks(s);
        }

        build(s);
        classify(s);
        coalesce(s);
        remats(s);

        if (s->stale) {
                return fail(err, LIR_NONE, "refreshed load has no live base");
        }

        blocks(s);
        hints(s);

        if (!scan(s)) {
                return fail(err, LIR_NONE, "register allocation failed");
        }

        publish_pieces(s);
        splits(s);
        resolve(s);
        pins(s);
        prune(s);
        safepoints(s);

        if (!frame(s)) {
                return fail(err, LIR_NONE, "native frame is too large");
        }

        alloc->moves        = vv(s->moves);
        alloc->nmoves       = vN(s->moves);
        alloc->constraints  = vv(s->cons);
        alloc->nconstraints = vN(s->cons);

        return true;
}

bool
lir_allocate(
        Ty *ty,
        Lir const *L,
        LirCFG const *cfg,
        LirTarget const *target,
        LirConstraint const *constraints,
        u32 nconstraints,
        LirAlloc *alloc,
        LirError *err
)
{
        Scan s = {
                .ty     = ty,
                .L      = L,
                .cfg    = cfg,
                .target = target,
                .alloc  = alloc,
                .nregs  = vN(L->regs),
                .ninsts = vN(L->insts)
        };

        *alloc = (LirAlloc) {0};

        if (err != NULL) {
                *err = (LirError) {0};
        }

        if (
                !target_valid(target)
             || (vN(L->insts) >= UINT32_MAX / 8)
             || (nconstraints != 0 && constraints == NULL)
        ) {
                return fail(err, LIR_NONE, "invalid allocation target or constraints");
        }

        svR(s.cons, nconstraints + 1);
        s.cons.count = nconstraints;
        memcpy(vv(s.cons), constraints, nconstraints * sizeof *constraints);

        if (!allocate(&s, err)) {
                *alloc = (LirAlloc) {0};
                return false;
        }

        char const *paranoid = getenv("TY_JIT_VALIDATE");

        if (paranoid != NULL && !lir_check_alloc(ty, L, cfg, target, alloc, err)) {
                if (*paranoid == '2') {
                        lir_dump(L, stderr);
                        lir_dump_alloc(L, alloc, stderr);
                }
                *alloc = (LirAlloc) {0};
                return false;
        }

        return true;
}

typedef struct {
        u32  slot;
        u32  remat;
        u8   phys;
        bool fp;
} Loc;

static Loc
src(LirMove const *m)
{
        return (Loc) { m->from_slot, m->remat, m->from_phys, isfloat(m->cls) && !m->from_gpr };
}

static Loc
dst(LirMove const *m)
{
        return (Loc) { m->to_slot, LIR_NONE, m->to_phys, isfloat(m->cls) && !m->to_gpr };
}

static bool
alias(Loc a, Loc b)
{
        if (a.remat != LIR_NONE || b.remat != LIR_NONE) {
                return false;
        }

        if (a.slot != LIR_NONE || b.slot != LIR_NONE) {
                return a.slot == b.slot;
        }

        return (a.phys == b.phys) && (a.fp == b.fp);
}

static bool
vacant(Loc l)
{
        return (l.slot == LIR_NONE) && (l.phys >= LIR_MAX_PHYS) && (l.remat == LIR_NONE);
}

static bool
blocked_move(LirMove const *ms, u32 n, u32 i)
{
        for (u32 j = 0; j < n; ++j) {
                if (j != i && alias(dst(&ms[i]), src(&ms[j]))) {
                        return true;
                }
        }

        return false;
}

static u32
ready(LirMove const *ms, u32 n)
{
        for (u32 i = 0; i < n; ++i) {
                if (!blocked_move(ms, n, i)) {
                        return i;
                }
        }

        return LIR_NONE;
}

bool
lir_parallel_moves(
        Ty *ty,
        LirMove const *moves,
        u32 count,
        LirRegPool const *pool,
        LirMove **out,
        u32 *nout,
        LirError *err
)
{
        bool ok = false;
        u32  n  = 0;

        *out  = NULL;
        *nout = 0;

        if (
                (pool == NULL)
             || (pool->nscratch == 0)
             || (pool->scratch[0] >= LIR_MAX_PHYS)
             || (count != 0 && moves == NULL)
        ) {
                return fail(err, LIR_NONE, "parallel moves need a scratch register");
        }

        LirMove *done  = new(LirMove, 2 * count + 1);
        u32      ndone = 0;

        LirMove *pending = new(LirMove, count + 1);
        LirMove *late    = new(LirMove, count + 1);
        u32      nlate   = 0;
        Loc      tmp     = { LIR_NONE, LIR_NONE, pool->scratch[0], false };

        for (u32 i = 0; i < count; ++i) {
                LirMove m = moves[i];

                if (
                        (m.kind != LIR_MOVE_COPY)
                     || vacant(src(&m))
                     || vacant(dst(&m))
                ) {
                        fail(err, m.op, "invalid parallel move location");
                        goto End;
                }

                if (m.remat != LIR_NONE) {
                        late[nlate++] = m;
                } else if (!alias(src(&m), dst(&m))) {
                        pending[n++] = m;
                }
        }

        for (u32 i = 0; i < n + nlate; ++i) {
                LirMove const *a = (i < n) ? &pending[i] : &late[i - n];
                for (u32 j = 0; j < i; ++j) {
                        LirMove const *b = (j < n) ? &pending[j] : &late[j - n];
                        if (alias(dst(a), dst(b))) {
                                fail(err, a->op, "duplicate parallel move destination");
                                goto End;
                        }
                }
        }

        while (n != 0) {
                u32 i = ready(pending, n);

                if (i != LIR_NONE) {
                        done[ndone++] = pending[i];
                        pending[i] = pending[--n];
                        continue;
                }

                LirMove save = pending[0];
                save.to_slot = LIR_NONE;
                save.to_phys = tmp.phys;
                save.to_gpr  = isfloat(save.cls);

                for (u32 j = 0; j < n; ++j) {
                        if (alias(src(&pending[j]), tmp) || alias(dst(&pending[j]), tmp)) {
                                fail(
                                        err,
                                        save.op,
                                        "parallel move uses its scratch register"
                                );
                                goto End;
                        }
                }

                done[ndone++] = save;

                for (u32 j = 0; j < n; ++j) {
                        if (alias(src(&pending[j]), src(&save))) {
                                pending[j].from_slot = LIR_NONE;
                                pending[j].from_phys = tmp.phys;
                                pending[j].from_gpr  = isfloat(pending[j].cls);
                        }
                }
        }

        for (u32 i = 0; i < nlate; ++i) {
                done[ndone++] = late[i];
        }

        *out  = done;
        *nout = ndone;
        ok    = true;

End:
        return ok;
}

u8
lir_physical(LirAlloc const *alloc, LirReg reg, u32 op, bool output)
{
        for (u32 i = 0; i < alloc->nconstraints; ++i) {
                LirConstraint const *c = &alloc->constraints[i];
                if (
                        (c->op == op)
                     && (c->reg == reg)
                     && (c->output == output)
                     && (c->phys != LIR_PHYS_NONE)
                ) {
                        return c->phys;
                }
        }

        return lir_where(alloc, reg, output ? LIR_OUT(op) : LIR_IN(op)).phys;
}

typedef struct {
        Ty              *ty;
        Lir const       *L;
        LirCFG const    *cfg;
        LirTarget const *target;
        LirAlloc const  *alloc;
        LirError        *err;
        u32              nslots;
        u32              width;
        u32             *at;
        u32             *next;
        u32             *in;
        bool            *seen;
} Check;

inline static u32 *
cell(Check const *k, u32 *st, LirLoc l, bool f)
{
        if (l.slot != LIR_NONE) {
                return &st[2 * LIR_MAX_PHYS + l.slot / 8];
        }

        return &st[(f ? LIR_MAX_PHYS : 0) + l.phys];
}

inline static LirReg
repof(Check const *k, LirReg r)
{
        return k->alloc->intervals[r].rep;
}

static bool
bad(Check *k, u32 pc, char const *what, LirReg r)
{
        LirSpan span = (pc < vN(k->L->insts)) ? v__(k->L->insts, pc).span : (LirSpan) {0};

        return lir_fail(k->err, LE_TARGET, pc, span, "allocation check: %s r%u at pc %u", what, r, pc);
}

static LirLoc
mloc(u32 slot, u8 phys, u32 remat)
{
        return (LirLoc) { slot, remat, phys };
}

static u32
check_pos(LirMove const *m)
{
        switch (m->phase) {
        case LIR_MOVE_AFTER:
                return LIR_OUT(m->op);

        case LIR_MOVE_EDGE_IN:
        case LIR_MOVE_EDGE_OUT:
        case LIR_MOVE_STUB:
                return LIR_IN(m->edge);

        default:
                return LIR_IN(m->op);
        }
}

static bool
remat_ok(Check *k, u32 const *st, u32 def, u32 pos, u32 depth)
{
        LirInst const *in = v_(k->L->insts, def);

        if (LirOps[in->op].form != LF_LD) {
                return true;
        }

        LirReg             b  = in->args[0].mem.base;
        LirInterval const *bi = &k->alloc->intervals[repof(k, b)];

        if (!covers(bi->ranges, bi->nranges, pos)) {
                return (depth < 4) && (bi->remat != LIR_NONE) && remat_ok(k, st, bi->remat, pos, depth + 1);
        }

        LirLoc l = lir_where(k->alloc, b, pos);

        if (l.remat != LIR_NONE) {
                return (depth < 4) && remat_ok(k, st, l.remat, pos, depth + 1);
        }

        return *cell(k, (u32 *)st, l, false) == repof(k, b);
}

static void
apply(Check *k, u32 *st, LirMove const *ms, u32 n)
{
        Ty  *ty = k->ty;
        u32 *v  = new(u32, n + 1);

        for (u32 i = 0; i < n; ++i) {
                LirMove const *m = &ms[i];
                bool           f = isfloat(m->cls) && !m->from_gpr;
                if (m->remat == LIR_NONE) {
                        v[i] = *cell(k, st, mloc(m->from_slot, m->from_phys, LIR_NONE), f);
                }
        }

        for (u32 i = 0; i < n; ++i) {
                LirMove const *m = &ms[i];
                bool           f = isfloat(m->cls) && !m->to_gpr;
                if (m->remat == LIR_NONE) {
                        *cell(k, st, mloc(m->to_slot, m->to_phys, LIR_NONE), f) = v[i];
                }
        }

        for (u32 i = 0; i < n; ++i) {
                LirMove const *m = &ms[i];
                bool           f = isfloat(m->cls) && !m->to_gpr;
                if (m->remat != LIR_NONE) {
                        v[i] = remat_ok(k, st, m->remat, check_pos(m), 0) ? m->from : LIR_NONE;
                        *cell(k, st, mloc(m->to_slot, m->to_phys, LIR_NONE), f) = v[i];
                }
        }
}

static bool
phase_moves(Check *k, u32 *st, u32 pc, LirMovePhase ph, u32 edge, int slow)
{
        Ty            *ty = k->ty;
        LirAlloc const *a = k->alloc;
        u32            n  = 0;
        LirMove       *ms = new(LirMove, a->nmoves + 1);

        for (u32 i = k->at[pc]; i != LIR_NONE; i = k->next[i]) {
                LirMove const *m = &a->moves[i];

                if (m->phase != ph || (edge != LIR_NONE && m->edge != edge)) {
                        continue;
                }

                if (slow >= 0 && m->slow != (bool)slow) {
                        continue;
                }

                if (m->kind == LIR_MOVE_ROOT) {
                        if (m->remat == LIR_NONE && *cell(k, st, mloc(m->from_slot, m->from_phys, LIR_NONE), false) != m->from) {
                                return bad(k, pc, "GC root reads a stale", m->from);
                        }
                        continue;
                }

                ms[n++] = *m;
        }

        apply(k, st, ms, n);

        return true;
}

static void
clobber(Check *k, u32 *st, bool f, u64 mask)
{
        for (u32 p = 0; p < LIR_MAX_PHYS; ++p) {
                if ((mask >> p) & 1) {
                        st[(f ? LIR_MAX_PHYS : 0) + p] = LIR_NONE;
                }
        }
}

static void
clobber_call(Check *k, u32 *st)
{
        LirTarget const *t = k->target;

        clobber(k, st, false, t->gpr.available & ~t->gpr.callee_saved);
        clobber(k, st, true, t->fpr.available & ~t->fpr.callee_saved);
}

static u8
fixed_phys(Check const *k, u32 pc, LirReg r, bool output)
{
        for (u32 i = 0; i < k->alloc->nconstraints; ++i) {
                LirConstraint const *c = &k->alloc->constraints[i];
                if (c->op == pc && c->reg == r && c->output == output && c->phys != LIR_PHYS_NONE) {
                        return c->phys;
                }
        }

        return LIR_PHYS_NONE;
}

static bool
reads(Check *k, u32 *st, u32 pc, LirReg r, bool must)
{
        LirReg rep  = repof(k, r);
        bool   f    = isfloat(v__(k->L->regs, r).cls);
        u8     phys = fixed_phys(k, pc, r, false);
        LirLoc l    = (phys != LIR_PHYS_NONE)
                    ? mloc(LIR_NONE, phys, LIR_NONE)
                    : lir_where(k->alloc, r, LIR_IN(pc));

        if (l.remat != LIR_NONE) {
                return !must || bad(k, pc, "register operand is rematerialized for", r);
        }

        if (l.phys == LIR_PHYS_NONE && l.slot == LIR_NONE) {
                return bad(k, pc, "no location for", r);
        }

        if (must && l.phys == LIR_PHYS_NONE) {
                return bad(k, pc, "register operand is in memory for", r);
        }

        if (*cell(k, st, l, f) != rep) {
                return bad(k, pc, "stale value for", r);
        }

        return true;
}

static void
forget(Check *k, u32 *st, LirReg rep)
{
        for (u32 i = 0; i < k->width; ++i) {
                if (st[i] == rep) {
                        st[i] = LIR_NONE;
                }
        }
}

static bool
writes(Check *k, u32 *st, u32 pc, LirReg r, u8 phys)
{
        LirReg         rep = repof(k, r);
        bool           f   = isfloat(v__(k->L->regs, r).cls);
        LirInst const *in  = v_(k->L->insts, pc);
        LirLoc         l   = (phys != LIR_PHYS_NONE)
                           ? mloc(LIR_NONE, phys, LIR_NONE)
                           : lir_where(k->alloc, r, LIR_OUT(pc));

        if (
                (in->op == LIR_MOV)
             && (in->args[0].kind == LO_REG)
             && (repof(k, in->args[0].reg) == rep)
        ) {
                return true;
        }

        if (l.phys == LIR_PHYS_NONE && l.slot == LIR_NONE) {
                return bad(k, pc, "no location for", r);
        }

        forget(k, st, rep);
        *cell(k, st, l, f) = rep;

        return true;
}

static bool
operands_ok(Check *k, u32 *st, u32 pc)
{
        LirInst const *in = v_(k->L->insts, pc);
        LirReg         rs[2];

        for (u32 j = 0; j < in->nargs + in->ncall_args; ++j) {
                LirOpnd a    = (j < in->nargs) ? in->args[j] : in->call_args[j - in->nargs];
                bool    must = (j < in->nargs)
                            && (a.kind == LO_MEM || (
                                       (in->op != LIR_CALL)
                                    && (in->op != LIR_TAILCALL)
                                    && (in->op != LIR_RET)
                                    && (in->op != LIR_POLL)
                               ));

                for (u32 x = 0, n = regs_of(a, rs); x < n; ++x) {
                        bool m = must && fixed_phys(k, pc, rs[x], false) == LIR_PHYS_NONE;
                        if (!reads(k, st, pc, rs[x], m)) {
                                return false;
                        }
                }
        }

        for (u32 j = 0; j < in->raw.nin; ++j) {
                LirRawBinding b = in->raw.in[j];
                bool          f = isfloat(v__(k->L->regs, b.reg).cls);
                if (*cell(k, st, mloc(LIR_NONE, b.phys, LIR_NONE), f) != repof(k, b.reg)) {
                        return bad(k, pc, "raw input is stale for", b.reg);
                }
        }

        return true;
}

static bool
effects(Check *k, u32 *st, u32 pc)
{
        LirInst const *in = v_(k->L->insts, pc);

        if (iscall(in->op)) {
                clobber_call(k, st);
        }

        clobber(k, st, false, in->raw.gpr_clobber);
        clobber(k, st, true, in->raw.fpr_clobber);

        for (u32 i = 0; i < k->alloc->nconstraints; ++i) {
                LirConstraint const *c = &k->alloc->constraints[i];
                if (c->op == pc && c->phys != LIR_PHYS_NONE && (c->output || c->reg == LIR_NONE)) {
                        bool f = (c->reg != LIR_NONE) ? isfloat(v__(k->L->regs, c->reg).cls) : c->fpr;
                        clobber(k, st, f, bit(c->phys));
                }
        }

        for (u32 j = 0; j < in->raw.nout; ++j) {
                LirRawBinding b = in->raw.out[j];
                bool          f = isfloat(v__(k->L->regs, b.reg).cls);
                clobber(k, st, f, bit(b.phys));
        }

        if (in->dst != LIR_NONE && !writes(k, st, pc, in->dst, fixed_phys(k, pc, in->dst, true))) {
                return false;
        }

        for (u32 j = 0; j < in->raw.nout; ++j) {
                if (!writes(k, st, pc, in->raw.out[j].reg, in->raw.out[j].phys)) {
                        return false;
                }
        }

        return true;
}

static void
join(Check *k, u32 b, u32 const *st, u32 *work, u32 *nwork, bool *queued)
{
        u32 *dst = &k->in[(usize)b * k->width];

        if (!k->seen[b]) {
                memcpy(dst, st, k->width * sizeof *st);
                k->seen[b] = true;
        } else {
                bool changed = false;
                for (u32 i = 0; i < k->width; ++i) {
                        if (dst[i] != st[i] && dst[i] != LIR_NONE) {
                                dst[i]  = LIR_NONE;
                                changed = true;
                        }
                }
                if (!changed) {
                        return;
                }
        }

        if (!queued[b]) {
                queued[b] = true;
                work[(*nwork)++] = b;
        }
}

static bool
flow(Check *k, u32 pb, u32 const *st, u32 const *slow, u32 *work, u32 *nwork, bool *queued)
{
        Ty             *ty  = k->ty;
        LirCFG const   *cfg = k->cfg;
        LirBlock const *P   = &cfg->blocks[pb];
        LirInst const  *in  = v_(k->L->insts, P->end - 1);
        u32            *tmp = new(u32, k->width);
        u32             nt  = isbranch(in) ? ((in->op == LIR_SWITCH) ? in->ntargets + 1 : 1) : 0;

        for (u32 j = 0; j < nt; ++j) {
                LirLabel     l  = (j == 0) ? in->args[in->nargs - 1].label : in->targets[j - 1];
                u32          sp = v__(k->L->labels, l).pos;
                u32          sb = cfg->block_at[sp];
                u32 const   *from = (in->op == LIR_POLL) ? slow : st;
                LirMovePhase ph   = (in->op == LIR_JMP) ? LIR_MOVE_EDGE_OUT : LIR_MOVE_STUB;

                memcpy(tmp, from, k->width * sizeof *tmp);

                if (!phase_moves(k, tmp, P->end - 1, ph, sp, -1)) {
                        return false;
                }

                if (!phase_moves(k, tmp, sp, LIR_MOVE_EDGE_IN, sp, -1)) {
                        return false;
                }

                join(k, sb, tmp, work, nwork, queued);
        }

        if (falls(in) && P->end < vN(k->L->insts)) {
                u32 sp = P->end;

                memcpy(tmp, st, k->width * sizeof *tmp);

                if (!phase_moves(k, tmp, P->end - 1, LIR_MOVE_EDGE_OUT, sp, -1)) {
                        return false;
                }

                join(k, cfg->block_at[sp], tmp, work, nwork, queued);
        }

        return true;
}

static bool
walk(Check *k, u32 b, u32 *work, u32 *nwork, bool *queued)
{
        Ty             *ty  = k->ty;
        LirBlock const *B   = &k->cfg->blocks[b];
        u32            *st  = new(u32, k->width);
        u32            *alt = new(u32, k->width);

        memcpy(st, &k->in[(usize)b * k->width], k->width * sizeof *st);
        memcpy(alt, st, k->width * sizeof *st);

        for (u32 pc = B->first; pc < B->end; ++pc) {
                LirInst const *in   = v_(k->L->insts, pc);
                bool           poll = (in->op == LIR_POLL);

                if (
                        !phase_moves(k, st, pc, LIR_MOVE_BEFORE, LIR_NONE, poll ? 0 : -1)
                     || !phase_moves(k, st, pc, LIR_MOVE_PIN, LIR_NONE, -1)
                ) {
                        return false;
                }

                if (!operands_ok(k, st, pc)) {
                        return false;
                }

                if (poll) {
                        memcpy(alt, st, k->width * sizeof *st);

                        if (!phase_moves(k, alt, pc, LIR_MOVE_BEFORE, LIR_NONE, 1)) {
                                return false;
                        }

                        clobber_call(k, alt);

                        if (!phase_moves(k, alt, pc, LIR_MOVE_AFTER, LIR_NONE, 1)) {
                                return false;
                        }

                        for (u32 i = 0; i < k->width; ++i) {
                                if (st[i] != alt[i]) {
                                        st[i] = LIR_NONE;
                                }
                        }
                }

                if (!effects(k, st, pc)) {
                        return false;
                }

                if (!phase_moves(k, st, pc, LIR_MOVE_AFTER, LIR_NONE, poll ? 0 : -1)) {
                        return false;
                }

                if (poll && !phase_moves(k, alt, pc, LIR_MOVE_AFTER, LIR_NONE, 0)) {
                        return false;
                }
        }

        return (B->first == B->end) || flow(k, b, st, alt, work, nwork, queued);
}

bool
lir_check_alloc(
        Ty *ty,
        Lir const *L,
        LirCFG const *cfg,
        LirTarget const *target,
        LirAlloc const *alloc,
        LirError *err
)
{
        Check k = {
                .ty     = ty,
                .L      = L,
                .cfg    = cfg,
                .target = target,
                .alloc  = alloc,
                .err    = err,
                .nslots = alloc->spill_size / 8
        };

        bool ok = true;

        u32   n      = vN(L->insts);
        u32   nb     = cfg->nblocks;
        u32  *work   = new(u32, nb + 1);
        bool *queued = new0(bool, nb + 1);
        u32   nwork  = 0;

        k.width = 2 * LIR_MAX_PHYS + k.nslots + 1;
        k.at    = nones(n + 1);
        k.next  = nones(alloc->nmoves + 1);
        k.in    = nones((usize)nb * k.width + 1);
        k.seen  = new0(bool, nb + 1);

        for (u32 i = alloc->nmoves; i-- > 0;) {
                u32 op = alloc->moves[i].op;
                if (op < n) {
                        k.next[i] = k.at[op];
                        k.at[op]  = i;
                }
        }

        u32 *entry = nones(k.width);

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirInterval const *i = &alloc->intervals[r];
                if (
                        (v__(L->regs, r).param != LIR_NONE)
                     && covers(i->ranges, i->nranges, 0)
                ) {
                        LirLoc l = lir_where(alloc, r, 0);
                        if (l.phys != LIR_PHYS_NONE || l.slot != LIR_NONE) {
                                *cell(&k, entry, l, isfloat(v__(L->regs, r).cls)) = i->rep;
                        }
                }
        }

        if (nb != 0 && cfg->blocks[0].reachable) {
                join(&k, 0, entry, work, &nwork, queued);
        }

        while (ok && nwork != 0) {
                u32 b = work[--nwork];
                queued[b] = false;
                ok = walk(&k, b, work, &nwork, queued);
        }

        return ok;
}

static void
dump_loc(Lir const *L, LirReg r, LirPiece const *p, LirInterval const *i, FILE *out)
{
        char bank = isfloat(v__(L->regs, r).cls) ? 'f' : 'g';

        if (p->phys != LIR_PHYS_NONE) {
                fprintf(out, "%c%u", bank, p->phys);
        } else if (i->remat != LIR_NONE) {
                fprintf(out, "remat@%u", i->remat);
        } else {
                fprintf(out, "spill+%u", i->spill);
        }
}

void
lir_dump_alloc(Lir const *L, LirAlloc const *alloc, FILE *out)
{
        for (u32 r = 0; r < alloc->nintervals; ++r) {
                LirInterval const *i   = &alloc->intervals[r];
                LirInterval const *rep = &alloc->intervals[i->rep];

                fprintf(out, "  r%u:", r);

                if (i->rep != r) {
                        fprintf(out, " = r%u\n", i->rep);
                        continue;
                }

                if (rep->npieces == 0) {
                        fprintf(out, " -\n");
                        continue;
                }

                for (u32 k = 0; k < rep->npieces; ++k) {
                        LirPiece const *p = &rep->pieces[k];
                        fprintf(out, " [%u.%u,%u.%u)=", p->start / 4, p->start % 4, p->end / 4, p->end % 4);
                        dump_loc(L, r, p, rep, out);
                }

                fputc('\n', out);
        }

        for (u32 k = 0; k < alloc->nmoves; ++k) {
                LirMove const *m = &alloc->moves[k];
                static char const *phases[] = { "before", "pin", "after", "edge-in", "edge-out", "stub" };

                if (m->kind == LIR_MOVE_ROOT) {
                        fprintf(out, "  root r%u @%u -> vslot %u%s\n", m->from, m->op, m->to_slot, m->slow ? " (slow)" : "");
                        continue;
                }

                fprintf(out, "  move r%u @%u %s", m->from, m->op, phases[m->phase]);

                if (m->edge != LIR_NONE) {
                        fprintf(out, " ->%u", m->edge);
                }

                if (m->remat != LIR_NONE) {
                        fprintf(out, ": remat@%u", m->remat);
                } else if (m->from_slot != LIR_NONE) {
                        fprintf(out, ": spill+%u", m->from_slot);
                } else {
                        fprintf(out, ": %u", m->from_phys);
                }

                if (m->to_slot != LIR_NONE) {
                        fprintf(out, " -> spill+%u", m->to_slot);
                } else {
                        fprintf(out, " -> %u", m->to_phys);
                }

                fprintf(out, "%s\n", m->slow ? " (slow)" : "");
        }
}
