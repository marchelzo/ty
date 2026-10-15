#include <string.h>
#include <stdlib.h>

#include "ty.h"
#include "jit/lir.h"

#define new(T, n)  ((T *)smA((usize)(n) * sizeof (T)))
#define new0(T, n) ((T *)smA0((usize)(n) * sizeof (T)))
#define nones(n)   ((u32 *)memset(new(u32, (n)), 0xff, (usize)(n) * sizeof (u32)))

#define cfor(c, x, k) for (u32 c = (x)->at[(k)]; c != LIR_NONE; c = v__((x)->next, c))

typedef struct {
        u32 reg;
        u32 start;
        u32 end;
} Span;

typedef struct {
        u32 reg;
        u32 pc;
} Use;

typedef struct {
        u32 reg;
        u32 start;
} Order;

typedef struct {
        u32     *at;
        u32     *last;
        vec(u32) next;
} Index;

typedef struct {
        Order *order;
        u32    norder;
        u32    next;
        u32   *live;
        u32    nlive;
        u32   *hits;
        u32    nhits;
} Sweep;

typedef struct {
        u32  slot;
        u8   phys;
        bool fp;
} Loc;

typedef struct {
        Ty                   *ty;
        Lir const            *L;
        LirTarget const      *target;
        LirAlloc             *alloc;
        u8                   *hint;
        u32                  *active;
        u32                   nactive;
        u32                  *ends;
        u64                   free[2];
        u64                  *live[2];
        u64                  *saved;
        u32                   nsaved;
        u32                   nslots;
        Index                 index;
        vec(u32)              touched;
        vec(Span)             spans;
        vec(Use)              uses;
        vec(LirMove)          moves;
        vec(LirConstraint)    cons;
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

inline static u64
alignup(u64 n, u64 a)
{
        return (n + a - 1) & ~(a - 1);
}

inline static u32
nregs(Scan const *s)
{
        return vN(s->L->regs);
}

inline static u32
ninsts(Scan const *s)
{
        return vN(s->L->insts);
}

inline static LirInst const *
inst(Scan const *s, u32 pc)
{
        return v_(s->L->insts, pc);
}

inline static bool
fpreg(Scan const *s, LirReg r)
{
        return isfloat(v__(s->L->regs, r).cls);
}

inline static bool
fpcon(Scan const *s, LirConstraint const *con)
{
        return (con->reg < nregs(s)) ? fpreg(s, con->reg) : con->fpr;
}

inline static LirInterval *
iv(Scan const *s, LirReg r)
{
        return &s->alloc->intervals[r];
}

inline static u32
iend(LirInterval const *i)
{
        return i->ranges[i->nranges - 1].end;
}

inline static LirRegPool const *
pool(Scan const *s, bool f)
{
        return f ? &s->target->fpr : &s->target->gpr;
}

inline static bool
iscall(LirOp op)
{
        return (op == LIR_CALL) || (op == LIR_TAILCALL) || (op == LIR_POLL);
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
chain(Scan const *s, u32 n, bool byreg)
{
        Ty   *ty = s->ty;
        u32   nc = vN(s->cons);
        Index x  = {
                .at   = nones(n + 1),
                .last = nones(n + 1),
                .next = { .items = nones(nc + 1), .count = nc, .capacity = nc + 1 }
        };

        for (u32 c = 0; c < nc; ++c) {
                LirConstraint const *con = v_(s->cons, c);
                u32 key = byreg ? con->reg : con->op;
                if (key < n) {
                        hook(&x, key, c);
                }
        }

        return x;
}

static void
bystart(Ty *ty, Order *xs, u32 n, u32 ninsts)
{
        if (n < 2) {
                return;
        }

        SCRATCH_SAVE();

        usize  lim   = 2 * (usize)ninsts + 2;
        u32   *count = new0(u32, lim + 1);
        Order *tmp   = new(Order, n);

        for (u32 k = 0; k < n; ++k) {
                count[xs[k].start + 1] += 1;
        }

        for (usize k = 1; k <= lim; ++k) {
                count[k] += count[k - 1];
        }

        for (u32 k = 0; k < n; ++k) {
                tmp[count[xs[k].start]++] = xs[k];
        }

        memcpy(xs, tmp, n * sizeof *xs);

        SCRATCH_RESTORE();
}

static int
regcmp(void const *a, void const *b)
{
        u32 x = *(u32 const *)a;
        u32 y = *(u32 const *)b;

        return (x < y) ? -1 : (x != y);
}

static Sweep
sweep(Scan const *s, bool (*want)(Scan const *, LirReg))
{
        Ty *ty = s->ty;
        u32 n = nregs(s);
        Sweep w = {
                .order = new(Order, n + 1),
                .live  = new(u32, n + 1),
                .hits  = new(u32, n + 1)
        };

        for (u32 r = 0; r < n; ++r) {
                if (want(s, r)) {
                        w.order[w.norder++] = (Order) { r, iv(s, r)->ranges[0].start };
                }
        }

        bystart(ty, w.order, w.norder, ninsts(s));

        return w;
}

static void
advance(Scan const *s, Sweep *w, u32 admit, u32 expire)
{
        u32 keep = 0;

        while (w->next < w->norder && w->order[w->next].start <= admit) {
                w->live[w->nlive++] = w->order[w->next++].reg;
        }

        for (u32 a = 0; a < w->nlive; ++a) {
                if (iend(iv(s, w->live[a])) > expire) {
                        w->live[keep++] = w->live[a];
                }
        }

        w->nlive = keep;
        w->nhits = 0;
}

static void
hit(Sweep *w, LirReg r)
{
        w->hits[w->nhits++] = r;
}

static void
sorthits(Sweep *w)
{
        if (w->nhits > 1) {
                qsort(w->hits, w->nhits, sizeof *w->hits, regcmp);
        }
}

static void
touch(Scan *s, LirReg r)
{
        Ty *ty = s->ty;
        svP(s->touched, r);
}

static void
span(Scan *s, LirReg r, u32 start, u32 end)
{
        Ty *ty = s->ty;

        if (start < end) {
                svP(s->spans, ((Span) { r, start, end }));
                iv(s, r)->nranges += 1;
        }
}

static void
use(Scan *s, LirReg r, u32 pc)
{
        Ty *ty = s->ty;

        if (s->ends[r] == LIR_NONE) {
                s->ends[r] = pc + 1;
                touch(s, r);
        }

        svP(s->uses, ((Use) { r, pc }));
        iv(s, r)->nuses += 1;
}

static void
def(Scan *s, LirReg r, u32 pc)
{
        u32 end = (s->ends[r] == LIR_NONE) ? pc + 1 : s->ends[r];
        s->ends[r] = LIR_NONE;
        span(s, r, pc, end);
}

static void
uses_of(Scan *s, LirOpnd a, u32 pc)
{
        LirReg rs[2];
        u32 n = regs_of(a, rs);

        for (u32 k = 0; k < n; ++k) {
                use(s, rs[k], pc);
        }
}

static void
coalesce(LirInterval *i)
{
        u32 n = 0;

        for (u32 j = 0; j < i->nranges; ++j) {
                LirRange r = i->ranges[j];
                if (n == 0 || r.start > i->ranges[n - 1].end) {
                        i->ranges[n++] = r;
                } else if (r.end > i->ranges[n - 1].end) {
                        i->ranges[n - 1].end = r.end;
                }
        }

        i->nranges = n;
        n = 0;

        for (u32 j = 0; j < i->nuses; ++j) {
                if (n == 0 || i->uses[j] != i->uses[n - 1]) {
                        i->uses[n++] = i->uses[j];
                }
        }

        i->nuses = n;
}

static void
pool_intervals(Scan *s)
{
        Ty       *ty     = s->ty;
        LirRange *ranges = new(LirRange, vN(s->spans) + 1);
        u32      *uses   = new(u32, vN(s->uses) + 1);

        for (u32 r = 0; r < nregs(s); ++r) {
                LirInterval *i = iv(s, r);
                i->ranges = (ranges += i->nranges);
                i->uses   = (uses += i->nuses);
        }

        for (u32 k = 0; k < vN(s->spans); ++k) {
                Span const *x = v_(s->spans, k);
                *--iv(s, x->reg)->ranges = (LirRange) { x->start, x->end };
        }

        vfor(s->uses, *--iv(s, it->reg)->uses = it->pc);

        for (u32 r = 0; r < nregs(s); ++r) {
                coalesce(iv(s, r));
        }
}

static void
build_intervals(Scan *s, LirCFG const *cfg)
{
        Ty *ty = s->ty;

        s->ends = nones(nregs(s) + 1);

        for (u32 b = cfg->nblocks; b-- > 0;) {
                LirBlock const *block = &cfg->blocks[b];

                v0(s->touched);

                for (u32 w = 0; w < cfg->nwords; ++w) {
                        for (u64 bits = block->live_out[w]; bits != 0; bits &= bits - 1) {
                                u32 r = cfg->globals[w * 64 + __builtin_ctzll(bits)];
                                s->ends[r] = 2 * block->end;
                                touch(s, r);
                        }
                }

                for (u32 pc = block->end; pc-- > block->first;) {
                        LirInst const *in = inst(s, pc);

                        if (in->dst != LIR_NONE) {
                                def(s, in->dst, 2 * pc + 1);
                        }

                        for (u32 j = 0; j < in->raw.nout; ++j) {
                                def(s, in->raw.out[j].reg, 2 * pc + 1);
                        }

                        for (u32 j = 0; j < in->nargs; ++j) {
                                uses_of(s, in->args[j], 2 * pc);
                        }

                        for (u32 j = 0; j < in->ncall_args; ++j) {
                                uses_of(s, in->call_args[j], 2 * pc);
                        }

                        for (u32 j = 0; j < in->raw.nin; ++j) {
                                use(s, in->raw.in[j].reg, 2 * pc);
                        }
                }

                for (u32 t = 0; t < vN(s->touched); ++t) {
                        u32 r = v__(s->touched, t);
                        if (s->ends[r] != LIR_NONE) {
                                span(s, r, 2 * block->first, s->ends[r]);
                                s->ends[r] = LIR_NONE;
                        }
                }
        }

        pool_intervals(s);
}

static bool
covers(LirInterval const *i, u32 pos)
{
        if (
                (i->nranges == 0)
             || (pos < i->ranges[0].start)
             || (pos >= iend(i))
        ) {
                return false;
        }

        u32 lo = 0;
        u32 hi = i->nranges;

        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (i->ranges[mid].start <= pos) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        return pos < i->ranges[lo - 1].end;
}

static bool
overlap(LirInterval const *a, LirInterval const *b)
{
        u32 i = 0;
        u32 j = 0;

        while (i < a->nranges && j < b->nranges) {
                LirRange x = a->ranges[i];
                LirRange y = b->ranges[j];

                if (x.start < y.end && y.start < x.end) {
                        return true;
                }

                if (x.end <= y.end) {
                        i += 1;
                } else {
                        j += 1;
                }
        }

        return false;
}

static u32
next_use(LirInterval const *i, u32 pos)
{
        u32 k = lower(i->uses, i->nuses, pos);
        return (k < i->nuses) ? i->uses[k] : LIR_NONE;
}

static bool
dead_after(Scan const *s, LirReg r, u32 pos)
{
        return next_use(iv(s, r), pos) == LIR_NONE;
}

static u32
slot(Scan *s)
{
        u32 at = s->alloc->spill_size;
        s->alloc->spill_size += 8;
        return at;
}

static void
spill(Scan *s, LirReg r)
{
        LirInterval *i = iv(s, r);

        if (!i->spilled) {
                i->spill = slot(s);
        }

        i->spilled = true;
        i->phys    = LIR_PHYS_NONE;
}

static void
move(Scan *s, LirMove m)
{
        Ty *ty = s->ty;
        svP(s->moves, m);
}

static bool
fresh(Scan *s, u64 key);

static void
rehash(Scan *s)
{
        Ty  *ty   = s->ty;
        u64 *old  = s->saved;
        u32  nold = s->nslots;

        s->nslots = (nold == 0) ? 64 : 2 * nold;
        s->saved  = new0(u64, s->nslots);
        s->nsaved = 0;

        for (u32 j = 0; j < nold; ++j) {
                if (old[j] != 0) {
                        fresh(s, old[j]);
                }
        }
}

static bool
fresh(Scan *s, u64 key)
{
        if (2 * (s->nsaved + 1) > s->nslots) {
                rehash(s);
        }

        u32 mask = s->nslots - 1;

        for (u32 h = hash64(key) & mask;; h = (h + 1) & mask) {
                if (s->saved[h] == key) {
                        return false;
                }
                if (s->saved[h] == 0) {
                        s->saved[h] = key;
                        s->nsaved  += 1;
                        return true;
                }
        }
}

static void
save(Scan *s, LirReg r, u32 pc, u8 phys)
{
        LirInterval *i   = iv(s, r);
        LirClass     cls = v__(s->L->regs, r).cls;

        if (i->call_save == LIR_NONE) {
                i->call_save = slot(s);
        }

        if (!fresh(s, ((u64)r << 32 | pc) + 1)) {
                return;
        }

        move(s, (LirMove) {
                .op        = pc,
                .phase     = LIR_MOVE_BEFORE,
                .from      = r,
                .to        = r,
                .cls       = cls,
                .from_slot = LIR_NONE,
                .to_slot   = i->call_save,
                .from_phys = phys,
                .to_phys   = LIR_PHYS_NONE
        });

        move(s, (LirMove) {
                .op        = pc,
                .phase     = LIR_MOVE_AFTER,
                .from      = r,
                .to        = r,
                .cls       = cls,
                .from_slot = i->call_save,
                .to_slot   = LIR_NONE,
                .from_phys = LIR_PHYS_NONE,
                .to_phys   = phys
        });
}

static bool
survives(Scan const *s, LirReg r, u32 pc)
{
        LirInst const *in = inst(s, pc);

        if (in->dst == r) {
                return false;
        }

        for (u32 o = 0; o < in->raw.nout; ++o) {
                if (in->raw.out[o].reg == r) {
                        return false;
                }
        }

        return covers(iv(s, r), 2 * pc) && covers(iv(s, r), 2 * pc + 1);
}

static bool
crosses(Scan const *s, LirReg r, u32 const *calls, u32 ncalls)
{
        LirInterval const *i = iv(s, r);

        for (u32 k = 0; k < i->nranges; ++k) {
                u32 end = i->ranges[k].end / 2;
                u32 c   = lower(calls, ncalls, (i->ranges[k].start + 1) / 2);

                while (c < ncalls && calls[c] < end) {
                        if (survives(s, r, calls[c++])) {
                                return true;
                        }
                }
        }

        return false;
}

static void
hint_args(Scan *s, LirInst const *in, u32 pc)
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

                if (
                        (arg.kind == LO_REG)
                     && (a < pool(s, f)->nargs)
                     && dead_after(s, arg.reg, 2 * pc + 1)
                ) {
                        s->hint[arg.reg] = pool(s, f)->args[a];
                }
        }
}

static void
hints(Scan *s)
{
        Ty        *ty      = s->ty;
        Lir const *L       = s->L;
        u32        next[2] = {0};
        u32        ncalls  = 0;

        SCRATCH_SAVE();

        u32 *calls = new(u32, ninsts(s) + 1);

        for (u32 pc = 0; pc < ninsts(s); ++pc) {
                if (iscall(inst(s, pc)->op)) {
                        calls[ncalls++] = pc;
                }
        }

        for (u32 r = 0; r < nregs(s); ++r) {
                iv(s, r)->crosses_call = crosses(s, r, calls, ncalls);
        }

        SCRATCH_RESTORE();

        for (u32 p = 0; p < L->sig.nparams; ++p) {
                LirReg r = L->params[p];
                bool   f = fpreg(s, r);
                u32    a = next[f]++;
                if (a < pool(s, f)->nargs) {
                        s->hint[r] = pool(s, f)->args[a];
                }
        }

        for (u32 pc = 0; pc < ninsts(s); ++pc) {
                LirInst const *in = inst(s, pc);

                LirReg r = in->args[0].reg;

                if (
                        (in->op == LIR_RET)
                     && (in->nargs == 1)
                     && (in->args[0].kind == LO_REG)
                     && dead_after(s, r, 2 * pc + 1)
                ) {
                        s->hint[r] = pool(s, fpreg(s, r))->ret;
                }

                if (in->op == LIR_CALL || in->op == LIR_TAILCALL) {
                        hint_args(s, in, pc);
                }
        }
}

static bool
retired(LirInterval const *i, u32 pos)
{
        return (i->nranges != 0) && (iend(i) <= pos);
}

static u8
prefer(Scan const *s, Index const *byreg, LirReg r, u32 pos)
{
        u8 hint = s->hint[r];
        u32 pc  = pos / 2;

        if (pc < ninsts(s)) {
                LirInst const *in = inst(s, pc);
                if (in->dst == r && in->op == LIR_MOV && in->args[0].kind == LO_REG) {
                        LirInterval const *src = iv(s, in->args[0].reg);
                        if (retired(src, pos) && src->phys != LIR_PHYS_NONE) {
                                hint = src->phys;
                        }
                }
        }

        cfor (c, byreg, r) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->phys != LIR_PHYS_NONE) {
                        return con->phys;
                }
                if (con->tied < nregs(s) && retired(iv(s, con->tied), pos)) {
                        hint = iv(s, con->tied)->phys;
                }
        }

        return hint;
}

static u64
expire(Scan *s, LirInterval const *cur, bool f, u32 pos)
{
        u64 free = s->free[f];
        u32 keep = 0;

        for (u32 a = 0; a < s->nactive; ++a) {
                LirReg             v = s->active[a];
                LirInterval const *i = iv(s, v);

                if (i->spilled || iend(i) <= pos) {
                        continue;
                }

                s->active[keep++] = v;

                if (fpreg(s, v) == f && overlap(cur, i)) {
                        free &= ~bit(i->phys);
                }
        }

        s->nactive = keep;

        return free;
}

static bool
rival(Scan const *s, LirInterval const *cur, bool f, LirReg r)
{
        return (fpreg(s, r) == f) && overlap(cur, iv(s, r));
}

static bool
unique(Scan const *s, LirInterval const *cur, bool f, LirReg v)
{
        for (u32 b = 0; b < s->nactive; ++b) {
                LirReg w = s->active[b];
                if (
                        (w != v)
                     && (iv(s, w)->phys == iv(s, v)->phys)
                     && rival(s, cur, f, w)
                ) {
                        return false;
                }
        }

        return true;
}

static LirReg
victim(Scan const *s, LirInterval const *cur, bool f, u32 pos)
{
        LirReg victim   = LIR_NONE;
        u32    furthest = next_use(cur, pos);

        for (u32 a = 0; a < s->nactive; ++a) {
                LirReg v = s->active[a];

                if (!rival(s, cur, f, v)) {
                        continue;
                }

                u32 use = next_use(iv(s, v), pos);

                if (unique(s, cur, f, v) && use > furthest) {
                        victim   = v;
                        furthest = use;
                }
        }

        return victim;
}

static void
place(Scan *s, Index const *byreg, Order o)
{
        LirReg       r    = o.reg;
        u32          pos  = o.start;
        LirInterval *cur  = iv(s, r);
        bool         f    = fpreg(s, r);
        u64          free = expire(s, cur, f, pos);
        u64          safe = free & pool(s, f)->callee_saved;
        u64          pick = (cur->crosses_call && safe != 0) ? safe : free;
        u8           hint = prefer(s, byreg, r, pos);

        if (hint < LIR_MAX_PHYS && (pick & bit(hint))) {
                cur->phys = hint;
        } else if (pick != 0) {
                cur->phys = __builtin_ctzll(pick);
        } else {
                LirReg v = victim(s, cur, f, pos);

                if (v == LIR_NONE) {
                        spill(s, r);
                        return;
                }

                cur->phys = iv(s, v)->phys;
                spill(s, v);
        }

        s->active[s->nactive++] = r;
}

static void
assign(Scan *s)
{
        Ty *ty = s->ty;
        u32 n  = 0;

        SCRATCH_SAVE();

        Order *order = new(Order, nregs(s) + 1);
        Index  byreg = chain(s, nregs(s), true);

        for (u32 r = 0; r < nregs(s); ++r) {
                LirInterval const *i = iv(s, r);
                if (i->nranges != 0 && v__(s->L->regs, r).pin == LIR_NONE) {
                        order[n++] = (Order) { r, i->ranges[0].start };
                }
        }

        bystart(ty, order, n, ninsts(s));

        for (u32 o = 0; o < n; ++o) {
                place(s, &byreg, order[o]);
        }

        SCRATCH_RESTORE();
}

static bool
rooted(Scan const *s, LirReg r)
{
        LirInterval const *i   = iv(s, r);
        bool               ref = v__(s->L->regs, r).cls == LIR_REF;

        return (i->crosses_call || ref) && (i->nranges != 0);
}

static void
root(Scan *s, LirReg r, u32 pc)
{
        LirInterval *i = iv(s, r);

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
                .from_slot = i->spilled ? i->spill : LIR_NONE,
                .from_phys = i->phys,
                .to_slot   = i->root_slot,
                .to_phys   = LIR_PHYS_NONE
        });
}

static bool
may_gc(LirInst const *in)
{
        return (in->flags & (LIR_MAY_GC | LIR_MAY_THROW)) || (in->op == LIR_POLL);
}

static void
call_moves(Scan *s)
{
        Sweep w = sweep(s, rooted);

        for (u32 pc = 0; pc < ninsts(s); ++pc) {
                LirInst const *in   = inst(s, pc);
                bool           call = iscall(in->op);
                bool           gc   = may_gc(in);

                if (!call && !gc) {
                        continue;
                }

                advance(s, &w, 2 * pc + 1, 2 * pc);

                for (u32 a = 0; a < w.nlive; ++a) {
                        hit(&w, w.live[a]);
                }

                sorthits(&w);

                for (u32 k = 0; k < w.nhits; ++k) {
                        LirReg            r     = w.hits[k];
                        LirInterval      *i     = iv(s, r);
                        LirRegInfo const *ri    = v_(s->L->regs, r);
                        bool              alive = survives(s, r, pc);
                        u64               keep  = pool(s, isfloat(ri->cls))->callee_saved;

                        if (
                                alive
                             && call
                             && (i->phys != LIR_PHYS_NONE)
                             && (ri->pin == LIR_NONE)
                             && !(keep & bit(i->phys))
                        ) {
                                save(s, r, pc, i->phys);
                        }

                        if (gc && ri->cls == LIR_REF && covers(i, 2 * pc)) {
                                root(s, r, pc);
                        }
                }
        }
}

static void
pin(Scan *s, LirReg r, u8 phys, bool output, u32 pc)
{
        LirInterval const *i    = iv(s, r);
        u32                home = i->spilled ? i->spill : LIR_NONE;
        LirMove            m    = {
                .op        = pc,
                .phase     = output ? LIR_MOVE_AFTER : LIR_MOVE_BEFORE,
                .from      = r,
                .to        = r,
                .cls       = v__(s->L->regs, r).cls,
                .from_slot = output ? LIR_NONE : home,
                .to_slot   = output ? home : LIR_NONE,
                .from_phys = output ? phys : i->phys,
                .to_phys   = output ? i->phys : phys
        };

        if (
                (m.from_slot != LIR_NONE)
             || (m.to_slot != LIR_NONE)
             || (m.from_phys != m.to_phys)
        ) {
                move(s, m);
        }
}

static bool
placed(Scan const *s, LirReg r)
{
        LirInterval const *i = iv(s, r);
        return (i->phys != LIR_PHYS_NONE) && (i->nranges != 0);
}

static void
pin_raw(Scan *s, LirRawBinding const *bs, u32 n, bool output, u32 pc, u64 m[2])
{
        for (u32 o = 0; o < n; ++o) {
                m[fpreg(s, bs[o].reg)] |= bit(bs[o].phys);
                pin(s, bs[o].reg, bs[o].phys, output, pc);
        }
}

static bool
clobbered(Scan const *s, LirReg r, u32 pc)
{
        LirRaw const      *raw = &inst(s, pc)->raw;
        LirInterval const *i   = iv(s, r);
        bool               f   = fpreg(s, r);
        u64                cl  = f ? raw->fpr_clobber : raw->gpr_clobber;
        bool               own = false;
        bool               hit = (cl & bit(i->phys)) != 0;

        cfor (c, &s->index, pc) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->phys == i->phys) {
                        own = own || (con->reg == r && !con->output);
                        hit = hit || (con->output && fpcon(s, con) == f);
                }
        }

        for (u32 o = 0; o < raw->nout; ++o) {
                LirRawBinding b = raw->out[o];
                hit = hit || (b.phys == i->phys && fpreg(s, b.reg) == f);
        }

        for (u32 o = 0; o < raw->nin; ++o) {
                LirRawBinding b = raw->in[o];
                own = own || (b.reg == r && b.phys == i->phys);
        }

        return !own || hit;
}

static void
constraint_moves(Scan *s)
{
        Sweep w = sweep(s, placed);

        for (u32 pc = 0; pc < ninsts(s); ++pc) {
                LirRaw const *raw  = &inst(s, pc)->raw;
                u64           m[2] = { raw->gpr_clobber, raw->fpr_clobber };

                cfor (c, &s->index, pc) {
                        LirConstraint const *con = v_(s->cons, c);
                        if (con->phys == LIR_PHYS_NONE) {
                                continue;
                        }
                        m[fpcon(s, con)] |= bit(con->phys);
                        if (con->reg != LIR_NONE) {
                                pin(s, con->reg, con->phys, con->output, pc);
                        }
                }

                pin_raw(s, raw->in, raw->nin, false, pc, m);
                pin_raw(s, raw->out, raw->nout, true, pc, m);

                if ((m[0] | m[1]) == 0) {
                        continue;
                }

                advance(s, &w, 2 * pc, 2 * pc + 1);

                for (u32 a = 0; a < w.nlive; ++a) {
                        LirReg r    = w.live[a];
                        u64    mask = m[fpreg(s, r)];
                        if ((mask & bit(iv(s, r)->phys)) && survives(s, r, pc)) {
                                hit(&w, r);
                        }
                }

                sorthits(&w);

                for (u32 h = 0; h < w.nhits; ++h) {
                        if (clobbered(s, w.hits[h], pc)) {
                                save(s, w.hits[h], pc, iv(s, w.hits[h])->phys);
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

        for (u32 pc = 0; pc < ninsts(s); ++pc) {
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
                align  = max(align, a);
        }

        size = alignup(size, align);

        if (size > INT32_MAX) {
                return false;
        }

        alloc->frame_size  = size;
        alloc->frame_align = align;

        for (u32 r = 0; r < nregs(s); ++r) {
                if (iv(s, r)->phys != LIR_PHYS_NONE) {
                        preserve(s, fpreg(s, r), bit(iv(s, r)->phys));
                }
        }

        for (u32 c = 0; c < vN(s->cons); ++c) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->phys != LIR_PHYS_NONE) {
                        preserve(s, fpcon(s, con), bit(con->phys));
                }
        }

        for (u32 pc = 0; pc < ninsts(s); ++pc) {
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

static void
publish(Scan *s)
{
        s->alloc->moves        = vv(s->moves);
        s->alloc->nmoves       = vN(s->moves);
        s->alloc->constraints  = vv(s->cons);
        s->alloc->nconstraints = vN(s->cons);
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
        return (con->op < ninsts(s))
            && (con->reg == LIR_NONE || con->reg < nregs(s))
            && (con->phys == LIR_PHYS_NONE || con->phys < LIR_MAX_PHYS)
            && (con->tied == LIR_NONE || con->tied < nregs(s));
}

static bool
allocate(Scan *s, LirCFG const *cfg, LirError *err)
{
        Ty              *ty     = s->ty;
        Lir const       *L      = s->L;
        LirTarget const *target = s->target;
        LirAlloc        *alloc  = s->alloc;

        alloc->intervals      = new(LirInterval, nregs(s) + 1);
        alloc->alloca_offsets = new0(u32, ninsts(s) + 1);
        alloc->nintervals     = nregs(s);
        alloc->nvslots        = L->nvslots;

        s->hint    = memset(new(u8, nregs(s) + 1), LIR_PHYS_NONE, nregs(s) + 1);
        s->active  = new(u32, nregs(s) + 1);
        s->free[0] = target->gpr.available;
        s->free[1] = target->fpr.available;

        for (u32 r = 0; r < nregs(s); ++r) {
                LirInterval *i = iv(s, r);
                u32          p = v__(L->regs, r).pin;

                *i = (LirInterval) {
                        .reg       = r,
                        .spill     = LIR_NONE,
                        .call_save = LIR_NONE,
                        .root_slot = LIR_NONE,
                        .phys      = LIR_PHYS_NONE
                };

                if (p == LIR_NONE) {
                        continue;
                }

                if (p >= target->npins || target->pins[p] >= LIR_MAX_PHYS) {
                        return fail(err, LIR_NONE, "pin is unavailable on this target");
                }

                i->phys     = target->pins[p];
                s->free[0] &= ~bit(i->phys);
        }

        for (u32 c = 0; c < vN(s->cons); ++c) {
                LirConstraint const *con = v_(s->cons, c);
                if (!constraint_valid(s, con)) {
                        return fail(err, con->op, "invalid fixed-register constraint");
                }
        }

        build_intervals(s, cfg);
        hints(s);
        assign(s);
        call_moves(s);

        s->index = chain(s, ninsts(s), false);

        constraint_moves(s);

        if (!frame(s)) {
                return fail(err, LIR_NONE, "native frame is too large");
        }

        publish(s);

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
        Scan s = { .ty = ty, .L = L, .target = target, .alloc = alloc };

        *alloc = (LirAlloc) {0};

        if (err != NULL) {
                *err = (LirError) {0};
        }

        if (
                !target_valid(target)
             || (vN(L->insts) >= UINT32_MAX / 2)
             || (nconstraints != 0 && constraints == NULL)
        ) {
                return fail(err, LIR_NONE, "invalid allocation target or constraints");
        }

        svR(s.cons, nconstraints + 1);
        s.cons.count = nconstraints;
        memcpy(vv(s.cons), constraints, nconstraints * sizeof *constraints);

        if (!allocate(&s, cfg, err)) {
                *alloc = (LirAlloc) {0};
                return false;
        }

        return true;
}

static Loc
src(LirMove const *m)
{
        return (Loc) { m->from_slot, m->from_phys, isfloat(m->cls) && !m->from_gpr };
}

static Loc
dst(LirMove const *m)
{
        return (Loc) { m->to_slot, m->to_phys, isfloat(m->cls) && !m->to_gpr };
}

static bool
same(Loc a, Loc b)
{
        if (a.slot != LIR_NONE || b.slot != LIR_NONE) {
                return a.slot == b.slot;
        }

        return (a.phys == b.phys) && (a.fp == b.fp);
}

static bool
nowhere(u32 slot, u8 phys)
{
        return (slot == LIR_NONE) && (phys >= LIR_MAX_PHYS);
}

static bool
blocked(LirMove const *ms, u32 n, u32 i)
{
        for (u32 j = 0; j < n; ++j) {
                if (j != i && same(dst(&ms[i]), src(&ms[j]))) {
                        return true;
                }
        }

        return false;
}

static u32
ready(LirMove const *ms, u32 n)
{
        for (u32 i = 0; i < n; ++i) {
                if (!blocked(ms, n, i)) {
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

        SCRATCH_SAVE();

        LirMove *pending = new(LirMove, count + 1);
        Loc      tmp     = { LIR_NONE, pool->scratch[0], false };

        for (u32 i = 0; i < count; ++i) {
                LirMove m = moves[i];

                if (
                        (m.kind != LIR_MOVE_COPY)
                     || nowhere(m.from_slot, m.from_phys)
                     || nowhere(m.to_slot, m.to_phys)
                ) {
                        fail(err, m.op, "invalid parallel move location");
                        goto End;
                }

                if (!same(src(&m), dst(&m))) {
                        pending[n++] = m;
                }
        }

        for (u32 i = 0; i < n; ++i) {
                for (u32 j = 0; j < i; ++j) {
                        if (same(dst(&pending[i]), dst(&pending[j]))) {
                                fail(err, pending[i].op, "duplicate parallel move destination");
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
                        if (same(src(&pending[j]), tmp) || same(dst(&pending[j]), tmp)) {
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
                        if (same(src(&pending[j]), src(&save))) {
                                pending[j].from_slot = LIR_NONE;
                                pending[j].from_phys = tmp.phys;
                                pending[j].from_gpr  = isfloat(pending[j].cls);
                        }
                }
        }

        *out  = done;
        *nout = ndone;
        ok    = true;

End:
        SCRATCH_RESTORE();
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

        return alloc->intervals[reg].phys;
}

static u8
fixed(Scan const *s, LirReg r, u32 pc, bool output)
{
        cfor (c, &s->index, pc) {
                LirConstraint const *con = v_(s->cons, c);
                if (
                        (con->reg == r)
                     && (con->output == output)
                     && (con->phys != LIR_PHYS_NONE)
                ) {
                        return con->phys;
                }
        }

        return LIR_PHYS_NONE;
}

static bool
workspace(Scan *s, LirReg r, u32 pc, bool output, u64 m[2])
{
        Ty                *ty   = s->ty;
        LirInterval const *i    = iv(s, r);
        bool               f    = fpreg(s, r);
        u8                 phys = i->phys;

        if (!i->spilled) {
                return true;
        }

        if (phys == LIR_PHYS_NONE) {
                phys = fixed(s, r, pc, output);
        }

        if (phys != LIR_PHYS_NONE) {
                return true;
        }

        phys = fixed(s, r, pc, !output);

        if (phys == LIR_PHYS_NONE) {
                u64 avail = s->free[f] & ~m[f];

                if (avail == 0) {
                        return false;
                }

                u64 free = avail & ~(s->live[f][2 * pc] | s->live[f][2 * pc + 1]);

                phys  = (free != 0) ? __builtin_ctzll(free) : 63 - __builtin_clzll(avail);
                m[f] |= bit(phys);
        }

        svP(s->index.next, LIR_NONE);
        hook(&s->index, pc, vN(s->cons));
        svP(
                s->cons,
                ((LirConstraint) {
                        .op     = pc,
                        .reg    = r,
                        .phys   = phys,
                        .output = output,
                        .fpr    = f,
                        .tied   = LIR_NONE
                })
        );

        return true;
}

static void
occupy(Scan const *s, LirReg r, u64 m[2])
{
        u8 p = iv(s, r)->phys;

        if (p != LIR_PHYS_NONE) {
                m[fpreg(s, r)] |= bit(p);
        }
}

static bool
skips_workspace(LirOp op)
{
        return iscall(op) || (op == LIR_RET) || (op == LIR_RAW);
}

static void
mark_live(Scan *s)
{
        for (u32 r = 0; r < nregs(s); ++r) {
                LirInterval const *i = iv(s, r);

                if (v__(s->L->regs, r).pin != LIR_NONE) {
                        s->free[0] &= ~bit(i->phys);
                }

                if (i->phys == LIR_PHYS_NONE) {
                        continue;
                }

                u64 *live = s->live[fpreg(s, r)];

                for (u32 j = 0; j < i->nranges; ++j) {
                        LirRange x = i->ranges[j];
                        for (u32 pos = x.start; pos < x.end; ++pos) {
                                live[pos] |= bit(i->phys);
                        }
                }
        }
}

static bool
workspaces(Scan *s, u32 pc)
{
        LirInst const *in   = inst(s, pc);
        u64            m[2] = {0};
        LirReg         rs[2];

        if (in->dst != LIR_NONE) {
                occupy(s, in->dst, m);
        }

        for (u32 j = 0; j < in->nargs; ++j) {
                for (u32 k = 0, n = regs_of(in->args[j], rs); k < n; ++k) {
                        occupy(s, rs[k], m);
                }
        }

        cfor (c, &s->index, pc) {
                LirConstraint const *con = v_(s->cons, c);
                if (con->phys != LIR_PHYS_NONE) {
                        bool f = con->fpr || (con->reg < nregs(s) && fpreg(s, con->reg));
                        m[f] |= bit(con->phys);
                }
        }

        for (u32 j = 0; j < in->nargs; ++j) {
                for (u32 k = 0, n = regs_of(in->args[j], rs); k < n; ++k) {
                        if (!workspace(s, rs[k], pc, false, m)) {
                                return false;
                        }
                }
        }

        return (in->dst == LIR_NONE) || workspace(s, in->dst, pc, true, m);
}

bool
lir_allocate_workspaces(
        Ty *ty,
        Lir const *L,
        LirTarget const *target,
        LirAlloc *alloc,
        LirError *err
)
{
        if (alloc->spill_size == 0) {
                return true;
        }

        static char const why[] = "could not assign native spill workspaces";

        u32  n = vN(L->insts);
        Scan s = {
                .ty     = ty,
                .L      = L,
                .target = target,
                .alloc  = alloc,
                .free   = { target->gpr.available, target->fpr.available },
                .live   = { new0(u64, 2 * n + 1), new0(u64, 2 * n + 1) },
                .cons   = {
                        .items    = alloc->constraints,
                        .count    = alloc->nconstraints,
                        .capacity = alloc->nconstraints
                }
        };

        s.index = chain(&s, ninsts(&s), false);

        mark_live(&s);

        for (u32 pc = 0; pc < ninsts(&s); ++pc) {
                if (!skips_workspace(inst(&s, pc)->op) && !workspaces(&s, pc)) {
                        return fail(err, LIR_NONE, why);
                }
        }

        call_moves(&s);
        constraint_moves(&s);

        if (!frame(&s)) {
                return fail(err, LIR_NONE, why);
        }

        publish(&s);

        return true;
}
