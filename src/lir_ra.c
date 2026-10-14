#include <string.h>
#include <stdlib.h>
#include <limits.h>

#include "lir.h"

typedef struct lir_interval_build {
        u32 ranges;
        u32 uses;
        u8 hint;
} LirIntervalBuild;

typedef struct lir_scan {
        Lir const *L;
        LirTarget const *target;
        LirAlloc *alloc;
        LirIntervalBuild *build;
        u32 *active;
        u32 nactive;
        u32 move_capacity;
        u64 gpr;
        u64 fpr;
        LirError *err;
} LirScan;

static bool
ra_fail(LirError *err, LirErrorKind kind, u32 op, char const *message)
{
        if (err != NULL) {
                *err = (LirError) { .kind = kind, .op = op };
                snprintf(err->message, sizeof err->message, "%s", message);
        }
        return false;
}

static bool
reserve(void *ptr, u32 *cap, u32 n, usize size)
{
        void *p;
        void *q;
        u32 count = *cap;
        if (n <= count) {
                return true;
        }
        count = count == 0 ? 4 : count;
        while (count < n) {
                if (count > UINT32_MAX / 2) {
                        count = n;
                        break;
                }
                count *= 2;
        }
        if (count > SIZE_MAX / size) {
                return false;
        }
        memcpy(&p, ptr, sizeof p);
        q = realloc(p, count * size);
        if (q == NULL) {
                return false;
        }
        memcpy(ptr, &q, sizeof q);
        *cap = count;
        return true;
}

static bool
fp(LirClass cls)
{
        return cls == LIR_F32 || cls == LIR_F64;
}

static bool
has(u64 const *set, u32 r)
{
        return (set[r / 64] >> (r % 64)) & 1;
}

static bool
add_range(LirScan *s, u32 r, u32 start, u32 end)
{
        LirInterval *i = &s->alloc->intervals[r];
        if (start >= end) {
                return true;
        }
        if (!reserve(&i->ranges, &s->build[r].ranges, i->nranges + 1, sizeof *i->ranges)) {
                return false;
        }
        i->ranges[i->nranges++] = (LirRange) { .start = start, .end = end };
        return true;
}

static bool
add_use(LirScan *s, u32 r, u32 pc, u32 *ends)
{
        LirInterval *i = &s->alloc->intervals[r];
        if (ends[r] == LIR_NONE) {
                ends[r] = pc + 1;
        }
        if (!reserve(&i->uses, &s->build[r].uses, i->nuses + 1, sizeof *i->uses)) {
                return false;
        }
        i->uses[i->nuses++] = pc;
        return true;
}

static bool
use_operand(LirScan *s, LirOpnd a, u32 pc, u32 *ends)
{
        if (a.kind == LIR_OPERAND_REG) {
                return add_use(s, a.reg, pc, ends);
        }
        if (a.kind == LIR_OPERAND_MEM) {
                if (!add_use(s, a.mem.base, pc, ends)) {
                        return false;
                }
                if (a.mem.index != LIR_NONE) {
                        return add_use(s, a.mem.index, pc, ends);
                }
        }
        return true;
}

static bool
add_def(LirScan *s, u32 r, u32 pc, u32 *ends)
{
        u32 end = ends[r] == LIR_NONE ? pc + 1 : ends[r];
        ends[r] = LIR_NONE;
        return add_range(s, r, pc, end);
}

static int
range_cmp(void const *a, void const *b)
{
        LirRange const *x = a;
        LirRange const *y = b;
        if (x->start != y->start) {
                return x->start < y->start ? -1 : 1;
        }
        return x->end < y->end ? -1 : x->end != y->end;
}

static int
use_cmp(void const *a, void const *b)
{
        u32 x = *(u32 const *)a;
        u32 y = *(u32 const *)b;
        return x < y ? -1 : x != y;
}

static bool
build_intervals(LirScan *s, LirCFG const *cfg)
{
        Lir const *L = s->L;
        u32 *ends = malloc(((usize)L->nregs + 1) * sizeof *ends);
        if (ends == NULL) {
                return false;
        }
        for (u32 b = 0; b < cfg->nblocks; ++b) {
                LirBlock const *block = &cfg->blocks[b];
                for (u32 r = 0; r < L->nregs; ++r) {
                        ends[r] = has(block->live_out, r) ? 2 * block->end : LIR_NONE;
                }
                for (u32 pc = block->end; pc-- > block->first;) {
                        LirInst const *in = &L->insts[pc];
                        if (in->dst != LIR_NONE && !add_def(s, in->dst, 2 * pc + 1, ends)) {
                                goto Error;
                        }
                        for (u32 j = 0; j < in->raw.nout; ++j) {
                                if (!add_def(s, in->raw.out[j].reg, 2 * pc + 1, ends)) {
                                        goto Error;
                                }
                        }
                        for (u32 j = 0; j < in->nargs; ++j) {
                                if (!use_operand(s, in->args[j], 2 * pc, ends)) {
                                        goto Error;
                                }
                        }
                        for (u32 j = 0; j < in->ncall_args; ++j) {
                                if (!use_operand(s, in->call_args[j], 2 * pc, ends)) {
                                        goto Error;
                                }
                        }
                        for (u32 j = 0; j < in->raw.nin; ++j) {
                                if (!add_use(s, in->raw.in[j].reg, 2 * pc, ends)) {
                                        goto Error;
                                }
                        }
                }
                for (u32 r = 0; r < L->nregs; ++r) {
                        if (ends[r] != LIR_NONE && !add_range(s, r, 2 * block->first, ends[r])) {
                                goto Error;
                        }
                }
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                LirInterval *i = &s->alloc->intervals[r];
                u32 n = 0;
                if (i->nranges > 1) {
                        qsort(i->ranges, i->nranges, sizeof *i->ranges, range_cmp);
                }
                for (u32 j = 0; j < i->nranges; ++j) {
                        LirRange range = i->ranges[j];
                        if (n != 0 && range.start <= i->ranges[n - 1].end) {
                                if (range.end > i->ranges[n - 1].end) {
                                        i->ranges[n - 1].end = range.end;
                                }
                        } else {
                                i->ranges[n++] = range;
                        }
                }
                i->nranges = n;
                if (i->nuses > 1) {
                        qsort(i->uses, i->nuses, sizeof *i->uses, use_cmp);
                }
                n = 0;
                for (u32 j = 0; j < i->nuses; ++j) {
                        if (n == 0 || i->uses[j] != i->uses[n - 1]) {
                                i->uses[n++] = i->uses[j];
                        }
                }
                i->nuses = n;
        }
        free(ends);
        return true;
Error:
        free(ends);
        return false;
}

static bool
covers(LirInterval const *i, u32 pos)
{
        if (i->nranges == 0 || pos < i->ranges[0].start
            || pos >= i->ranges[i->nranges - 1].end) {
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
                if (a->ranges[i].start < b->ranges[j].end
                    && b->ranges[j].start < a->ranges[i].end) {
                        return true;
                }
                if (a->ranges[i].end <= b->ranges[j].end) {
                        ++i;
                } else {
                        ++j;
                }
        }
        return false;
}

static u32
next_use(LirInterval const *i, u32 pos)
{
        u32 lo = 0;
        u32 hi = i->nuses;
        while (lo < hi) {
                u32 mid = lo + (hi - lo) / 2;
                if (i->uses[mid] < pos) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }
        return lo < i->nuses ? i->uses[lo] : LIR_NONE;
}

static bool
slot(LirScan *s, u32 *out)
{
        if (s->alloc->spill_size > UINT32_MAX - 8) {
                return false;
        }
        *out = s->alloc->spill_size;
        s->alloc->spill_size += 8;
        return true;
}

static bool
spill(LirScan *s, u32 reg)
{
        LirInterval *i = &s->alloc->intervals[reg];
        if (!i->spilled && !slot(s, &i->spill)) {
                return false;
        }
        i->spilled = true;
        i->phys = LIR_PHYS_NONE;
        return true;
}

static bool
append_move(LirScan *s, LirMove move)
{
        if (!reserve(&s->alloc->moves, &s->move_capacity,
                     s->alloc->nmoves + 1, sizeof *s->alloc->moves)) {
                return false;
        }
        s->alloc->moves[s->alloc->nmoves++] = move;
        return true;
}

static bool
save_move(LirScan *s, u32 reg, u32 pc, u8 phys)
{
        LirInterval *i = &s->alloc->intervals[reg];
        if (i->call_save == LIR_NONE && !slot(s, &i->call_save)) {
                return false;
        }
        for (u32 j = 0; j < s->alloc->nmoves; ++j) {
                LirMove const *m = &s->alloc->moves[j];
                if (m->op == pc && m->phase == LIR_MOVE_BEFORE
                    && m->kind == LIR_MOVE_COPY && m->to_slot == i->call_save) {
                        return true;
                }
        }
        LirMove before = {
                .op = pc, .phase = LIR_MOVE_BEFORE,
                .from = reg, .to = reg, .cls = s->L->regs[reg].cls,
                .from_slot = LIR_NONE, .to_slot = i->call_save,
                .from_phys = phys, .to_phys = LIR_PHYS_NONE
        };
        LirMove after = {
                .op = pc, .phase = LIR_MOVE_AFTER,
                .from = reg, .to = reg, .cls = s->L->regs[reg].cls,
                .from_slot = i->call_save, .to_slot = LIR_NONE,
                .from_phys = LIR_PHYS_NONE, .to_phys = phys
        };
        return append_move(s, before) && append_move(s, after);
}

static bool
live_across(LirInterval const *i, u32 pc)
{
        return covers(i, 2 * pc) && covers(i, 2 * pc + 1);
}

static bool
survives(LirScan const *s, u32 r, u32 pc)
{
        LirInst const *in = &s->L->insts[pc];
        if (in->dst == r) {
                return false;
        }
        for (u32 o = 0; o < in->raw.nout; ++o) {
                if (in->raw.out[o].reg == r) {
                        return false;
                }
        }
        return live_across(&s->alloc->intervals[r], pc);
}

static bool
hints(LirScan *s)
{
        Lir const *L = s->L;
        u32 gp = 0;
        u32 fr = 0;
        u32 *calls = malloc(((usize)L->ninsts + 1) * sizeof *calls);
        u32 count = 0;
        if (calls == NULL) {
                return false;
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirOp op = L->insts[pc].op;
                if (op == LIR_CALL || op == LIR_TAILCALL || op == LIR_POLL) {
                        calls[count++] = pc;
                }
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                LirInterval *i = &s->alloc->intervals[r];
                for (u32 k = 0; k < i->nranges && !i->crosses_call; ++k) {
                        u32 first = (i->ranges[k].start + 1) / 2;
                        u32 end = i->ranges[k].end / 2;
                        u32 lo = 0;
                        u32 hi = count;
                        while (lo < hi) {
                                u32 mid = lo + (hi - lo) / 2;
                                if (calls[mid] < first) {
                                        lo = mid + 1;
                                } else {
                                        hi = mid;
                                }
                        }
                        while (lo < count && calls[lo] < end) {
                                if (survives(s, r, calls[lo++])) {
                                        i->crosses_call = true;
                                        break;
                                }
                        }
                }
        }
        free(calls);
        for (u32 p = 0; p < L->sig.nparams; ++p) {
                LirReg r = L->params[p];
                LirRegPool const *pool = fp(L->regs[r].cls) ? &s->target->fpr : &s->target->gpr;
                u32 a = fp(L->regs[r].cls) ? fr++ : gp++;
                if (a < pool->nargs) {
                        s->build[r].hint = pool->args[a];
                }
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                if (in->op == LIR_RET && in->nargs == 1 && in->args[0].kind == LIR_OPERAND_REG) {
                        u32 r = in->args[0].reg;
                        if (next_use(&s->alloc->intervals[r], 2 * pc + 1) == LIR_NONE) {
                                s->build[r].hint = fp(L->regs[r].cls)
                                                ? s->target->fpr.ret : s->target->gpr.ret;
                        }
                }
                if (in->op != LIR_CALL && in->op != LIR_TAILCALL) {
                        continue;
                }
                gp = 0;
                fr = 0;
                for (u32 p = 0; p < in->ncall_args; ++p) {
                        bool f = fp(lir_type_class(in->sig.params[p]));
                        LirRegPool const *pool = f ? &s->target->fpr : &s->target->gpr;
                        u32 a = f ? fr++ : gp++;
                        LirOpnd arg = in->call_args[p];
                        if (s->target->abi == LIR_ABI_APPLE_ARM64
                            && in->sig.variadic && p >= in->sig.nfixed) {
                                continue;
                        }
                        if (arg.kind == LIR_OPERAND_REG && a < pool->nargs
                            && next_use(&s->alloc->intervals[arg.reg], 2 * pc + 1) == LIR_NONE) {
                                s->build[arg.reg].hint = pool->args[a];
                        }
                }
        }
        return true;
}

typedef struct lir_order {
        u32 reg;
        u32 start;
} LirOrder;

static int
order_cmp(void const *a, void const *b)
{
        LirOrder const *x = a;
        LirOrder const *y = b;
        if (x->start != y->start) {
                return x->start < y->start ? -1 : 1;
        }
        return x->reg < y->reg ? -1 : x->reg != y->reg;
}

static bool
assign(LirScan *s)
{
        LirOrder *order = malloc(((usize)s->L->nregs + 1) * sizeof *order);
        u32 n = 0;
        if (order == NULL) {
                return false;
        }
        for (u32 r = 0; r < s->L->nregs; ++r) {
                LirInterval *i = &s->alloc->intervals[r];
                if (i->nranges != 0 && s->L->regs[r].pin == LIR_NONE) {
                        order[n++] = (LirOrder) { .reg = r, .start = i->ranges[0].start };
                }
        }
        qsort(order, n, sizeof *order, order_cmp);
        for (u32 o = 0; o < n; ++o) {
                u32 r = order[o].reg;
                LirInterval *cur = &s->alloc->intervals[r];
                bool f = fp(s->L->regs[r].cls);
                LirRegPool const *pool = f ? &s->target->fpr : &s->target->gpr;
                u64 free_regs = f ? s->fpr : s->gpr;
                u32 pos = order[o].start;
                u32 keep = 0;
                u8 chosen = LIR_PHYS_NONE;
                for (u32 a = 0; a < s->nactive; ++a) {
                        u32 v = s->active[a];
                        LirInterval const *i = &s->alloc->intervals[v];
                        if (i->spilled || i->ranges[i->nranges - 1].end <= pos) {
                                continue;
                        }
                        s->active[keep++] = v;
                        if (f == fp(s->L->regs[v].cls) && overlap(cur, i)) {
                                free_regs &= ~((u64)1 << i->phys);
                        }
                }
                s->nactive = keep;
                u64 preferred = cur->crosses_call ? free_regs & pool->callee_saved : free_regs;
                if (preferred == 0) {
                        preferred = free_regs;
                }
                u8 hint = s->build[r].hint;
                for (u32 pc = cur->ranges[0].start / 2; pc < s->L->ninsts && pc <= pos / 2; ++pc) {
                        LirInst const *in = &s->L->insts[pc];
                        if (in->dst == r && in->op == LIR_MOV && in->args[0].kind == LIR_OPERAND_REG) {
                                LirInterval const *src = &s->alloc->intervals[in->args[0].reg];
                                if (src->nranges != 0 && src->ranges[src->nranges - 1].end <= pos
                                    && src->phys != LIR_PHYS_NONE) {
                                        hint = src->phys;
                                }
                        }
                }
                for (u32 c = 0; c < s->alloc->nconstraints; ++c) {
                        LirConstraint const *constraint = &s->alloc->constraints[c];
                        if (constraint->reg == r && constraint->phys != LIR_PHYS_NONE) {
                                hint = constraint->phys;
                                break;
                        }
                        if (constraint->reg == r && constraint->tied < s->L->nregs) {
                                LirInterval const *src = &s->alloc->intervals[constraint->tied];
                                if (src->nranges != 0 && src->ranges[src->nranges - 1].end <= pos) {
                                        hint = src->phys;
                                }
                        }
                }
                if (hint < LIR_MAX_PHYS && ((preferred >> hint) & 1)) {
                        chosen = hint;
                } else if (preferred != 0) {
                        chosen = __builtin_ctzll(preferred);
                }
                if (chosen == LIR_PHYS_NONE) {
                        u32 victim = LIR_NONE;
                        u32 furthest = next_use(cur, pos);
                        for (u32 a = 0; a < s->nactive; ++a) {
                                u32 v = s->active[a];
                                LirInterval const *i = &s->alloc->intervals[v];
                                if (f != fp(s->L->regs[v].cls) || !overlap(cur, i)) {
                                        continue;
                                }
                                u32 use = next_use(i, pos);
                                bool unique = true;
                                for (u32 b = 0; b < s->nactive; ++b) {
                                        u32 w = s->active[b];
                                        LirInterval const *other = &s->alloc->intervals[w];
                                        if (w != v && other->phys == i->phys
                                            && fp(s->L->regs[w].cls) == f && overlap(cur, other)) {
                                                unique = false;
                                                break;
                                        }
                                }
                                if (unique && use > furthest) {
                                        victim = v;
                                        furthest = use;
                                }
                        }
                        if (victim == LIR_NONE) {
                                if (!spill(s, r)) {
                                        goto Error;
                                }
                                continue;
                        }
                        chosen = s->alloc->intervals[victim].phys;
                        if (!spill(s, victim)) {
                                goto Error;
                        }
                }
                cur->phys = chosen;
                s->active[s->nactive++] = r;
        }
        free(order);
        return true;
Error:
        free(order);
        return false;
}

static bool
call_moves(LirScan *s)
{
        u32 *regs = malloc(((usize)s->L->nregs + 1) * sizeof *regs);
        u32 count = 0;
        if (regs == NULL) {
                return false;
        }
        for (u32 r = 0; r < s->L->nregs; ++r) {
                if (s->alloc->intervals[r].crosses_call || s->L->regs[r].cls == LIR_REF) {
                        regs[count++] = r;
                }
        }
        for (u32 pc = 0; pc < s->L->ninsts; ++pc) {
                LirInst const *in = &s->L->insts[pc];
                bool call = in->op == LIR_CALL || in->op == LIR_TAILCALL || in->op == LIR_POLL;
                bool gc = (in->flags & (LIR_MAY_GC | LIR_MAY_THROW)) || in->op == LIR_POLL;
                if (!call && !gc) {
                        continue;
                }
                for (u32 k = 0; k < count; ++k) {
                        u32 r = regs[k];
                        LirInterval *i = &s->alloc->intervals[r];
                        LirRegInfo const *ri = &s->L->regs[r];
                        bool live = survives(s, r, pc);
                        bool root = gc && ri->cls == LIR_REF && covers(i, 2 * pc);
                        if (!live && !root) {
                                continue;
                        }
                        LirRegPool const *pool = fp(ri->cls) ? &s->target->fpr : &s->target->gpr;
                        if (live && call && i->phys != LIR_PHYS_NONE && ri->pin == LIR_NONE
                            && ((pool->callee_saved >> i->phys) & 1) == 0) {
                                if (!save_move(s, r, pc, i->phys)) {
                                        goto Error;
                                }
                        }
                        if (root) {
                                if (i->root_slot == LIR_NONE) {
                                        if (s->alloc->nvslots == LIR_NONE) {
                                                goto Error;
                                        }
                                        i->root_slot = s->alloc->nvslots++;
                                }
                                LirMove move = {
                                        .op = pc, .kind = LIR_MOVE_ROOT, .phase = LIR_MOVE_BEFORE,
                                        .from = r, .to = LIR_NONE, .cls = LIR_REF,
                                        .from_slot = i->spilled ? i->spill : LIR_NONE,
                                        .from_phys = i->phys, .to_slot = i->root_slot,
                                        .to_phys = LIR_PHYS_NONE
                                };
                                if (!append_move(s, move)) {
                                        goto Error;
                                }
                        }
                }
        }
        free(regs);
        return true;
Error:
        free(regs);
        return false;
}

static bool
fixed_move(LirScan *s, u32 r, u8 phys, bool output, u32 pc)
{
        LirInterval const *i = &s->alloc->intervals[r];
        LirMove move = {
                .op = pc, .phase = output ? LIR_MOVE_AFTER : LIR_MOVE_BEFORE,
                .from = r, .to = r, .cls = s->L->regs[r].cls,
                .from_slot = LIR_NONE, .to_slot = LIR_NONE,
                .from_phys = phys, .to_phys = i->phys
        };
        if (output) {
                move.to_slot = i->spilled ? i->spill : LIR_NONE;
        } else {
                move.from_phys = i->phys;
                move.to_phys = phys;
                move.from_slot = i->spilled ? i->spill : LIR_NONE;
        }
        if (move.from_slot == LIR_NONE && move.to_slot == LIR_NONE
            && move.from_phys == move.to_phys) {
                return true;
        }
        return append_move(s, move);
}

static bool
constraint_moves(LirScan *s)
{
        for (u32 pc = 0; pc < s->L->ninsts; ++pc) {
                u64 gp = s->L->insts[pc].raw.gpr_clobber;
                u64 fr = s->L->insts[pc].raw.fpr_clobber;
                for (u32 c = 0; c < s->alloc->nconstraints; ++c) {
                        LirConstraint const *con = &s->alloc->constraints[c];
                        if (con->op != pc || con->phys == LIR_PHYS_NONE) {
                                continue;
                        }
                        bool f = con->reg < s->L->nregs
                               ? fp(s->L->regs[con->reg].cls) : con->fpr;
                        if (f) {
                                fr |= (u64)1 << con->phys;
                        } else {
                                gp |= (u64)1 << con->phys;
                        }
                        if (con->reg == LIR_NONE) {
                                continue;
                        }
                        if (!fixed_move(s, con->reg, con->phys, con->output, pc)) {
                                return false;
                        }
                }
                LirRaw const *raw = &s->L->insts[pc].raw;
                for (u32 o = 0; o < raw->nin; ++o) {
                        u32 r = raw->in[o].reg;
                        if (fp(s->L->regs[r].cls)) {
                                fr |= (u64)1 << raw->in[o].phys;
                        } else {
                                gp |= (u64)1 << raw->in[o].phys;
                        }
                        if (!fixed_move(s, r, raw->in[o].phys, false, pc)) {
                                return false;
                        }
                }
                for (u32 o = 0; o < raw->nout; ++o) {
                        u32 r = raw->out[o].reg;
                        if (fp(s->L->regs[r].cls)) {
                                fr |= (u64)1 << raw->out[o].phys;
                        } else {
                                gp |= (u64)1 << raw->out[o].phys;
                        }
                        if (!fixed_move(s, r, raw->out[o].phys, true, pc)) {
                                return false;
                        }
                }
                if (gp == 0 && fr == 0) {
                        continue;
                }
                for (u32 r = 0; r < s->L->nregs; ++r) {
                        LirInterval const *i = &s->alloc->intervals[r];
                        u64 mask = fp(s->L->regs[r].cls) ? fr : gp;
                        if (i->phys == LIR_PHYS_NONE || !((mask >> i->phys) & 1)
                            || !survives(s, r, pc)) {
                                continue;
                        }
                        bool owner = false;
                        bool overwritten = ((fp(s->L->regs[r].cls)
                                             ? raw->fpr_clobber : raw->gpr_clobber) >> i->phys) & 1;
                        for (u32 c = 0; c < s->alloc->nconstraints; ++c) {
                                LirConstraint const *con = &s->alloc->constraints[c];
                                owner = owner || (con->op == pc && con->reg == r
                                                  && !con->output && con->phys == i->phys);
                                bool f = con->reg < s->L->nregs
                                       ? fp(s->L->regs[con->reg].cls) : con->fpr;
                                overwritten = overwritten || (con->op == pc && con->output
                                                 && con->phys == i->phys && f == fp(s->L->regs[r].cls));
                        }
                        for (u32 o = 0; o < raw->nout; ++o) {
                                overwritten = overwritten || (raw->out[o].phys == i->phys
                                                && fp(s->L->regs[raw->out[o].reg].cls)
                                                   == fp(s->L->regs[r].cls));
                        }
                        for (u32 o = 0; o < raw->nin; ++o) {
                                owner = owner || (raw->in[o].reg == r && raw->in[o].phys == i->phys);
                        }
                        if ((!owner || overwritten) && !save_move(s, r, pc, i->phys)) {
                                return false;
                        }
                }
        }
        return true;
}

static bool
frame(LirScan *s)
{
        u64 size = s->alloc->spill_size;
        u32 alignment = s->target->stack_align;
        for (u32 pc = 0; pc < s->L->ninsts; ++pc) {
                LirInst const *in = &s->L->insts[pc];
                if (in->op == LIR_ALLOCA) {
                        u32 a = in->args[1].imm;
                        size = (size + a - 1) & ~(u64)(a - 1);
                        if (size > UINT32_MAX) {
                                return false;
                        }
                        s->alloc->alloca_offsets[pc] = size;
                        size += in->args[0].imm;
                        if (a > alignment) {
                                alignment = a;
                        }
                }
        }
        size = (size + alignment - 1) & ~(u64)(alignment - 1);
        if (size > INT32_MAX) {
                return false;
        }
        s->alloc->frame_size = size;
        s->alloc->frame_align = alignment;
        for (u32 r = 0; r < s->L->nregs; ++r) {
                LirInterval const *i = &s->alloc->intervals[r];
                if (i->phys == LIR_PHYS_NONE) {
                        continue;
                }
                if (fp(s->L->regs[r].cls)) {
                        s->alloc->saved_fpr |= ((u64)1 << i->phys) & s->target->fpr.callee_saved;
                } else {
                        s->alloc->saved_gpr |= ((u64)1 << i->phys) & s->target->gpr.callee_saved;
                }
        }
        for (u32 c = 0; c < s->alloc->nconstraints; ++c) {
                LirConstraint const *con = &s->alloc->constraints[c];
                if (con->phys == LIR_PHYS_NONE) {
                        continue;
                }
                bool f = con->reg < s->L->nregs ? fp(s->L->regs[con->reg].cls) : con->fpr;
                if (f) {
                        s->alloc->saved_fpr |= ((u64)1 << con->phys) & s->target->fpr.callee_saved;
                } else {
                        s->alloc->saved_gpr |= ((u64)1 << con->phys) & s->target->gpr.callee_saved;
                }
        }
        for (u32 pc = 0; pc < s->L->ninsts; ++pc) {
                LirRaw const *raw = &s->L->insts[pc].raw;
                s->alloc->saved_gpr |= raw->gpr_clobber & s->target->gpr.callee_saved;
                s->alloc->saved_fpr |= raw->fpr_clobber & s->target->fpr.callee_saved;
                for (u32 k = 0; k < 2; ++k) {
                        LirRawBinding const *bindings = k == 0 ? raw->in : raw->out;
                        u32 n = k == 0 ? raw->nin : raw->nout;
                        for (u32 b = 0; b < n; ++b) {
                                u64 bit = (u64)1 << bindings[b].phys;
                                if (fp(s->L->regs[bindings[b].reg].cls)) {
                                        s->alloc->saved_fpr |= bit & s->target->fpr.callee_saved;
                                } else {
                                        s->alloc->saved_gpr |= bit & s->target->gpr.callee_saved;
                                }
                        }
                }
        }
        return true;
}

void
lir_alloc_free(LirAlloc *alloc)
{
        for (u32 i = 0; i < alloc->nintervals; ++i) {
                free(alloc->intervals[i].ranges);
                free(alloc->intervals[i].uses);
        }
        free(alloc->intervals);
        free(alloc->moves);
        free(alloc->alloca_offsets);
        free(alloc->constraints);
        *alloc = (LirAlloc) {0};
}

bool
lir_allocate(Lir const *L, LirCFG const *cfg, LirTarget const *target,
             LirConstraint const *constraints, u32 nconstraints,
             LirAlloc *alloc, LirError *err)
{
        LirScan s = { .L = L, .target = target, .alloc = alloc, .err = err };
        bool ok = false;
        *alloc = (LirAlloc) {0};
        if (err != NULL) {
                *err = (LirError) {0};
        }
        if (target == NULL || target->stack_align == 0
            || (target->stack_align & (target->stack_align - 1)) != 0
            || target->npins > LIR_MAX_PINS || L->ninsts >= UINT32_MAX / 2
            || (nconstraints != 0 && constraints == NULL)
            || (target->gpr.available >> LIR_MAX_PHYS) != 0
            || (target->fpr.available >> LIR_MAX_PHYS) != 0) {
                return ra_fail(err, LIR_ERROR_TARGET, LIR_NONE, "invalid allocation target or constraints");
        }
        alloc->intervals = calloc((usize)L->nregs + 1, sizeof *alloc->intervals);
        alloc->alloca_offsets = calloc((usize)L->ninsts + 1, sizeof *alloc->alloca_offsets);
        alloc->constraints = malloc(((usize)nconstraints + 1) * sizeof *alloc->constraints);
        s.build = calloc((usize)L->nregs + 1, sizeof *s.build);
        s.active = calloc((usize)L->nregs + 1, sizeof *s.active);
        if (alloc->intervals == NULL || alloc->alloca_offsets == NULL || alloc->constraints == NULL
            || s.build == NULL || s.active == NULL) {
                goto NoMemory;
        }
        alloc->nintervals = L->nregs;
        alloc->nconstraints = nconstraints;
        alloc->nvslots = L->nvslots;
        if (nconstraints != 0) {
                memcpy(alloc->constraints, constraints, nconstraints * sizeof *constraints);
        }
        s.gpr = target->gpr.available;
        s.fpr = target->fpr.available;
        for (u32 r = 0; r < L->nregs; ++r) {
                LirInterval *i = &alloc->intervals[r];
                *i = (LirInterval) {
                        .reg = r, .spill = LIR_NONE, .call_save = LIR_NONE,
                        .root_slot = LIR_NONE, .phys = LIR_PHYS_NONE
                };
                s.build[r].hint = LIR_PHYS_NONE;
                if (L->regs[r].pin != LIR_NONE) {
                        u32 p = L->regs[r].pin;
                        if (p >= target->npins || target->pins[p] >= LIR_MAX_PHYS) {
                                ra_fail(err, LIR_ERROR_TARGET, LIR_NONE, "pin is unavailable on this target");
                                goto End;
                        }
                        i->phys = target->pins[p];
                        s.gpr &= ~((u64)1 << i->phys);
                }
        }
        for (u32 c = 0; c < nconstraints; ++c) {
                LirConstraint const *con = &constraints[c];
                if (con->op >= L->ninsts || (con->reg != LIR_NONE && con->reg >= L->nregs)
                    || (con->phys != LIR_PHYS_NONE && con->phys >= LIR_MAX_PHYS)
                    || (con->tied != LIR_NONE && con->tied >= L->nregs)) {
                        ra_fail(err, LIR_ERROR_TARGET, con->op, "invalid fixed-register constraint");
                        goto End;
                }
        }
        if (!build_intervals(&s, cfg)) {
                goto NoMemory;
        }
        if (!hints(&s)) {
                goto NoMemory;
        }
        if (!assign(&s) || !call_moves(&s) || !constraint_moves(&s)) {
                goto NoMemory;
        }
        if (!frame(&s)) {
                ra_fail(err, LIR_ERROR_TARGET, LIR_NONE, "native frame is too large");
                goto End;
        }
        ok = true;
        goto End;
NoMemory:
        ra_fail(err, LIR_ERROR_MEMORY, LIR_NONE, "out of memory allocating LIR registers");
End:
        free(s.build);
        free(s.active);
        if (!ok) {
                lir_alloc_free(alloc);
        }
        return ok;
}

static bool
same_location(u32 aslot, u8 aphys, bool afp, u32 bslot, u8 bphys, bool bfp)
{
        if (aslot != LIR_NONE || bslot != LIR_NONE) {
                return aslot == bslot;
        }
        return aphys == bphys && afp == bfp;
}

static bool
from_fp(LirMove const *move)
{
        return fp(move->cls) && !move->from_gpr;
}

static bool
to_fp(LirMove const *move)
{
        return fp(move->cls) && !move->to_gpr;
}

bool
lir_parallel_moves(LirMove const *moves, u32 count, LirRegPool const *pool,
                   LirMove **out, u32 *nout, LirError *err)
{
        LirMove *pending = NULL;
        LirMove *result = NULL;
        u32 n = 0;
        u32 emitted = 0;
        u32 cap = 0;
        bool ok = false;
        *out = NULL;
        *nout = 0;
        if (pool == NULL || pool->nscratch == 0 || pool->scratch[0] >= LIR_MAX_PHYS
            || (count != 0 && moves == NULL)) {
                return ra_fail(err, LIR_ERROR_TARGET, LIR_NONE, "parallel moves need a scratch register");
        }
        pending = malloc(((usize)count + 1) * sizeof *pending);
        if (pending == NULL) {
                goto NoMemory;
        }
        for (u32 i = 0; i < count; ++i) {
                LirMove move = moves[i];
                if (move.kind != LIR_MOVE_COPY
                    || (move.from_slot == LIR_NONE && move.from_phys == LIR_PHYS_NONE)
                    || (move.to_slot == LIR_NONE && move.to_phys == LIR_PHYS_NONE)
                    || (move.from_slot == LIR_NONE && move.from_phys >= LIR_MAX_PHYS)
                    || (move.to_slot == LIR_NONE && move.to_phys >= LIR_MAX_PHYS)) {
                        ra_fail(err, LIR_ERROR_TARGET, move.op, "invalid parallel move location");
                        goto End;
                }
                if (!same_location(move.from_slot, move.from_phys, from_fp(&move),
                                   move.to_slot, move.to_phys, to_fp(&move))) {
                        pending[n++] = move;
                }
        }
        for (u32 i = 0; i < n; ++i) {
                for (u32 j = 0; j < i; ++j) {
                        if (same_location(pending[i].to_slot, pending[i].to_phys, to_fp(&pending[i]),
                                          pending[j].to_slot, pending[j].to_phys, to_fp(&pending[j]))) {
                                ra_fail(err, LIR_ERROR_TARGET, pending[i].op, "duplicate parallel move destination");
                                goto End;
                        }
                }
        }
        while (n != 0) {
                bool progress = false;
                for (u32 i = 0; i < n; ++i) {
                        bool needed = false;
                        for (u32 j = 0; j < n; ++j) {
                                if (j != i && same_location(pending[i].to_slot, pending[i].to_phys,
                                                           to_fp(&pending[i]), pending[j].from_slot,
                                                           pending[j].from_phys, from_fp(&pending[j]))) {
                                        needed = true;
                                        break;
                                }
                        }
                        if (!needed) {
                                if (!reserve(&result, &cap, emitted + 1, sizeof *result)) {
                                        goto NoMemory;
                                }
                                result[emitted++] = pending[i];
                                pending[i] = pending[--n];
                                progress = true;
                                break;
                        }
                }
                if (progress) {
                        continue;
                }
                LirMove save = pending[0];
                save.to_slot = LIR_NONE;
                save.to_phys = pool->scratch[0];
                save.to_gpr = fp(save.cls);
                for (u32 i = 0; i < n; ++i) {
                        if ((pending[i].from_slot == LIR_NONE && !from_fp(&pending[i])
                             && pending[i].from_phys == save.to_phys)
                            || (pending[i].to_slot == LIR_NONE && !to_fp(&pending[i])
                                && pending[i].to_phys == save.to_phys)) {
                                ra_fail(err, LIR_ERROR_TARGET, save.op, "parallel move uses its scratch register");
                                goto End;
                        }
                }
                if (!reserve(&result, &cap, emitted + 1, sizeof *result)) {
                        goto NoMemory;
                }
                result[emitted++] = save;
                for (u32 i = 0; i < n; ++i) {
                        if (same_location(pending[i].from_slot, pending[i].from_phys, from_fp(&pending[i]),
                                          save.from_slot, save.from_phys, from_fp(&save))) {
                                pending[i].from_slot = LIR_NONE;
                                pending[i].from_phys = save.to_phys;
                                pending[i].from_gpr = fp(pending[i].cls);
                        }
                }
        }
        *out = result;
        *nout = emitted;
        result = NULL;
        ok = true;
        goto End;
NoMemory:
        ra_fail(err, LIR_ERROR_MEMORY, LIR_NONE, "out of memory resolving parallel moves");
End:
        free(pending);
        free(result);
        return ok;
}

u8
lir_physical(LirAlloc const *alloc, LirReg reg, u32 op, bool output)
{
        for (u32 i = 0; i < alloc->nconstraints; ++i) {
                LirConstraint const *c = &alloc->constraints[i];
                if (c->op == op && c->reg == reg && c->output == output
                    && c->phys != LIR_PHYS_NONE) {
                        return c->phys;
                }
        }
        return alloc->intervals[reg].phys;
}

static bool
workspace_reg(LirScan *s, LirReg r, u32 pc, bool output, u64 *gp, u64 *fr, u32 *cap)
{
        LirInterval const *interval = &s->alloc->intervals[r];
        LirConstraint c = { .op = pc, .reg = r, .output = output, .tied = LIR_NONE };
        u8 phys;
        bool f;
        u64 available;
        u64 free_regs;
        if (!interval->spilled) {
                return true;
        }
        f = fp(s->L->regs[r].cls);
        phys = lir_physical(s->alloc, r, pc, output);
        if (phys != LIR_PHYS_NONE) {
                return true;
        }
        for (u32 i = 0; i < s->alloc->nconstraints; ++i) {
                LirConstraint const *other = &s->alloc->constraints[i];
                if (other->op == pc && other->reg == r && other->phys != LIR_PHYS_NONE) {
                        phys = other->phys;
                        break;
                }
        }
        if (phys == LIR_PHYS_NONE) {
                available = (f ? s->target->fpr.available : s->gpr) & ~(f ? *fr : *gp);
                free_regs = available;
                for (u32 i = 0; i < s->L->nregs; ++i) {
                        LirInterval const *v = &s->alloc->intervals[i];
                        if (v->phys != LIR_PHYS_NONE && fp(s->L->regs[i].cls) == f
                            && (covers(v, 2 * pc) || covers(v, 2 * pc + 1))) {
                                free_regs &= ~((u64)1 << v->phys);
                        }
                }
                if (available == 0) {
                        return false;
                }
                phys = free_regs != 0 ? __builtin_ctzll(free_regs) : 63 - __builtin_clzll(available);
                if (f) {
                        *fr |= (u64)1 << phys;
                } else {
                        *gp |= (u64)1 << phys;
                }
        }
        c.phys = phys;
        c.fpr = f;
        if (!reserve(&s->alloc->constraints, cap, s->alloc->nconstraints + 1,
                     sizeof *s->alloc->constraints)) {
                return false;
        }
        s->alloc->constraints[s->alloc->nconstraints++] = c;
        return true;
}

static void
occupy(LirScan const *s, LirReg r, u64 *gp, u64 *fr)
{
        u8 p = s->alloc->intervals[r].phys;
        if (p != LIR_PHYS_NONE) {
                if (fp(s->L->regs[r].cls)) {
                        *fr |= (u64)1 << p;
                } else {
                        *gp |= (u64)1 << p;
                }
        }
}

bool
lir_allocate_workspaces(Lir const *L, LirTarget const *target, LirAlloc *alloc, LirError *err)
{
        LirScan s = { .L = L, .target = target, .alloc = alloc, .err = err,
                      .gpr = target->gpr.available, .fpr = target->fpr.available,
                      .move_capacity = alloc->nmoves };
        u32 cap = alloc->nconstraints;
        for (u32 r = 0; r < L->nregs; ++r) {
                if (L->regs[r].pin != LIR_NONE) {
                        s.gpr &= ~((u64)1 << alloc->intervals[r].phys);
                }
        }
        for (u32 pc = 0; pc < L->ninsts; ++pc) {
                LirInst const *in = &L->insts[pc];
                u64 gp = 0;
                u64 fr = 0;
                if (in->op == LIR_CALL || in->op == LIR_TAILCALL
                    || in->op == LIR_POLL || in->op == LIR_RET || in->op == LIR_RAW) {
                        continue;
                }
                if (in->dst != LIR_NONE) {
                        occupy(&s, in->dst, &gp, &fr);
                }
                for (u32 j = 0; j < in->nargs; ++j) {
                        LirOpnd a = in->args[j];
                        if (a.kind == LIR_OPERAND_REG) {
                                occupy(&s, a.reg, &gp, &fr);
                        } else if (a.kind == LIR_OPERAND_MEM) {
                                occupy(&s, a.mem.base, &gp, &fr);
                                if (a.mem.index != LIR_NONE) {
                                        occupy(&s, a.mem.index, &gp, &fr);
                                }
                        }
                }
                for (u32 c = 0; c < alloc->nconstraints; ++c) {
                        LirConstraint const *con = &alloc->constraints[c];
                        if (con->op == pc && con->phys != LIR_PHYS_NONE) {
                                if (con->fpr || (con->reg < L->nregs && fp(L->regs[con->reg].cls))) {
                                        fr |= (u64)1 << con->phys;
                                } else {
                                        gp |= (u64)1 << con->phys;
                                }
                        }
                }
                for (u32 j = 0; j < in->nargs; ++j) {
                        LirOpnd a = in->args[j];
                        if (a.kind == LIR_OPERAND_REG) {
                                if (!workspace_reg(&s, a.reg, pc, false, &gp, &fr, &cap)) {
                                        goto Error;
                                }
                        } else if (a.kind == LIR_OPERAND_MEM) {
                                if (!workspace_reg(&s, a.mem.base, pc, false, &gp, &fr, &cap)) {
                                        goto Error;
                                }
                                if (a.mem.index != LIR_NONE
                                    && !workspace_reg(&s, a.mem.index, pc, false, &gp, &fr, &cap)) {
                                        goto Error;
                                }
                        }
                }
                if (in->dst != LIR_NONE
                    && !workspace_reg(&s, in->dst, pc, true, &gp, &fr, &cap)) {
                        goto Error;
                }
        }
        free(alloc->moves);
        alloc->moves = NULL;
        alloc->nmoves = 0;
        s.move_capacity = 0;
        if (!call_moves(&s) || !constraint_moves(&s) || !frame(&s)) {
                goto Error;
        }
        return true;
Error:
        return ra_fail(err, LIR_ERROR_TARGET, LIR_NONE, "could not assign native spill workspaces");
}
