#include <string.h>
#include <stdlib.h>
#include <limits.h>

#include "lir.h"

typedef struct lir_interval_build {
        u8 hint;
} LirIntervalBuild;

typedef struct lir_range_rec {
        u32 reg;
        u32 start;
        u32 end;
} LirRangeRec;

typedef struct lir_use_rec {
        u32 reg;
        u32 pc;
} LirUseRec;

typedef struct lir_constraint_index {
        u32 *at;
        u32 *last;
        u32 *next;
        u32 capacity;
} LirConstraintIndex;

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
        LirConstraintIndex *cindex;
        u64 *live_gp;
        u64 *live_fp;
        u64 *saved;
        u32 nsaved;
        u32 saved_cap;
        u32 *touched;
        u32 ntouched;
        u32 touched_cap;
        LirRangeRec *range_recs;
        u32 nrange_recs;
        u32 range_cap;
        LirUseRec *use_recs;
        u32 nuse_recs;
        u32 use_cap;
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

static void
constraint_index_free(LirConstraintIndex *index)
{
        free(index->at);
        free(index->last);
        free(index->next);
        *index = (LirConstraintIndex) {0};
}

static bool
constraint_index_add(LirConstraintIndex *index, u32 i, u32 pc)
{
        if (!reserve(&index->next, &index->capacity, i + 1, sizeof *index->next)) {
                return false;
        }
        index->next[i] = LIR_NONE;
        if (index->last[pc] == LIR_NONE) {
                index->at[pc] = i;
        } else {
                index->next[index->last[pc]] = i;
        }
        index->last[pc] = i;
        return true;
}

static bool
constraint_index_init(LirConstraintIndex *index, LirAlloc const *alloc, u32 n)
{
        *index = (LirConstraintIndex) {0};
        index->at = malloc(((usize)n + 1) * sizeof *index->at);
        index->last = malloc(((usize)n + 1) * sizeof *index->last);
        if (index->at == NULL || index->last == NULL) {
                goto Error;
        }
        for (u32 pc = 0; pc <= n; ++pc) {
                index->at[pc] = LIR_NONE;
                index->last[pc] = LIR_NONE;
        }
        for (u32 i = 0; i < alloc->nconstraints; ++i) {
                if (alloc->constraints[i].op < n
                    && !constraint_index_add(index, i, alloc->constraints[i].op)) {
                        goto Error;
                }
        }
        return true;
Error:
        constraint_index_free(index);
        return false;
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
        if (start >= end) {
                return true;
        }
        if (!reserve(&s->range_recs, &s->range_cap, s->nrange_recs + 1, sizeof *s->range_recs)) {
                return false;
        }
        s->range_recs[s->nrange_recs++] = (LirRangeRec) { .reg = r, .start = start, .end = end };
        s->alloc->intervals[r].nranges += 1;
        return true;
}

static bool
touch(LirScan *s, u32 r)
{
        if (!reserve(&s->touched, &s->touched_cap, s->ntouched + 1, sizeof *s->touched)) {
                return false;
        }
        s->touched[s->ntouched++] = r;
        return true;
}

static bool
add_use(LirScan *s, u32 r, u32 pc, u32 *ends)
{
        if (ends[r] == LIR_NONE) {
                ends[r] = pc + 1;
                if (!touch(s, r)) {
                        return false;
                }
        }
        if (!reserve(&s->use_recs, &s->use_cap, s->nuse_recs + 1, sizeof *s->use_recs)) {
                return false;
        }
        s->use_recs[s->nuse_recs++] = (LirUseRec) { .reg = r, .pc = pc };
        s->alloc->intervals[r].nuses += 1;
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

static bool
pool_intervals(LirScan *s)
{
        Lir const *L = s->L;
        LirAlloc *alloc = s->alloc;
        usize nr = 0;
        usize nu = 0;
        alloc->range_pool = malloc(((usize)s->nrange_recs + 1) * sizeof *alloc->range_pool);
        alloc->use_pool = malloc(((usize)s->nuse_recs + 1) * sizeof *alloc->use_pool);
        if (alloc->range_pool == NULL || alloc->use_pool == NULL) {
                return false;
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                LirInterval *i = &alloc->intervals[r];
                nr += i->nranges;
                nu += i->nuses;
                i->ranges = alloc->range_pool + nr;
                i->uses = alloc->use_pool + nu;
        }
        for (u32 k = 0; k < s->nrange_recs; ++k) {
                LirRangeRec const *rec = &s->range_recs[k];
                *--alloc->intervals[rec->reg].ranges = (LirRange) { .start = rec->start, .end = rec->end };
        }
        for (u32 k = 0; k < s->nuse_recs; ++k) {
                LirUseRec const *rec = &s->use_recs[k];
                *--alloc->intervals[rec->reg].uses = rec->pc;
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                LirInterval *i = &alloc->intervals[r];
                u32 n = 0;
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
                n = 0;
                for (u32 j = 0; j < i->nuses; ++j) {
                        if (n == 0 || i->uses[j] != i->uses[n - 1]) {
                                i->uses[n++] = i->uses[j];
                        }
                }
                i->nuses = n;
        }
        return true;
}

static bool
build_intervals(LirScan *s, LirCFG const *cfg)
{
        Lir const *L = s->L;
        u32 *ends = malloc(((usize)L->nregs + 1) * sizeof *ends);
        if (ends == NULL) {
                return false;
        }
        u32 nw = cfg->nwords;
        for (u32 r = 0; r < L->nregs; ++r) {
                ends[r] = LIR_NONE;
        }
        for (u32 b = cfg->nblocks; b-- > 0;) {
                LirBlock const *block = &cfg->blocks[b];
                s->ntouched = 0;
                for (u32 w = 0; w < nw; ++w) {
                        u64 bits = block->live_out[w];
                        while (bits != 0) {
                                u32 r = cfg->globals[w * 64 + (u32)__builtin_ctzll(bits)];
                                bits &= bits - 1;
                                ends[r] = 2 * block->end;
                                if (!touch(s, r)) {
                                        goto Error;
                                }
                        }
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
                for (u32 t = 0; t < s->ntouched; ++t) {
                        u32 r = s->touched[t];
                        if (ends[r] != LIR_NONE && !add_range(s, r, 2 * block->first, ends[r])) {
                                goto Error;
                        }
                        ends[r] = LIR_NONE;
                }
        }
        free(ends);
        return pool_intervals(s);
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
saved_grow(LirScan *s)
{
        u32 cap = s->saved_cap == 0 ? 64 : s->saved_cap * 2;
        u64 *table = calloc(cap, sizeof *table);
        if (table == NULL) {
                free(s->saved);
                s->saved = NULL;
                return false;
        }
        for (u32 j = 0; j < s->saved_cap; ++j) {
                u64 key = s->saved[j];
                if (key != 0) {
                        u32 h = (u32)((key * 0x9E3779B97F4A7C15ull) >> 32) & (cap - 1);
                        while (table[h] != 0) {
                                h = (h + 1) & (cap - 1);
                        }
                        table[h] = key;
                }
        }
        free(s->saved);
        s->saved = table;
        s->saved_cap = cap;
        return true;
}

static bool
saved_add(LirScan *s, u64 key)
{
        if ((s->nsaved + 1) * 2 > s->saved_cap && !saved_grow(s)) {
                return false;
        }
        u32 h = (u32)((key * 0x9E3779B97F4A7C15ull) >> 32) & (s->saved_cap - 1);
        while (s->saved[h] != 0) {
                if (s->saved[h] == key) {
                        return false;
                }
                h = (h + 1) & (s->saved_cap - 1);
        }
        s->saved[h] = key;
        s->nsaved += 1;
        return true;
}

static bool
save_move(LirScan *s, u32 reg, u32 pc, u8 phys)
{
        LirInterval *i = &s->alloc->intervals[reg];
        if (i->call_save == LIR_NONE && !slot(s, &i->call_save)) {
                return false;
        }
        if (!saved_add(s, ((u64)reg << 32 | pc) + 1)) {
                return s->saved != NULL;
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

static bool
sort_order(LirOrder *order, u32 n, u32 ninsts)
{
        usize limit = 2 * (usize)ninsts + 2;
        u32 *count;
        LirOrder *tmp;
        if (n < 2) {
                return true;
        }
        count = calloc(limit + 1, sizeof *count);
        tmp = malloc((usize)n * sizeof *tmp);
        if (count == NULL || tmp == NULL) {
                free(count);
                free(tmp);
                return false;
        }
        for (u32 k = 0; k < n; ++k) {
                count[order[k].start + 1] += 1;
        }
        for (usize k = 1; k <= limit; ++k) {
                count[k] += count[k - 1];
        }
        for (u32 k = 0; k < n; ++k) {
                tmp[count[order[k].start]++] = order[k];
        }
        memcpy(order, tmp, (usize)n * sizeof *order);
        free(count);
        free(tmp);
        return true;
}

static int
reg_cmp(void const *a, void const *b)
{
        u32 x = *(u32 const *)a;
        u32 y = *(u32 const *)b;
        return x < y ? -1 : x != y;
}

static bool
assign(LirScan *s)
{
        LirOrder *order = malloc(((usize)s->L->nregs + 1) * sizeof *order);
        u32 *chead = NULL;
        u32 *ctail = NULL;
        u32 *cnext = NULL;
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
        if (!sort_order(order, n, s->L->ninsts)) {
                free(order);
                return false;
        }
        chead = malloc(((usize)s->L->nregs + 1) * sizeof *chead);
        ctail = malloc(((usize)s->L->nregs + 1) * sizeof *ctail);
        cnext = malloc(((usize)s->alloc->nconstraints + 1) * sizeof *cnext);
        if (chead == NULL || ctail == NULL || cnext == NULL) {
                goto Error;
        }
        for (u32 r = 0; r < s->L->nregs; ++r) {
                chead[r] = LIR_NONE;
        }
        for (u32 c = 0; c < s->alloc->nconstraints; ++c) {
                u32 r = s->alloc->constraints[c].reg;
                cnext[c] = LIR_NONE;
                if (r >= s->L->nregs) {
                        continue;
                }
                if (chead[r] == LIR_NONE) {
                        chead[r] = c;
                } else {
                        cnext[ctail[r]] = c;
                }
                ctail[r] = c;
        }
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
                for (u32 c = chead[r]; c != LIR_NONE; c = cnext[c]) {
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
        free(chead);
        free(ctail);
        free(cnext);
        return true;
Error:
        free(order);
        free(chead);
        free(ctail);
        free(cnext);
        return false;
}

static bool
call_moves(LirScan *s)
{
        LirOrder *order = malloc(((usize)s->L->nregs + 1) * sizeof *order);
        u32 *live = malloc(((usize)s->L->nregs + 1) * sizeof *live);
        u32 *hits = malloc(((usize)s->L->nregs + 1) * sizeof *hits);
        u32 norder = 0;
        u32 nlive = 0;
        u32 next = 0;
        if (order == NULL || live == NULL || hits == NULL) {
                goto Error;
        }
        for (u32 r = 0; r < s->L->nregs; ++r) {
                LirInterval const *i = &s->alloc->intervals[r];
                if ((i->crosses_call || s->L->regs[r].cls == LIR_REF) && i->nranges != 0) {
                        order[norder++] = (LirOrder) { .reg = r, .start = i->ranges[0].start };
                }
        }
        if (!sort_order(order, norder, s->L->ninsts)) {
                goto Error;
        }
        for (u32 pc = 0; pc < s->L->ninsts; ++pc) {
                LirInst const *in = &s->L->insts[pc];
                bool call = in->op == LIR_CALL || in->op == LIR_TAILCALL || in->op == LIR_POLL;
                bool gc = (in->flags & (LIR_MAY_GC | LIR_MAY_THROW)) || in->op == LIR_POLL;
                if (!call && !gc) {
                        continue;
                }
                while (next < norder && order[next].start <= 2 * pc + 1) {
                        live[nlive++] = order[next++].reg;
                }
                u32 keep = 0;
                u32 nhits = 0;
                for (u32 a = 0; a < nlive; ++a) {
                        u32 r = live[a];
                        LirInterval const *i = &s->alloc->intervals[r];
                        if (i->ranges[i->nranges - 1].end <= 2 * pc) {
                                continue;
                        }
                        live[keep++] = r;
                        hits[nhits++] = r;
                }
                nlive = keep;
                if (nhits > 1) {
                        qsort(hits, nhits, sizeof *hits, reg_cmp);
                }
                for (u32 k = 0; k < nhits; ++k) {
                        u32 r = hits[k];
                        LirInterval *i = &s->alloc->intervals[r];
                        LirRegInfo const *ri = &s->L->regs[r];
                        bool live_here = survives(s, r, pc);
                        bool root = gc && ri->cls == LIR_REF && covers(i, 2 * pc);
                        if (!live_here && !root) {
                                continue;
                        }
                        LirRegPool const *pool = fp(ri->cls) ? &s->target->fpr : &s->target->gpr;
                        if (live_here && call && i->phys != LIR_PHYS_NONE && ri->pin == LIR_NONE
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
        free(order);
        free(live);
        free(hits);
        return true;
Error:
        free(order);
        free(live);
        free(hits);
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
        LirConstraintIndex own = {0};
        LirConstraintIndex *index = s->cindex;
        LirOrder *order = NULL;
        u32 *live = NULL;
        u32 *hits = NULL;
        u32 norder = 0;
        u32 nlive = 0;
        u32 next = 0;
        bool ok = false;
        if (index == NULL && s->alloc->nconstraints != 0) {
                if (!constraint_index_init(&own, s->alloc, s->L->ninsts)) {
                        goto End;
                }
                index = &own;
        }
        order = malloc(((usize)s->L->nregs + 1) * sizeof *order);
        live = malloc(((usize)s->L->nregs + 1) * sizeof *live);
        hits = malloc(((usize)s->L->nregs + 1) * sizeof *hits);
        if (order == NULL || live == NULL || hits == NULL) {
                goto End;
        }
        for (u32 r = 0; r < s->L->nregs; ++r) {
                LirInterval const *i = &s->alloc->intervals[r];
                if (i->phys != LIR_PHYS_NONE && i->nranges != 0) {
                        order[norder++] = (LirOrder) { .reg = r, .start = i->ranges[0].start };
                }
        }
        if (!sort_order(order, norder, s->L->ninsts)) {
                goto End;
        }
        for (u32 pc = 0; pc < s->L->ninsts; ++pc) {
                u64 gp = s->L->insts[pc].raw.gpr_clobber;
                u64 fr = s->L->insts[pc].raw.fpr_clobber;
                u32 first = index == NULL ? LIR_NONE : index->at[pc];
                for (u32 c = first; c != LIR_NONE; c = index->next[c]) {
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
                                goto End;
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
                                goto End;
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
                                goto End;
                        }
                }
                if (gp == 0 && fr == 0) {
                        continue;
                }
                while (next < norder && order[next].start <= 2 * pc) {
                        live[nlive++] = order[next++].reg;
                }
                u32 keep = 0;
                u32 nhits = 0;
                for (u32 a = 0; a < nlive; ++a) {
                        u32 r = live[a];
                        LirInterval const *i = &s->alloc->intervals[r];
                        if (i->ranges[i->nranges - 1].end <= 2 * pc + 1) {
                                continue;
                        }
                        live[keep++] = r;
                        u64 mask = fp(s->L->regs[r].cls) ? fr : gp;
                        if (((mask >> i->phys) & 1) && survives(s, r, pc)) {
                                hits[nhits++] = r;
                        }
                }
                nlive = keep;
                if (nhits > 1) {
                        qsort(hits, nhits, sizeof *hits, reg_cmp);
                }
                for (u32 h = 0; h < nhits; ++h) {
                        u32 r = hits[h];
                        LirInterval const *i = &s->alloc->intervals[r];
                        bool owner = false;
                        bool overwritten = ((fp(s->L->regs[r].cls)
                                             ? raw->fpr_clobber : raw->gpr_clobber) >> i->phys) & 1;
                        for (u32 c = first; c != LIR_NONE; c = index->next[c]) {
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
                                goto End;
                        }
                }
        }
        ok = true;
End:
        free(order);
        free(live);
        free(hits);
        constraint_index_free(&own);
        return ok;
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
        free(alloc->range_pool);
        free(alloc->use_pool);
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
        free(s.saved);
        free(s.touched);
        free(s.range_recs);
        free(s.use_recs);
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
        phys = interval->phys;
        u32 first = s->cindex->at[pc];
        for (u32 i = first; i != LIR_NONE; i = s->cindex->next[i]) {
                LirConstraint const *other = &s->alloc->constraints[i];
                if (other->reg == r && other->output == output && other->phys != LIR_PHYS_NONE) {
                        phys = other->phys;
                        break;
                }
        }
        if (phys != LIR_PHYS_NONE) {
                return true;
        }
        for (u32 i = first; i != LIR_NONE; i = s->cindex->next[i]) {
                LirConstraint const *other = &s->alloc->constraints[i];
                if (other->op == pc && other->reg == r && other->phys != LIR_PHYS_NONE) {
                        phys = other->phys;
                        break;
                }
        }
        if (phys == LIR_PHYS_NONE) {
                available = (f ? s->target->fpr.available : s->gpr) & ~(f ? *fr : *gp);
                free_regs = available;
                u64 *live = f ? s->live_fp : s->live_gp;
                free_regs &= ~(live[2 * pc] | live[2 * pc + 1]);
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
        u32 i = s->alloc->nconstraints;
        if (!constraint_index_add(s->cindex, i, pc)) {
                return false;
        }
        s->alloc->constraints[i] = c;
        ++s->alloc->nconstraints;
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
        if (alloc->spill_size == 0) {
                return true;
        }
        LirConstraintIndex index = {0};
        LirScan s = { .L = L, .target = target, .alloc = alloc, .err = err,
                      .gpr = target->gpr.available, .fpr = target->fpr.available,
                      .move_capacity = alloc->nmoves, .cindex = &index };
        bool ok = false;
        u32 cap = alloc->nconstraints;
        s.live_gp = calloc((usize)L->ninsts * 2 + 1, sizeof *s.live_gp);
        s.live_fp = calloc((usize)L->ninsts * 2 + 1, sizeof *s.live_fp);
        if (s.live_gp == NULL || s.live_fp == NULL
            || !constraint_index_init(&index, alloc, L->ninsts)) {
                goto Error;
        }
        for (u32 r = 0; r < L->nregs; ++r) {
                if (L->regs[r].pin != LIR_NONE) {
                        s.gpr &= ~((u64)1 << alloc->intervals[r].phys);
                }
                LirInterval const *interval = &alloc->intervals[r];
                if (interval->phys == LIR_PHYS_NONE) {
                        continue;
                }
                u64 *live = fp(L->regs[r].cls) ? s.live_fp : s.live_gp;
                for (u32 j = 0; j < interval->nranges; ++j) {
                        LirRange range = interval->ranges[j];
                        for (u32 pos = range.start; pos < range.end; ++pos) {
                                live[pos] |= (u64)1 << interval->phys;
                        }
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
                for (u32 c = index.at[pc]; c != LIR_NONE; c = index.next[c]) {
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
        ok = true;
        goto End;
Error:
        ra_fail(err, LIR_ERROR_TARGET, LIR_NONE, "could not assign native spill workspaces");
End:
        free(s.live_gp);
        free(s.live_fp);
        constraint_index_free(&index);
        return ok;
}
