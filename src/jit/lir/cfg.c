#include "impl.h"

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

inline static u32
target(Lir const *L, LirCFG const *cfg, LirLabel label)
{
        return cfg->block_at[v__(L->labels, label).pos];
}

static void
split(Ty *ty, Lir const *L, LirCFG *cfg)
{
        u32   n       = vN(L->insts);
        bool *leaders = stA0(bool, n + 1);

        leaders[0] = true;
        leaders[n] = true;

        vfor(L->labels, leaders[it->pos] = true);

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (isexit(in) || isbranch(in) || (in->flags & LIR_RETURNS_TWICE)) {
                        leaders[pc + 1] = true;
                }
                if (in->op == LIR_ENTRY) {
                        leaders[pc] = true;
                }
        }

        for (u32 pc = 0; pc <= n; ++pc) {
                cfg->nblocks += leaders[pc];
        }

        cfg->blocks   = stA0(LirBlock, cfg->nblocks);
        cfg->block_at = stA0(u32, n + 1);

        LirBlock *b = cfg->blocks;

        for (u32 pc = 1; pc <= n; ++pc) {
                if (leaders[pc]) {
                        b->end       = pc;
                        (++b)->first = pc;
                }
                cfg->block_at[pc] = b - cfg->blocks;
        }

        b->end = n;

        for (u32 l = 0; l < vN(L->labels); ++l) {
                if (v__(L->labels, l).entry) {
                        cfg->blocks[target(L, cfg, l)].entry = true;
                }
        }
}

static void
find_globals(Ty *ty, Lir const *L, LirCFG *cfg)
{
        u32  nregs = vN(L->regs);
        u32 *stamp = stA0(u32, nregs + 1);

        cfg->global  = stA(u32, nregs + 1);
        cfg->globals = stA(u32, nregs + 1);

        memset(cfg->global, 0xff, (nregs + 1) * sizeof *cfg->global);

        for (u32 i = 0; i < cfg->nblocks; ++i) {
                LirBlock const *b = &cfg->blocks[i];
                for (u32 pc = b->first; pc < b->end; ++pc) {
                        LirInst const *in = v_(L->insts, pc);
                        each_read(in, r) {
                                if (stamp[r] != i + 1) {
                                        cfg->global[r] = 0;
                                }
                        }
                        each_write(in, r) {
                                stamp[r] = i + 1;
                        }
                }
        }

        for (u32 r = 0; r < nregs; ++r) {
                if (cfg->global[r] != LIR_NONE) {
                        cfg->global[r] = cfg->nglobals;
                        cfg->globals[cfg->nglobals++] = r;
                }
        }
}

static void
summarize(LirCFG const *cfg, LirBlock *b, LirInst const *in)
{
        u32 const *global = cfg->global;

        each_read(in, r) {
                if (global[r] != LIR_NONE && !bhas(b->def, global[r])) {
                        bset(b->use, global[r]);
                }
        }

        each_write(in, r) {
                if (global[r] != LIR_NONE) {
                        bset(b->def, global[r]);
                }
        }
}

static void
connect(Ty *ty, Lir const *L, LirCFG *cfg, LirBlock *b)
{
        LirInst const *in = v_(L->insts, b->end - 1);

        b->succ = stA(u32, in->ntargets + 2);

        if (isbranch(in)) {
                b->succ[b->nsucc++] = target(L, cfg, in->args[in->nargs - 1].label);
                for (u32 j = 0; j < in->ntargets; ++j) {
                        b->succ[b->nsucc++] = target(L, cfg, in->targets[j]);
                }
        }

        if (falls(in)) {
                b->succ[b->nsucc++] = cfg->block_at[b->end];
        }
}

static void
chain(Ty *ty, Lir const *L, LirCFG *cfg)
{
        cfg->nwords = (cfg->nglobals + 63) / 64;

        u32 words = (cfg->nwords == 0) ? 1 : cfg->nwords;

        cfg->sets = stA0(u64, (usize)cfg->nblocks * words * 4);

        for (u32 i = 0; i < cfg->nblocks; ++i) {
                LirBlock *b = &cfg->blocks[i];

                b->use      = cfg->sets + (usize)i * words * 4;
                b->def      = b->use + words;
                b->live_in  = b->def + words;
                b->live_out = b->live_in + words;

                for (u32 pc = b->first; pc < b->end; ++pc) {
                        summarize(cfg, b, v_(L->insts, pc));
                }

                if (b->first != b->end) {
                        connect(ty, L, cfg, b);
                }
        }
}

static void
reach(Ty *ty, LirCFG *cfg)
{
        u32 *queue = stA(u32, cfg->nblocks);
        u32  head  = 0;
        u32  tail  = 0;

        for (u32 i = 0; i < cfg->nblocks; ++i) {
                if (i == 0 || cfg->blocks[i].entry) {
                        cfg->blocks[i].reachable = true;
                        queue[tail++] = i;
                }
        }

        while (head < tail) {
                LirBlock const *b = &cfg->blocks[queue[head++]];
                for (u32 j = 0; j < b->nsucc; ++j) {
                        LirBlock *next = &cfg->blocks[b->succ[j]];
                        if (!next->reachable) {
                                next->reachable = true;
                                queue[tail++]   = b->succ[j];
                        }
                }
        }
}

static bool
transfer(LirCFG const *cfg, LirBlock *b)
{
        bool changed = false;

        for (u32 w = 0; w < cfg->nwords; ++w) {
                u64 out = 0;

                for (u32 j = 0; j < b->nsucc; ++j) {
                        out |= cfg->blocks[b->succ[j]].live_in[w];
                }

                u64 in = b->use[w] | (out & ~b->def[w]);

                changed       |= (in != b->live_in[w]);
                b->live_in[w]  = in;
                b->live_out[w] = out;
        }

        return changed;
}

static void
liveness(Ty *ty, LirCFG *cfg)
{
        u32   nb    = cfg->nblocks;
        u32  *at    = stA0(u32, nb + 1);
        u32  *fill  = stA0(u32, nb);
        u32  *queue = stA(u32, nb);
        bool *inq   = stA0(bool, nb);

        for (u32 i = 0; i < nb; ++i) {
                LirBlock const *b = &cfg->blocks[i];
                for (u32 j = 0; j < b->nsucc; ++j) {
                        at[b->succ[j] + 1] += 1;
                }
        }

        for (u32 i = 0; i < nb; ++i) {
                at[i + 1] += at[i];
        }

        u32 *preds = stA(u32, at[nb] + 1);

        for (u32 i = 0; i < nb; ++i) {
                LirBlock const *b = &cfg->blocks[i];
                for (u32 j = 0; j < b->nsucc; ++j) {
                        u32 t = b->succ[j];
                        preds[at[t] + fill[t]++] = i;
                }
        }

        u32 head = 0;
        u32 tail = 0;

        for (u32 i = nb; i-- > 0;) {
                if (cfg->blocks[i].reachable) {
                        queue[tail++] = i;
                        inq[i]        = true;
                }
        }

        u32 pending = tail;

        tail %= nb;

#define next(i) (((i) + 1 == nb) ? 0 : (i) + 1)
        while (pending != 0) {
                u32 bi = queue[head];

                head     = next(head);
                pending -= 1;
                inq[bi]  = false;

                if (!transfer(cfg, &cfg->blocks[bi])) {
                        continue;
                }

                for (u32 j = at[bi]; j < at[bi + 1]; ++j) {
                        u32 p = preds[j];
                        if (!inq[p] && cfg->blocks[p].reachable) {
                                inq[p]       = true;
                                queue[tail]  = p;
                                tail         = next(tail);
                                pending     += 1;
                        }
                }
        }
#undef next
}

bool
lir_cfg(Ty *ty, Lir const *L, LirCFG *cfg, LirError *err)
{
        *cfg = (LirCFG) {0};
        ty   = lir_scratch(ty);

        if (relay(L, err) || !lir_check_labels(L, err)) {
                return false;
        }

        for (u32 pc = 0; !L->trusted && pc < vN(L->insts); ++pc) {
                if (!lir_check_inst(L, pc, err)) {
                        return false;
                }
        }

        split(ty, L, cfg);
        find_globals(ty, L, cfg);
        chain(ty, L, cfg);
        reach(ty, cfg);
        liveness(ty, cfg);

        return true;
}
