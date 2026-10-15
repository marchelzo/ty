#include <math.h>

#include "ty.h"
#include "jit/lir.h"

#if defined(__aarch64__) || defined(__x86_64__)

#define DASM_FDEF static
#define DASM_CHECKS
#include "../../../dynasm/dasm_proto.h"

#if defined(__aarch64__)
#include "../../../dynasm/dasm_arm64.h"
enum { TMP0 = 16, TMP1 = 17, FRAME = 29, TAIL_BASE = 9, TAIL_COPY = 10 };
static usize const Reach = 1u << 19;
#else
#define DASM_ALIGNED_WRITES
#include "../../../dynasm/dasm_x86.h"
enum { TMP0 = 10, TMP1 = 11, FRAME = 5, TAIL_BASE = 11, TAIL_COPY = 0 };
static usize const Reach = SIZE_MAX;
#endif

static bool
emit(Ty *ty, Lir const *L, LirAlloc const *alloc, LirCode *code, LirError *err);

static void
mem(dasm_State **Dst, bool w, u8 r, u8 base, i64 disp, u32 size, bool sign, bool fp);

inline static void
ld(dasm_State **Dst, u8 r, u8 base, i64 disp)
{
        mem(Dst, false, r, base, disp, 8, false, false);
}

inline static void
st(dasm_State **Dst, u8 r, u8 base, i64 disp)
{
        mem(Dst, true, r, base, disp, 8, false, false);
}

inline static LirConstraint
fix(u32 pc, LirReg reg, u8 phys, bool output, bool fpr)
{
        return (LirConstraint) {
                .op     = pc,
                .reg    = reg,
                .phys   = phys,
                .output = output,
                .fpr    = fpr,
                .tied   = LIR_NONE
        };
}

#if defined(__aarch64__)
#include "arm64.h"
#else
#include "x64.h"
#endif

#define Dst (&e->dasm)
#define tmp(T, n) ((T *)AllocateScratch(e->ty, (usize)(n) * sizeof (T)))
#define each(i, ch, h) for (u32 i = (ch).head[(h)]; i != LIR_NONE; i = (ch).next[i])

enum {
        MV_ALL,
        MV_SLOW,
        MV_FAST
};

typedef struct {
        u8      phys;
        bool    fpr;
        u32     stack;
        LirType type;
} ArgLoc;

typedef struct {
        u32 *head;
        u32 *next;
} Chain;

typedef struct {
        Ty              *ty;
        dasm_State      *dasm;
        void            *globals[1];
        Lir const       *L;
        LirAlloc const  *alloc;
        LirCode         *code;
        LirTarget const *target;
        LirError        *err;

        u32 outgoing;
        u32 incoming;
        u32 save_gp;
        u32 save_fp;
        u32 params;
        u32 origin;
        u32 pc_slot;
        u32 result;
        u32 ty_slot;
        u32 top_slot;
        u32 stack_base;
        u32 stack_end;
        u32 frame;

        u32 epilogue;
        u32 thunk;
        u32 literals;
        u32 sites;
        u32 rebased;
        u32 stubs;
        u32 edges;

        u32 nsites;
        u32 nentries;

        bool    context;
        bool    islands;
        LirReg  ty_vreg;
        ArgLoc *arguments;
        u32    *pointers;
        u32     npointers;
        Chain   labels;
        Chain   moves;
        Chain   constraints;
} Emit;

inline static u32
width(LirClass cls)
{
        return (cls == LIR_I32 || cls == LIR_F32) ? 4 : 8;
}

inline static bool
inmask(u8 mask, u32 pin)
{
        return (pin < 8) && ((mask >> pin) & 1);
}

inline static u32
argsize(LirType type)
{
        return (type == LT_VAL) ? 8 : lir_type_size(type);
}

inline static LirClass
rcls(Emit const *e, LirReg r)
{
        return v__(e->L->regs, r).cls;
}

inline static LirInterval const *
ival(Emit const *e, LirReg r)
{
        return &e->alloc->intervals[e->alloc->intervals[r].rep];
}

inline static LirLoc
loc(Emit const *e, LirReg r, u32 pos)
{
        return lir_where(e->alloc, r, pos);
}

inline static bool
covering(LirInterval const *i, u32 pos)
{
        if (
                (i->nranges == 0)
             || (pos < i->ranges[0].start)
             || (pos >= i->ranges[i->nranges - 1].end)
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

inline static u32
slot(Emit const *e, u32 spill)
{
        return e->outgoing + spill;
}

inline static u32
pslot(Emit const *e, u32 param)
{
        return e->params + 8 * param;
}

static Chain
chain(Ty *ty, u32 heads, u32 items)
{
        Chain ch = {
                .head = smA(heads * sizeof (u32)),
                .next = smA(items * sizeof (u32))
        };

        memset(ch.head, 0xff, heads * sizeof (u32));

        return ch;
}

inline static void
hook(Chain *ch, u32 head, u32 item)
{
        ch->next[item] = ch->head[head];
        ch->head[head] = item;
}

static void *
refptr(Value const *v)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_OBJECT: return v->object;
        case VALUE_TUPLE:  return v->items;
        case VALUE_STRING: return (v->str0 == NULL) ? (void *)v->str : v->str0;
        default:           return v->ptr;
        }
}

static u64
fbits(Lir const *L, LirInst const *in)
{
        double x = in->args[0].fimm;

        return (v__(L->regs, in->dst).cls == LIR_F32)
             ? (union { float  f; u32 u; }) { .f = x }.u
             : (union { double f; u64 u; }) { .f = x }.u;
}

static u32
locate(LirTarget const *target, LirSig const *sig, ArgLoc *args)
{
        bool apple   = (target->abi == LIR_ABI_APPLE_ARM64);
        u32  next[2] = { 0, 0 };
        u32  stack   = 0;

        for (u32 i = 0; i < sig->nparams; ++i) {
                LirType           type = sig->params[i];
                bool              f    = (type == LT_F32) || (type == LT_F64);
                bool              anon = sig->variadic && i >= sig->nfixed;
                LirRegPool const *pool = f ? &target->fpr : &target->gpr;

                args[i] = (ArgLoc) {
                        .phys  = LIR_PHYS_NONE,
                        .fpr   = f,
                        .stack = LIR_NONE,
                        .type  = type
                };

                if (next[f] < pool->nargs && !(apple && anon)) {
                        args[i].phys = pool->args[next[f]++];
                        continue;
                }

                u32 size  = argsize(type);
                u32 align = size;

                if (!apple || anon) {
                        size  = 8;
                        align = 8;
                }

                stack         = (stack + align - 1) & ~(align - 1);
                args[i].stack = stack;
                stack        += size;
        }

        return (stack + 15) & ~(u32)15;
}

static u32
outsize(Emit *e, LirSig const *sig)
{
        return locate(e->target, sig, tmp(ArgLoc, sig->nparams + 1));
}

static u32
nfloats(Emit const *e, LirSig const *sig)
{
        u32 n = 0;

        for (u32 i = 0; i < sig->nparams; ++i) {
                n += (sig->params[i] == LT_F32) || (sig->params[i] == LT_F64);
        }

        return (n < e->target->fpr.nargs) ? n : e->target->fpr.nargs;
}

static u8
physical(Emit const *e, LirReg r, u32 pc, bool output)
{
        if (r == LIR_NONE) {
                return LIR_PHYS_NONE;
        }

        each(i, e->constraints, pc) {
                LirConstraint const *c = &e->alloc->constraints[i];
                if (c->reg == r && c->output == output && c->phys != LIR_PHYS_NONE) {
                        return c->phys;
                }
        }

        return loc(e, r, output ? LIR_OUT(pc) : LIR_IN(pc)).phys;
}

static void
spill(Emit *e, bool write, u8 r, u32 s, LirClass cls, bool fp)
{
        mem(Dst, write, r, FRAME, slot(e, s), width(cls), false, fp);
}

static void
vslot(Emit *e, u8 d, u8 t, u32 index)
{
        ld(Dst, t, FRAME, e->ty_slot);
        vm_slots(Dst, d, t, e->top_slot);
        addr(Dst, d, d, ((i64)index - e->code->nvslots) * sizeof (Value));
}

static void
fetch(Emit *e, u8 d, LirLoc l, LirClass cls, bool gpr, u32 pos);

static void
reload(Emit *e, u8 d, LirInst const *in, bool gpr, u32 pos)
{
        LirMem             m    = in->args[0].mem;
        LirInterval const *bi   = ival(e, m.base);
        LirType            type = LirOps[in->op].type;
        LirLoc             b    = covering(bi, pos)
                                ? loc(e, m.base, pos)
                                : (LirLoc) { LIR_NONE, bi->remat, LIR_PHYS_NONE };
        u8                 base = b.phys;

        if (base == LIR_PHYS_NONE) {
                fetch(e, TMP1, b, LIR_PTR, true, pos);
                base = TMP1;
        }

        mem(
                Dst,
                false,
                d,
                base,
                m.disp,
                lir_type_size(type),
                type == LT_I8 || type == LT_I16 || type == LT_I32,
                isfloat(lir_type_class(type)) && !gpr
        );
}

static void
materialize(Emit *e, u8 d, u32 def, bool gpr, u32 pos)
{
        LirInst const *in  = v_(e->L->insts, def);
        LirClass       cls = rcls(e, in->dst);
        LirOpnd        x   = in->args[0];

        if (LirOps[in->op].form == LF_LD) {
                reload(e, d, in, gpr, pos);
                return;
        }

        switch (in->op) {
        case LIR_LI:
                li(Dst, d, (cls == LIR_I32) ? (u32)x.imm : (u64)x.imm);
                break;

        case LIR_FLI:
                if (gpr) {
                        li(Dst, d, fbits(e->L, in));
                } else if (!e->islands) {
                        fli(Dst, d, cls, e->literals + def);
                } else {
                        li(Dst, TMP0, fbits(e->L, in));
                        mov(Dst, d, TMP0, cls, true, false);
                }
                break;

        default:
                li(Dst, d, (x.kind == LO_CONST)
                        ? (uptr)&e->code->roots[x.index]
                        : (uptr)refptr(&e->code->roots[x.index]));
                break;
        }
}

static void
fetch(Emit *e, u8 d, LirLoc l, LirClass cls, bool gpr, u32 pos)
{
        bool f = isfloat(cls);

        if (l.remat != LIR_NONE) {
                materialize(e, d, l.remat, gpr || !f, pos);
        } else if (l.slot != LIR_NONE) {
                spill(e, false, d, l.slot, cls, f && !gpr);
        } else {
                mov(Dst, d, l.phys, cls, false, f && gpr);
        }
}

static void
put(Emit *e, u8 r, LirLoc l, LirClass cls)
{
        if (l.slot != LIR_NONE) {
                spill(e, true, r, l.slot, cls, isfloat(cls));
        } else if (l.phys != LIR_PHYS_NONE) {
                mov(Dst, l.phys, r, cls, false, false);
        }
}

static u32
movepos(LirMove const *m)
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

static void
move(Emit *e, LirMove const *m)
{
        bool f = isfloat(m->cls);

        if (m->remat != LIR_NONE && m->to_slot != LIR_NONE) {
                materialize(e, TMP0, m->remat, true, movepos(m));
                spill(e, true, TMP0, m->to_slot, m->cls, false);
        } else if (m->remat != LIR_NONE) {
                materialize(e, m->to_phys, m->remat, !f || m->to_gpr, movepos(m));
        } else if (m->from_slot != LIR_NONE) {
                spill(e, false, m->to_phys, m->from_slot, m->cls, f && !m->to_gpr);
        } else if (m->to_slot != LIR_NONE) {
                spill(e, true, m->from_phys, m->to_slot, m->cls, f && !m->from_gpr);
        } else {
                mov(Dst, m->to_phys, m->from_phys, m->cls, m->from_gpr, m->to_gpr);
        }
}

static void
rootmove(Emit *e, LirMove const *m)
{
        u8 src = m->from_phys;

        vslot(e, TMP0, TMP1, m->to_slot);

        if (m->remat != LIR_NONE) {
                materialize(e, TMP1, m->remat, true, movepos(m));
                src = TMP1;
        } else if (m->from_slot != LIR_NONE) {
                ld(Dst, TMP1, FRAME, slot(e, m->from_slot));
                src = TMP1;
        }

        zero(Dst, TMP0);
        st(Dst, src, TMP0, offsetof(Value, ptr));
        st(Dst, src, TMP0, offsetof(Value, gcptr));
        li(Dst, TMP1, (uptr)&LirRefRoot);
        st(Dst, TMP1, TMP0, offsetof(Value, extra));
        li(Dst, TMP1, VALUE_PTR);
        mem(Dst, true, TMP1, TMP0, offsetof(Value, type), 1, false, false);
}

static bool
shuffle(Emit *e, LirMove const *moves, u32 n)
{
        Ty               *ty  = e->ty;
        LirRegPool const *gpr = &e->target->gpr;
        LirMove          *ordered;
        u32               count;

        SCRATCH_SAVE();

        bool ok = lir_parallel_moves(ty, moves, n, gpr, &ordered, &count, e->err);

        for (u32 i = 0; ok && i < count; ++i) {
                move(e, &ordered[i]);
        }

        SCRATCH_RESTORE();

        return ok;
}

static bool
phase(Emit *e, u32 pc, LirMovePhase when, u32 edge, int mode)
{
        u32 n = 0;

        each(i, e->moves, pc) {
                n += 1;
        }

        if (n == 0) {
                return true;
        }

        LirMove        *moves = tmp(LirMove, n);
        LirMove const **roots = tmp(LirMove const *, n);
        u32             nroot = 0;

        n = 0;

        each(i, e->moves, pc) {
                LirMove const *m = &e->alloc->moves[i];
                if (
                        (m->phase != when)
                     || (edge != LIR_NONE && m->edge != edge)
                     || (mode != MV_ALL && m->slow != (mode == MV_SLOW))
                ) {
                        continue;
                }
                if (m->kind == LIR_MOVE_ROOT) {
                        roots[nroot++] = m;
                } else {
                        moves[n++] = *m;
                }
        }

        if (!shuffle(e, moves, n)) {
                return false;
        }

        for (u32 i = 0; i < nroot; ++i) {
                rootmove(e, roots[i]);
        }

        return true;
}

static bool
before(Emit *e, u32 pc, int mode)
{
        return phase(e, pc, LIR_MOVE_BEFORE, LIR_NONE, mode)
            && phase(e, pc, LIR_MOVE_PIN, LIR_NONE, MV_ALL);
}

static bool
after(Emit *e, u32 pc)
{
        return phase(e, pc, LIR_MOVE_AFTER, LIR_NONE, MV_ALL);
}

static bool
leave(Emit *e, u32 pc)
{
        return phase(e, pc, LIR_MOVE_EDGE_OUT, LIR_NONE, MV_ALL);
}

static u32
dest(Emit *e, u32 pc, LirLabel label)
{
        u32 at = v__(e->L->labels, label).pos;

        each(i, e->moves, pc) {
                LirMove const *m = &e->alloc->moves[i];
                if (m->phase == LIR_MOVE_STUB && m->edge == at) {
                        return e->edges + m->stub;
                }
        }

        return label;
}

static void
home(Emit *e, LirReg r, u32 pc, u8 dest, LirType type)
{
        LirClass cls = rcls(e, r);

        fetch(e, dest, loc(e, r, LIR_IN(pc)), cls, false, LIR_IN(pc));

        if (!isfloat(cls)) {
                fit(Dst, dest, type);
        }
}

static bool
pass(Emit *e, LirInst const *in, u32 pc)
{
        ArgLoc  *args  = tmp(ArgLoc, in->ncall_args + 1);
        LirMove *moves = tmp(LirMove, in->ncall_args + 1);
        u32      n     = 0;

        locate(e->target, &in->sig, args);

        for (u32 p = 0; p < in->ncall_args; ++p) {
                if (in->call_args[p].kind == LO_IMM) {
                        continue;
                }

                LirReg   r    = in->call_args[p].reg;
                LirType  type = in->sig.params[p];
                LirClass cls  = rcls(e, r);
                LirLoc   l    = loc(e, r, LIR_IN(pc));
                bool     f    = isfloat(cls);

                if (args[p].phys != LIR_PHYS_NONE) {
                        moves[n++] = (LirMove) {
                                .op        = pc,
                                .from      = r,
                                .to        = r,
                                .cls       = cls,
                                .from_slot = l.slot,
                                .remat     = l.remat,
                                .to_slot   = LIR_NONE,
                                .from_phys = l.phys,
                                .to_phys   = args[p].phys
                        };
                        continue;
                }

                u8   src = l.phys;
                bool fpr = f;

                if (l.phys == LIR_PHYS_NONE || (!f && type == LT_BOOL)) {
                        fetch(e, TMP0, l, cls, true, LIR_IN(pc));
                        if (!f) {
                                fit(Dst, TMP0, type);
                        }
                        src = TMP0;
                        fpr = false;
                }

                mem(Dst, true, src, FRAME, args[p].stack, argsize(type), false, fpr);
        }

        if (!shuffle(e, moves, n)) {
                return false;
        }

        for (u32 p = 0; p < in->ncall_args; ++p) {
                if (in->call_args[p].kind != LO_IMM) {
                        continue;
                }

                if (args[p].phys != LIR_PHYS_NONE) {
                        li(Dst, args[p].phys, in->call_args[p].imm);
                } else {
                        li(Dst, TMP0, in->call_args[p].imm);
                        mem(Dst, true, TMP0, FRAME, args[p].stack, argsize(in->sig.params[p]), false, false);
                }
        }

        for (u32 p = 0; p < in->ncall_args; ++p) {
                if (args[p].phys != LIR_PHYS_NONE && !args[p].fpr) {
                        fit(Dst, args[p].phys, in->sig.params[p]);
                }
        }

        return true;
}

static bool
liveptr(Emit const *e, u32 r, u32 pc)
{
        LirInst const *in = v_(e->L->insts, pc);

        if (
                (rcls(e, r) != LIR_PTR)
             || ((in->op == LIR_CALL) && (in->dst != LIR_NONE) && (ival(e, in->dst)->reg == r))
        ) {
                return false;
        }

        return covering(ival(e, r), LIR_OUT(pc));
}

static bool
shifts(Emit const *e, u32 pc)
{
        LirInst const *in   = v_(e->L->insts, pc);
        u32            gcky = LIR_MAY_GC | LIR_MAY_THROW | LIR_RETURNS_TWICE;

        return (e->L->resolved_mode == LIR_MODE_ATTACHED)
            && (in->op == LIR_POLL || (in->op == LIR_CALL && (in->flags & gcky)));
}

static bool
anyptr(Emit const *e, u32 pc, bool heap)
{
        for (u32 k = 0; k < e->npointers; ++k) {
                u32 r = e->pointers[k];
                if ((!heap || !ival(e, r)->stackish) && liveptr(e, r, pc)) {
                        return true;
                }
        }

        return false;
}

static bool
rebases(Emit const *e, u32 pc)
{
        return shifts(e, pc) && anyptr(e, pc, false);
}

static bool
unsure(Emit const *e, u32 pc)
{
        return anyptr(e, pc, true);
}

static u8
tyreg(Emit const *e, u32 pos)
{
        if (e->ty_vreg == LIR_NONE || !covering(ival(e, e->ty_vreg), pos)) {
                return LIR_PHYS_NONE;
        }

        return loc(e, e->ty_vreg, pos).phys;
}

static void
items(Emit *e, u8 d, u32 pos)
{
        u8 t = tyreg(e, pos);

        if (t != LIR_PHYS_NONE) {
                ld(Dst, d, t, offsetof(Ty, stack.items));
        } else {
                ld(Dst, d, FRAME, e->ty_slot);
                ld(Dst, d, d, offsetof(Ty, stack.items));
        }
}

static void
bounds(Emit *e, u32 pc)
{
        if (!rebases(e, pc) || !unsure(e, pc)) {
                return;
        }

        u8 t = tyreg(e, LIR_IN(pc));

        if (t == LIR_PHYS_NONE) {
                stack_bounds(Dst, e->ty_slot, e->stack_base, e->stack_end);
                return;
        }

        ld(Dst, TMP0, t, offsetof(Ty, stack.capacity));
        ld(Dst, TMP1, t, offsetof(Ty, stack.items));
        alui(Dst, LIR_SHL, TMP0, TMP0, 5, false);
        alu(Dst, LIR_ADD, TMP0, TMP0, TMP1, false);
        st(Dst, TMP0, FRAME, e->stack_end);
}

static void
slide(Emit *e, u32 pc)
{
        for (u32 k = 0; k < e->npointers; ++k) {
                u32 r = e->pointers[k];

                if (!ival(e, r)->stackish || !liveptr(e, r, pc)) {
                        continue;
                }

                LirLoc l = loc(e, r, LIR_OUT(pc));

                if (l.slot != LIR_NONE) {
                        ld(Dst, TMP1, FRAME, slot(e, l.slot));
                        alu(Dst, LIR_ADD, TMP1, TMP1, TMP0, false);
                        st(Dst, TMP1, FRAME, slot(e, l.slot));
                } else if (l.phys != LIR_PHYS_NONE) {
                        alu(Dst, LIR_ADD, l.phys, l.phys, TMP0, false);
                }
        }
}

static void
chase(Emit *e, u32 pc)
{
        for (u32 k = 0; k < e->npointers; ++k) {
                u32 r = e->pointers[k];

                if (ival(e, r)->stackish || !liveptr(e, r, pc)) {
                        continue;
                }

                LirLoc l = loc(e, r, LIR_OUT(pc));
                u8     p = (l.slot != LIR_NONE) ? TMP1 : l.phys;

                if (l.remat != LIR_NONE || p == LIR_PHYS_NONE) {
                        continue;
                }

                if (l.slot != LIR_NONE) {
                        ld(Dst, p, FRAME, slot(e, l.slot));
                }

                rebase_pointer(Dst, p, e->ty_slot, e->stack_base, e->stack_end);

                if (l.slot != LIR_NONE) {
                        mov(Dst, TMP0, p, LIR_PTR, false, false);
                        st(Dst, TMP0, FRAME, slot(e, l.slot));
                }
        }
}

static void
rebase(Emit *e, u32 pc)
{
        if (!rebases(e, pc)) {
                if (e->context && shifts(e, pc)) {
                        items(e, TMP0, LIR_OUT(pc));
                        st(Dst, TMP0, FRAME, e->stack_base);
                }
                return;
        }

        items(e, TMP0, LIR_OUT(pc));
        rebase_check(Dst, e->stack_base, e->stubs + pc);
        label(Dst, e->rebased + pc);
        cold(Dst);
        label(Dst, e->stubs + pc);

        if (unsure(e, pc)) {
                chase(e, pc);
                rebase_delta(Dst, e->ty_slot, e->stack_base);
                slide(e, pc);
                items(e, TMP0, LIR_OUT(pc));
                st(Dst, TMP0, FRAME, e->stack_base);
        } else {
                st(Dst, TMP0, FRAME, e->stack_base);
                alu(Dst, LIR_SUB, TMP0, TMP0, TMP1, false);
                slide(e, pc);
        }

        jump(Dst, e->rebased + pc);
        hot(Dst);
}

static void
bank(Emit *e, bool write, u64 mask, u32 off, bool fp)
{
        for (u32 r = 0; r < 32; ++r) {
                if ((mask >> r) & 1) {
                        mem(Dst, write, r, FRAME, off, 8, false, fp);
                        off += 8;
                }
        }
}

static void
saveregs(Emit *e, bool write)
{
        bank(e, write, e->alloc->saved_gpr, e->save_gp, false);
        bank(e, write, e->alloc->saved_fpr, e->save_fp, true);
}

static bool
tail(Emit *e, LirInst const *in)
{
        u32 out = outsize(e, &in->sig);

        if (out > e->incoming) {
                return false;
        }

        if (out != 0) {
                ld(Dst, TAIL_BASE, FRAME, e->origin);
                for (u32 i = 0; i < out; i += 8) {
                        ld(Dst, TAIL_COPY, FRAME, i);
                        st(Dst, TAIL_COPY, TAIL_BASE, 16 + i);
                }
                if (in->sig.variadic) {
                        varargs(Dst, nfloats(e, &in->sig));
                }
        }

        saveregs(e, false);
        epilogue(Dst, e->origin, true);

        return true;
}

static bool
invoke(Emit *e, LirInst const *in, u32 pc)
{
        LirOpnd fn    = in->args[0];
        u64     where = 0;
        u32     twin  = LIR_RETURNS_TWICE | LIR_CALL_SITE;
        bool    site  = (in->flags & LIR_CALL_SITE) != 0;

        bounds(e, pc);

        switch (fn.kind) {
        case LO_REG:
                home(e, fn.reg, pc, TMP0, LT_PTR);
                st(Dst, TMP0, FRAME, e->result);
                break;

        case LO_IMM:    where = fn.imm;                    break;
        case LO_CODE:   where = (uptr)fn.code->body;       break;
        case LO_HELPER: where = (uptr)fn.helper->address;  break;
        }

        if (!pass(e, in, pc)) {
                return false;
        }

        if (in->sig.variadic) {
                varargs(Dst, nfloats(e, &in->sig));
        }

        if (fn.kind == LO_REG) {
                ld(Dst, TMP0, FRAME, e->result);
        } else {
                li(Dst, TMP0, where);
        }

        if (in->op == LIR_TAILCALL && !site && tail(e, in)) {
                return true;
        }

        if ((in->flags & twin) == twin) {
                twice(Dst, e->pc_slot, e->sites + pc);
        } else {
                call(Dst, site, e->thunk, e->pc_slot);
        }

        if (site) {
                label(Dst, e->sites + pc);
        }

        if (
                (in->sig.ret != LT_VOID)
             && !isfloat(lir_type_class(in->sig.ret))
        ) {
                fit(Dst, 0, (in->sig.ret == LT_BOOL) ? LT_U8 : in->sig.ret);
        }

        if (in->dst != LIR_NONE) {
                put(e, 0, loc(e, in->dst, LIR_OUT(pc)), rcls(e, in->dst));
        }

        if (
                e->code->entry_thunk
             && (fn.kind == LO_IMM)
             && ((uptr)fn.imm == (uptr)lir_runtime()->reserve)
        ) {
                ld(Dst, TMP0, FRAME, e->ty_slot);
                ld(Dst, TMP0, TMP0, offsetof(Ty, stack.count));
                addr(Dst, TMP0, TMP0, -(i64)e->code->entry_body_slots);
                st(Dst, TMP0, FRAME, e->top_slot);
        }

        if (in->op == LIR_TAILCALL) {
                jump(Dst, e->epilogue);
        }

        return true;
}

static void
incoming(Emit *e, u8 d, u32 p, bool fpr)
{
        ArgLoc a = e->arguments[p];

        ld(Dst, TMP1, FRAME, e->origin);
        mem(Dst, false, d, TMP1, 16 + a.stack, argsize(a.type), false, fpr);
}

static bool
spilled_params(Emit *e)
{
        Lir const *L = e->L;

        for (u32 p = 0; p < L->sig.nparams; ++p) {
                ArgLoc a    = e->arguments[p];
                u32    size = (a.type == LT_F32) ? 4 : 8;
                if (a.phys != LIR_PHYS_NONE) {
                        mem(Dst, true, a.phys, FRAME, pslot(e, p), size, false, a.fpr);
                } else {
                        incoming(e, TMP0, p, false);
                        st(Dst, TMP0, FRAME, pslot(e, p));
                }
        }

        li(Dst, TMP0, (uptr)lir_runtime()->current_ty);
        call(Dst, false, e->thunk, e->pc_slot);
        st(Dst, 0, FRAME, e->ty_slot);
        ld(Dst, TMP0, 0, offsetof(Ty, stack.count));
        st(Dst, TMP0, FRAME, e->top_slot);
        ld(Dst, TMP0, 0, offsetof(Ty, stack.items));
        st(Dst, TMP0, FRAME, e->stack_base);

        for (u32 p = 0; p < L->sig.nparams; ++p) {
                e->arguments[p].phys = LIR_PHYS_NONE;
        }

        return true;
}

static void
context(Emit *e)
{
        Lir const *L = e->L;
        ArgLoc     a = e->arguments[L->ty_param];
        u8         t = a.phys;

        if (t == LIR_PHYS_NONE) {
                incoming(e, TMP0, L->ty_param, false);
                t = TMP0;
        }

        st(Dst, t, FRAME, e->ty_slot);
        ld(Dst, TMP1, t, offsetof(Ty, stack.count));
        st(Dst, TMP1, FRAME, e->top_slot);
        ld(Dst, TMP1, t, offsetof(Ty, stack.items));
        st(Dst, TMP1, FRAME, e->stack_base);
}

static bool
receive(Emit *e)
{
        Lir const *L       = e->L;
        bool       typaram = (L->ty_param != LIR_NONE) && (L->ty_param < L->sig.nparams);
        bool       saved   = e->context && !typaram;
        LirMove   *moves   = tmp(LirMove, vN(L->regs) + 1);
        bool      *done    = tmp(bool, vN(L->regs) + 1);
        u32        n       = 0;

        memset(done, 0, vN(L->regs) + 1);

        if (saved) {
                spilled_params(e);
        } else if (e->context) {
                context(e);
        }

        if (L->pc_param != LIR_NONE) {
                ArgLoc a = e->arguments[L->pc_param];
                u8     d = a.phys;
                if (saved) {
                        ld(Dst, TMP0, FRAME, pslot(e, L->pc_param));
                        d = TMP0;
                } else if (d == LIR_PHYS_NONE) {
                        incoming(e, TMP0, L->pc_param, false);
                        d = TMP0;
                }
                addr(Dst, TMP1, FRAME, e->pc_slot);
                st(Dst, TMP1, d, 0);
        }

        for (u32 p = 0; p < L->sig.nparams && !saved; ++p) {
                ArgLoc a = e->arguments[p];
                if (a.phys != LIR_PHYS_NONE && !a.fpr) {
                        fit(Dst, a.phys, a.type);
                }
        }

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirRegInfo const  *ri = v_(L->regs, r);
                LirInterval const *i  = ival(e, r);

                if (ri->param == LIR_NONE || done[i->reg] || !covering(i, 0)) {
                        continue;
                }

                LirLoc to = loc(e, r, 0);
                ArgLoc a  = e->arguments[ri->param];

                if (a.phys == LIR_PHYS_NONE || (to.phys == LIR_PHYS_NONE && to.slot == LIR_NONE)) {
                        continue;
                }

                done[i->reg] = true;

                moves[n++] = (LirMove) {
                        .from      = r,
                        .to        = r,
                        .cls       = ri->cls,
                        .from_slot = LIR_NONE,
                        .to_slot   = to.slot,
                        .remat     = LIR_NONE,
                        .from_phys = a.phys,
                        .to_phys   = to.phys
                };
        }

        if (!shuffle(e, moves, n)) {
                return false;
        }

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirRegInfo const  *ri = v_(L->regs, r);
                LirInterval const *i  = ival(e, r);

                if (ri->param == LIR_NONE || done[i->reg] || !covering(i, 0)) {
                        continue;
                }

                done[i->reg] = true;

                LirLoc to   = loc(e, r, 0);
                ArgLoc a    = e->arguments[ri->param];
                bool   f    = isfloat(ri->cls);
                u32    size = (ri->cls == LIR_F32) ? 4 : 8;

                if (a.phys != LIR_PHYS_NONE || (to.phys == LIR_PHYS_NONE && to.slot == LIR_NONE)) {
                        continue;
                }

                bool reg = (to.phys != LIR_PHYS_NONE);
                u8   d   = reg ? to.phys : TMP0;

                if (saved) {
                        mem(Dst, false, d, FRAME, pslot(e, ri->param), size, false, f && reg);
                } else {
                        incoming(e, d, ri->param, f && reg);
                }

                if (!f) {
                        fit(Dst, d, L->sig.params[ri->param]);
                }

                if (to.slot != LIR_NONE) {
                        mem(Dst, true, d, FRAME, slot(e, to.slot), size, false, false);
                }
        }

        return true;
}

static bool
safepoint(Emit *e, LirInst const *in, u32 pc, u32 fast, u32 end)
{
        LirRuntime const *rt   = lir_runtime();
        u8 const         *args = e->target->gpr.args;
        bool              site = (in->flags & LIR_CALL_SITE) != 0;

        if (rt == NULL || rt->interrupt == NULL || rt->poll == NULL) {
                return lir_fail(
                        e->err,
                        LE_MODE,
                        pc,
                        in->span,
                        "POLL requires a VM runtime"
                );
        }

        bounds(e, pc);
        li(Dst, TMP0, (uptr)rt->interrupt);
        mem(Dst, false, TMP0, TMP0, 0, 4, false, false);
        brz(Dst, TMP0, false, true, fast);

        if (!phase(e, pc, LIR_MOVE_BEFORE, LIR_NONE, MV_SLOW)) {
                return false;
        }

        if (in->nargs == 4) {
                LirInst x = {
                        .sig = {
                                .ret     = LT_I32,
                                .params  = (LirType[]) { LT_PTR, LT_PTR, LT_PTR },
                                .nparams = 3,
                                .nfixed  = 3
                        },
                        .call_args  = (LirOpnd *)in->args,
                        .ncall_args = 3
                };
                if (!pass(e, &x, pc)) {
                        return false;
                }
        } else {
                ld(Dst, args[0], FRAME, e->ty_slot);
                vm_top(Dst, args[1], args[0]);
                li(Dst, args[2], 0);
        }

        li(Dst, TMP0, (uptr)rt->poll);
        call(Dst, site, e->thunk, e->pc_slot);

        if (site) {
                label(Dst, e->sites + pc);
        }

        mov(Dst, TMP0, 0, LIR_I32, false, false);
        st(Dst, TMP0, FRAME, e->result);

        if (!phase(e, pc, LIR_MOVE_AFTER, LIR_NONE, MV_SLOW)) {
                return false;
        }

        rebase(e, pc);
        ld(Dst, TMP0, FRAME, e->result);
        brz(Dst, TMP0, true, true, dest(e, pc, in->args[in->nargs - 1].label));
        label(Dst, fast);
        label(Dst, end);

        return phase(e, pc, LIR_MOVE_AFTER, LIR_NONE, MV_FAST);
}

static bool
movop(Emit *e, LirInst const *in, u32 pc, u8 d, u8 a, LirClass cls)
{
        LirOpnd x = in->args[0];

        switch (x.kind) {
        case LO_REG:      mov(Dst, d, a, cls, false, false);                   break;
        case LO_CONST:    li(Dst, d, (uptr)&e->code->roots[x.index]);          break;
        case LO_REFCONST: li(Dst, d, (uptr)refptr(&e->code->roots[x.index]));  break;
        case LO_VSLOT:    vslot(e, d, TMP0, x.index);                          break;
        default:
                return lir_fail(e->err, LE_TARGET, pc, in->span, "unsupported native move");
        }

        return true;
}

static void
memop(Emit *e, LirInst const *in, u32 pc, u8 d, u8 const *a)
{
        LirForm form  = LirOps[in->op].form;
        LirMem  m     = in->args[0].mem;
        u8      base  = physical(e, m.base, pc, false);
        u8      index = physical(e, m.index, pc, false);
        bool    word  = (m.index != LIR_NONE) && (rcls(e, m.index) == LIR_I32);

        if (form == LF_LEA) {
                lea(Dst, d, base, index, m.scale, m.disp, word);
                return;
        }

        LirType type   = LirOps[in->op].type;
        u32     size   = lir_type_size(type);
        bool    direct = (index == LIR_PHYS_NONE);
        i32     disp   = m.disp;

#if defined(__aarch64__)
        direct = direct
              && (m.disp >= 0)
              && ((u32)m.disp <= 4095 * size)
              && (m.disp % size == 0);
#endif

        if (!direct) {
                lea(Dst, TMP0, base, index, m.scale, m.disp, word);
                base = TMP0;
                disp = 0;
        }

#if defined(__x86_64__)
        if (form == LF_ST && in->args[1].kind == LO_IMM) {
                sti(Dst, base, disp, size, in->args[1].imm);
                return;
        }
#endif

        mem(
                Dst,
                form == LF_ST,
                (form == LF_ST) ? a[1] : d,
                base,
                disp,
                size,
                type == LT_I8 || type == LT_I16 || type == LT_I32,
                isfloat(lir_type_class(type))
        );
}

static void
test(Emit *e, LirInst const *in, u8 const *a)
{
        LirClass cls = rcls(e, in->args[1].reg);

#if defined(__x86_64__)
        if (in->args[2].kind == LO_IMM) {
                cmpi(Dst, a[1], in->args[2].imm, cls);
                return;
        }
#endif

        compare(Dst, a[1], a[2], cls);
}

static bool
insn(Emit *e, u32 pc)
{
        Lir const     *L    = e->L;
        LirInst const *in   = v_(L->insts, pc);
        LirOpnd const *x    = in->args;
        LirForm        form = LirOps[in->op].form;
        LirClass       cls  = (in->dst == LIR_NONE) ? LIR_I64 : rcls(e, in->dst);
        bool           word = (cls == LIR_I32);
        u8             d    = physical(e, in->dst, pc, true);
        u32            yes  = vN(L->labels) + 2 * pc;
        u32            end  = yes + 1;
        u8             a[LIR_MAX_OPERANDS] = {0};

        for (u32 p = 0; p < in->nargs; ++p) {
                if (x[p].kind == LO_REG) {
                        a[p] = physical(e, x[p].reg, pc, false);
                }
        }

        switch (form) {
        case LF_MOV:
                if (!movop(e, in, pc, d, a[0], cls)) {
                        return false;
                }
                break;

        case LF_LI:
                li(Dst, d, word ? (u32)x[0].imm : (u64)x[0].imm);
                break;

        case LF_FLI:
                fli(Dst, d, cls, e->literals + pc);
                if (e->islands) {
                        jump(Dst, end);
                        literal(Dst, e->literals + pc, fbits(L, in));
                        label(Dst, end);
                }
                break;

        case LF_IBINARY:
                if (x[1].kind == LO_IMM) {
                        alui(Dst, in->op, d, a[0], x[1].imm, word);
                } else {
                        alu(Dst, in->op, d, a[0], a[1], word);
                }
                break;

        case LF_IUNARY:
                unary(Dst, in->op, d, a[0], word);
                break;

        case LF_CHECKED:
                checked(Dst, in->op, d, a[0], a[1], word);
                if (!after(e, pc)) {
                        return false;
                }
                overflow(Dst, in->op, dest(e, pc, x[2].label));
                return true;

        case LF_FBINARY:
        case LF_FUNARY:
        case LF_FMA:
                fop(Dst, in->op, d, a[0], a[1], a[2], cls == LIR_F32);
                break;

        case LF_I2F:
        case LF_F2I:
        case LF_FEXT:
        case LF_FTRUNC:
        case LF_BITCAST:
                convert(Dst, in->op, d, a[0], cls, rcls(e, x[0].reg));
                break;

        case LF_LEA:
        case LF_LD:
        case LF_ST:
                memop(e, in, pc, d, a);
                break;

        case LF_SETCC:
        case LF_FSETCC:
                test(e, in, a);
                setcc(Dst, d, x[0].cc, yes, end);
                break;

        case LF_SELECT:
        case LF_FSELECT:
                test(e, in, a);
#if defined(__x86_64__)
                if (form == LF_SELECT) {
                        choose(Dst, d, a[3], a[4], x[0].cc, cls);
                        break;
                }
#endif
                branch(Dst, x[0].cc, yes);
                pick(Dst, d, a[3], a[4], cls, yes, end);
                break;

        case LF_BR:
        case LF_FBR:
                test(e, in, a);
                if (!after(e, pc)) {
                        return false;
                }
                branch(Dst, x[0].cc, dest(e, pc, x[3].label));
                return true;

        case LF_BRZ:
                cmpz(Dst, a[0], rcls(e, x[0].reg));
                if (!after(e, pc)) {
                        return false;
                }
                branch(Dst, (in->op == LIR_BRNZ) ? LIR_NE : LIR_EQ, dest(e, pc, x[1].label));
                return true;

        case LF_JMP:
                if (!after(e, pc) || !leave(e, pc)) {
                        return false;
                }
                jump(Dst, x[0].label);
                return true;

        case LF_SWITCH:
                st(Dst, a[0], FRAME, e->result);
                if (!after(e, pc)) {
                        return false;
                }
                ld(Dst, TMP0, FRAME, e->result);
                if (rcls(e, x[0].reg) == LIR_I32) {
                        fit(Dst, TMP0, LT_U32);
                }
                jtab(Dst, TMP0, in->ntargets, dest(e, pc, x[1].label), e->literals + pc);
                if (e->islands) {
                        table(Dst, e->literals + pc, in->targets, in->ntargets);
                }
                return true;

        case LF_RET:
                if (in->nargs != 0) {
                        home(e, x[0].reg, pc, 0, L->sig.ret);
                }
                jump(Dst, e->epilogue);
                return true;

        case LF_CALL:
        case LF_TAILCALL:
                if (!invoke(e, in, pc)) {
                        return false;
                }
                if (form == LF_TAILCALL) {
                        return true;
                }
                if (!after(e, pc)) {
                        return false;
                }
                rebase(e, pc);
                return true;

        case LF_CAS:
        case LF_ATOMIC:
                atomic(
                        Dst,
                        in->op,
                        d,
                        physical(e, x[0].mem.base, pc, false),
                        a[1],
                        a[2],
                        word,
                        yes,
                        end
                );
                break;

        case LF_FENCE:
                fence(Dst);
                break;

        case LF_COPY:
                copy32(
                        Dst,
                        physical(e, x[0].mem.base, pc, false),
                        x[0].mem.disp,
                        physical(e, x[1].mem.base, pc, false),
                        x[1].mem.disp
                );
                break;

        case LF_ALLOCA:
                addr(Dst, d, FRAME, slot(e, e->alloc->alloca_offsets[pc]));
                break;

        case LF_SITE:
                label(Dst, e->sites + pc);
                break;

        case LF_ENTRY:
                break;

        case LF_RAW:
                if (!raw(Dst, &in->raw)) {
                        return lir_fail(
                                e->err,
                                LE_TARGET,
                                pc,
                                in->span,
                                "RAW has no %s instructions",
                                e->target->name
                        );
                }
                break;

        case LF_POLL:
                return safepoint(e, in, pc, yes, end);
        }

        return after(e, pc);
}

inline static bool
issite(LirInst const *in)
{
        return (in->op == LIR_SITE) || (in->flags & LIR_CALL_SITE);
}

static bool
prepare(Emit *e)
{
        Lir const      *L     = e->L;
        LirAlloc const *alloc = e->alloc;
        u32             n     = vN(L->insts);
        u32             out   = 0;
        u32             align = alloc->frame_align;

        e->labels      = chain(e->ty, n + 1, vN(L->labels) + 1);
        e->moves       = chain(e->ty, n + 1, alloc->nmoves + 1);
        e->constraints = chain(e->ty, n + 1, alloc->nconstraints + 1);
        e->arguments   = tmp(ArgLoc, L->sig.nparams + 1);
        e->pointers    = tmp(u32, vN(L->regs) + 1);

        for (u32 i = alloc->nmoves; i-- > 0;) {
                LirMove const *m = &alloc->moves[i];
                if (m->op < n) {
                        hook(&e->moves, m->op, i);
                }
        }

        for (u32 i = alloc->nconstraints; i-- > 0;) {
                if (alloc->constraints[i].op < n) {
                        hook(&e->constraints, alloc->constraints[i].op, i);
                }
        }

        for (u32 l = vN(L->labels); l-- > 0;) {
                hook(&e->labels, v__(L->labels, l).pos, l);
        }

        bool *stable = tmp(bool, vN(L->regs) + 1);

        memset(stable, 0, vN(L->regs) + 1);

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirRegInfo const *ri = v_(L->regs, r);

                if (!inmask(L->stable_pins, ri->pin)) {
                        continue;
                }

                stable[alloc->intervals[r].rep] = true;

                if (L->ty_param != LIR_NONE && ri->param == L->ty_param) {
                        e->ty_vreg = r;
                }
        }

        for (u32 r = 0; r < vN(L->regs); ++r) {
                LirInterval const *i = &alloc->intervals[r];

                if (i->rep == r && !stable[r] && rcls(e, r) == LIR_PTR && i->crosses_call) {
                        e->pointers[e->npointers++] = r;
                }
        }

        e->incoming = locate(e->target, &L->sig, e->arguments);

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);

                if (in->op == LIR_CALL || in->op == LIR_TAILCALL) {
                        u32 need = outsize(e, &in->sig);
                        out = (need > out) ? need : out;
                }

                e->nsites   += issite(in);
                e->nentries += (in->op == LIR_ENTRY);
                e->context   = e->context
                            || (in->op == LIR_POLL && in->nargs == 1)
                            || rebases(e, pc);

                for (u32 i = 0; i < in->nargs; ++i) {
                        e->context = e->context || (in->args[i].kind == LO_VSLOT);
                }
        }

        if (
                e->context
             && ((lir_runtime() == NULL) || (lir_runtime()->current_ty == NULL))
        ) {
                return lir_fail(
                        e->err,
                        LE_MODE,
                        LIR_NOWHERE,
                        "attached calls, value slots and implicit polls require a Ty context"
                );
        }

        e->outgoing   = (out + align - 1) & ~(align - 1);
        e->save_gp    = e->outgoing + alloc->frame_size;
        e->save_fp    = e->save_gp + 8 * __builtin_popcountll(alloc->saved_gpr);
        e->params     = e->save_fp + 8 * __builtin_popcountll(alloc->saved_fpr);
        e->origin     = e->params + 8 * L->sig.nparams;
        e->pc_slot    = e->origin + 8;
        e->result     = e->pc_slot + 8;
        e->ty_slot    = e->result + 8;
        e->top_slot   = e->ty_slot + 8;
        e->stack_base = e->top_slot + 8;
        e->stack_end  = e->stack_base + 8;
        e->frame      = (e->stack_end + 8 + 15) & ~(u32)15;

        e->epilogue = vN(L->labels) + 2 * n;
        e->thunk    = e->epilogue + 1;
        e->literals = e->thunk + 1;
        e->sites    = e->literals + n;
        e->rebased  = e->sites + n;
        e->stubs    = e->rebased + n;
        e->edges    = e->stubs + n;

        return true;
}

static void
marks(Emit *e, u32 pc)
{
        each(l, e->labels, pc) {
                label(Dst, l);
        }
}

static bool
stubs(Emit *e)
{
        Lir const      *L     = e->L;
        LirAlloc const *alloc = e->alloc;
        u32             n     = vN(L->insts);
        bool           *done  = tmp(bool, alloc->nstubs + 1);

        memset(done, 0, alloc->nstubs + 1);

        for (u32 pc = 0; pc < n; ++pc) {
                each(i, e->moves, pc) {
                        LirMove const *m = &alloc->moves[i];

                        if (m->phase != LIR_MOVE_STUB || done[m->stub]) {
                                continue;
                        }

                        done[m->stub] = true;
                        label(Dst, e->edges + m->stub);

                        if (!phase(e, pc, LIR_MOVE_STUB, m->edge, MV_ALL)) {
                                return false;
                        }

                        jump(Dst, e->labels.head[m->edge]);
                }
        }

        return true;
}

static bool
assemble(Emit *e)
{
        Lir const *L = e->L;
        u32        n = vN(L->insts);

        dasm_init(Dst, DASM_MAXSECTION);
        dasm_setupglobal(Dst, e->globals, 0);
        dasm_growpc(Dst, vN(L->labels) + 6 * n + 4 + e->alloc->nstubs);
        dasm_setup(Dst, lir_actions);

        prologue(Dst, e->frame, e->alloc->frame_align, e->origin);
        saveregs(e, true);

        if (!receive(e)) {
                return false;
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirOp op   = v__(L->insts, pc).op;
                int   mode = (op == LIR_POLL) ? MV_FAST : MV_ALL;
                marks(e, pc);
                if (
                        !phase(e, pc, LIR_MOVE_EDGE_IN, pc, MV_ALL)
                     || !before(e, pc, mode)
                     || !insn(e, pc)
                     || (op != LIR_JMP && !leave(e, pc))
                ) {
                        return false;
                }
        }

        marks(e, n);
        label(Dst, e->epilogue);
        saveregs(e, false);
        epilogue(Dst, e->origin, false);
        thunk(Dst, e->thunk, e->pc_slot);
        cold(Dst);

        if (!stubs(e)) {
                return false;
        }

        for (u32 pc = 0; pc < n && !e->islands; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (in->op == LIR_FLI) {
                        literal(Dst, e->literals + pc, fbits(L, in));
                } else if (in->op == LIR_SWITCH) {
                        table(Dst, e->literals + pc, in->targets, in->ntargets);
                }
        }

        return true;
}

static bool
build(Emit *e, usize *size)
{
        for (;;) {
                if (!assemble(e)) {
                        return false;
                }

                int status = dasm_link(Dst, size);

                if (status != DASM_S_OK) {
                        return lir_fail(
                                e->err,
                                LE_TARGET,
                                LIR_NOWHERE,
                                "%s DynASM link failed: 0x%x",
                                e->target->name,
                                status
                        );
                }

                if (e->islands || *size <= Reach) {
                        return true;
                }

                dasm_free(Dst);
                e->islands = true;
        }
}

static LirSite
site(Emit *e, LirInst const *in, u32 pc)
{
        return (LirSite) {
                .pc  = dasm_getpclabel(Dst, e->sites + pc),
                .tag = (in->op == LIR_SITE) ? in->args[0].imm : in->tag
        };
}

static bool
publish(Emit *e, usize size)
{
        Lir const *L     = e->L;
        LirCode   *code  = e->code;
        u32        n     = vN(L->insts);
        usize      align = alignof (LirSite);
        usize      off   = (size + align - 1) & ~(align - 1);
        usize      total = sizeof (LirImage)
                         + off
                         + e->nsites * sizeof (LirSite)
                         + e->nentries * sizeof (u32);

        if (off > UINT32_MAX || total < off) {
                return lir_fail(
                        e->err,
                        LE_TARGET,
                        LIR_NOWHERE,
                        "native code image is too large"
                );
        }

        JitMapping map = jm_alloc(total);

        if (map.rx == NULL) {
                return false;
        }

        LirImage *header  = map.rw;
        u8       *rw      = (u8 *)(header + 1);
        u8       *rx      = (u8 *)map.rx + sizeof *header;
        LirSite  *sites   = (void *)(rw + off);
        u32      *resumes = (void *)(sites + e->nsites);

        code->sites   = xtA0(LirSite, e->nsites + 1);
        code->entries = xtA0(LirEntryInfo, e->nentries + 1);

        jm_write_begin();

        *header = (LirImage) {
                .size    = size,
                .table   = off,
                .nsites  = e->nsites,
                .nresume = e->nentries
        };

        int status = dasm_encode(Dst, rw);

        for (u32 pc = 0; pc < n && status == DASM_S_OK; ++pc) {
                LirInst const *in = v_(L->insts, pc);

                if (in->op == LIR_SWITCH) {
                        uptr *table = (void *)(rw + dasm_getpclabel(Dst, e->literals + pc));
                        for (u32 i = 0; i < in->ntargets; ++i) {
                                table[i] = (uptr)rx + dasm_getpclabel(Dst, dest(e, pc, in->targets[i]));
                        }
                }

                if (issite(in)) {
                        LirSite s = site(e, in, pc);
                        sites[code->nsites]         = s;
                        code->sites[code->nsites++] = s;
                }

                if (in->op == LIR_ENTRY) {
                        LirLabel l = in->args[0].label;
                        resumes[code->nentries] = in->tag;
                        code->entries[code->nentries++] = (LirEntryInfo) {
                                .label  = l,
                                .offset = dasm_getpclabel(Dst, l)
                        };
                }
        }

        bool sealed = jm_write_end(map.rx, total);

        if (status != DASM_S_OK || !sealed) {
                jm_free(map.rx);
                return lir_fail(
                        e->err,
                        LE_TARGET,
                        LIR_NOWHERE,
                        "native code publication failed"
                );
        }

        code->allocation = map.rx;
        code->body       = rx;
        code->size       = size;

        for (u32 pc = 0; pc < n; ++pc) {
                LirOp op = v__(L->insts, pc).op;
                if (op == LIR_FLI || op == LIR_SWITCH) {
                        u32 at = dasm_getpclabel(Dst, e->literals + pc);
                        code->literal_pool = rx + at;
                        code->literal_size = size - at;
                        break;
                }
        }

        jm_perf(code->body, code->size, code->name);

        return true;
}

static bool
emit(Ty *ty, Lir const *L, LirAlloc const *alloc, LirCode *code, LirError *err)
{
        Emit *e = &(Emit) {
                .ty      = ty,
                .L       = L,
                .alloc   = alloc,
                .code    = code,
                .target  = &Native,
                .err     = err,
                .context = alloc->nvslots > L->nvslots,
                .ty_vreg = LIR_NONE
        };
        usize size;

        SCRATCH_SAVE();

        bool ok = prepare(e) && build(e, &size) && publish(e, size);

        if (e->dasm != NULL) {
                dasm_free(Dst);
        }

        SCRATCH_RESTORE();

        if (!ok && err != NULL && err->kind == LE_NONE) {
                lir_fail(err, LE_TARGET, LIR_NOWHERE, "could not emit native function");
        }

        return ok;
}

LirTarget const *
lir_target(void)
{
        return &Native;
}

#else

LirTarget const *
lir_target(void)
{
        return NULL;
}

#endif
