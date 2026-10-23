#include <math.h>

#include "impl.h"

typedef struct {
        Lir     *lir;
        LirClass cls;
        LirSpan  span;
        u32      bits;
} Reduce;

static LirOpnd
emit(Reduce *r, LirOp op, LirOpnd a, LirOpnd b)
{
        LirInst in = {
                .op    = op,
                .dst   = lir_reg(r->lir, r->cls),
                .args  = { a, b },
                .nargs = LirOps[op].argc,
                .span  = r->span
        };

        lir_emit(r->lir, &in);

        return lir_r(in.dst);
}

static LirOpnd
signed_quotient(Reduce *r, LirOpnd x, i64 d)
{
        u64      magnitude = (d < 0) ? 0 - (u64)d : (u64)d;
        LirOpnd  q;

        if (magnitude == 1) {
                q = x;
        } else if ((magnitude & (magnitude - 1)) == 0) {
                u32 shift = __builtin_ctzll(magnitude);
                LirOpnd sign = x;

                if (shift != 1) {
                        sign = emit(r, LIR_SAR, x, lir_i(r->bits - 1));
                }

                LirOpnd bias = emit(r, LIR_SHR, sign, lir_i(r->bits - shift));

                q = emit(r, LIR_ADD, x, bias);
                q = emit(r, LIR_SAR, q, lir_i(shift));
        } else {
                u32 shift = 0;
                unsigned __int128 power = (unsigned __int128)1 << r->bits;
                unsigned __int128 multiplier = (power + magnitude - 1) / magnitude;

                while (multiplier * magnitude - power > ((u64)1 << (shift + 1))) {
                        power <<= 1;
                        shift += 1;
                        multiplier = (power + magnitude - 1) / magnitude;
                }

                u64 m = (u64)multiplier;

                q = emit(r, LIR_MULHS, x, lir_i(m));
                if ((m >> (r->bits - 1)) != 0) {
                        q = emit(r, LIR_ADD, q, x);
                }
                if (shift != 0) {
                        q = emit(r, LIR_SAR, q, lir_i(shift));
                }

                LirOpnd sign = emit(r, LIR_SHR, x, lir_i(r->bits - 1));

                q = emit(r, LIR_ADD, q, sign);
        }

        return (d < 0) ? emit(r, LIR_NEG, q, (LirOpnd) {0}) : q;
}

static LirOpnd
unsigned_quotient(Reduce *r, LirOpnd x, u64 d)
{
        u32 shift = 63 - __builtin_clzll(d);

        if ((d & (d - 1)) == 0) {
                return (shift == 0) ? x : emit(r, LIR_SHR, x, lir_i(shift));
        }

        unsigned __int128 power = (unsigned __int128)1 << (r->bits + shift);
        unsigned __int128 multiplier = (power + d - 1) / d;
        bool correct = multiplier * d - power > ((u64)1 << shift);

        if (correct) {
                multiplier = (2 * power + d - 1) / d;
        }

        u64 mask = (r->bits == 32) ? UINT32_MAX : UINT64_MAX;
        LirOpnd q = emit(r, LIR_MULHU, x, lir_i((u64)multiplier & mask));

        if (correct) {
                LirOpnd t = emit(r, LIR_SUB, x, q);
                t = emit(r, LIR_SHR, t, lir_i(1));
                q = emit(r, LIR_ADD, t, q);
        }

        return (shift == 0) ? q : emit(r, LIR_SHR, q, lir_i(shift));
}

static void
divide(Lir *L, LirInst in, u64 d)
{
        LirClass cls = rcls(L, in.dst);
        Reduce   r   = { L, cls, in.span, (cls == LIR_I32) ? 32 : 64 };
        bool     rem = (in.op == LIR_SREM) || (in.op == LIR_UREM);
        bool     sign = (in.op == LIR_SDIV) || (in.op == LIR_SREM);
        LirOpnd  x = in.args[0];
        LirOpnd  q;

        if (x.kind != LO_REG) {
                x = emit(&r, LIR_MOV, x, (LirOpnd) {0});
        }

        if (d == 0) {
                q = rem ? x : lir_i(0);
        } else {
                if (sign) {
                        i64 divisor = (cls == LIR_I32) ? (i32)d : (i64)d;
                        q = signed_quotient(&r, x, divisor);
                } else if (d >= ((u64)1 << (r.bits - 1))) {
                        LirInst cmp = {
                                .op    = LIR_SETCC,
                                .dst   = lir_reg(L, cls),
                                .args  = { lir_cc(LIR_UGE), x, lir_i(d) },
                                .nargs = 3,
                                .span  = in.span
                        };
                        lir_emit(L, &cmp);
                        q = lir_r(cmp.dst);
                } else {
                        q = unsigned_quotient(&r, x, d);
                }

                if (rem) {
                        q = emit(&r, LIR_MUL, q, lir_i(d));
                        q = emit(&r, LIR_SUB, x, q);
                }
        }

        in.op      = LIR_MOV;
        in.nargs   = 1;
        in.args[0] = q;

        lir_emit_owned(L, &in);
}

static bool
constant(Lir const *L, u32 const *defs, LirOpnd a, LirClass cls, u64 *out)
{
        for (u32 n = 0; a.kind == LO_REG && n < vN(L->regs); ++n) {
                LirRegInfo ri = v__(L->regs, a.reg);
                u32 pc = defs[a.reg];

                if (
                        (ri.cls != cls)
                     || (ri.param != LIR_NONE)
                     || (ri.pin != LIR_NONE)
                     || (pc >= vN(L->insts))
                ) {
                        return false;
                }

                LirInst const *in = v_(L->insts, pc);

                if (in->op != LIR_LI && in->op != LIR_MOV) {
                        return false;
                }

                a = in->args[0];
        }

        if (a.kind != LO_IMM) {
                return false;
        }

        *out = (cls == LIR_I32) ? (u32)a.imm : (u64)a.imm;

        return true;
}

static bool
fconstant(Lir const *L, u32 const *defs, LirOpnd a, double *out)
{
        for (u32 n = 0; a.kind == LO_REG && n < vN(L->regs); ++n) {
                LirRegInfo ri = v__(L->regs, a.reg);
                u32 pc = defs[a.reg];

                if (
                        (ri.cls != LIR_F64)
                     || (ri.param != LIR_NONE)
                     || (ri.pin != LIR_NONE)
                     || (pc >= vN(L->insts))
                ) {
                        return false;
                }

                LirInst const *in = v_(L->insts, pc);

                if (in->op != LIR_FLI && in->op != LIR_MOV) {
                        return false;
                }

                a = in->args[0];
        }

        if (a.kind != LO_FIMM) {
                return false;
        }

        *out = a.fimm;

        return true;
}

static void
become(LirInst *in, LirOp op, LirOpnd a)
{
        in->op      = op;
        in->nargs   = 1;
        in->args[0] = a;

        for (u32 i = 1; i < countof(in->args); ++i) {
                in->args[i] = (LirOpnd) { .kind = LO_NONE };
        }
}

static bool
integer_fold(LirOp op, u64 x, u64 y, u64 *out)
{
        u32 shift = y & 63;

        switch (op) {
        case LIR_ADD: *out = x + y;                   return true;
        case LIR_SUB: *out = x - y;                   return true;
        case LIR_MUL: *out = x * y;                   return true;
        case LIR_AND: *out = x & y;                   return true;
        case LIR_OR:  *out = x | y;                   return true;
        case LIR_XOR: *out = x ^ y;                   return true;
        case LIR_SHL: *out = x << shift;              return true;
        case LIR_SHR: *out = x >> shift;              return true;
        case LIR_SAR: *out = (u64)((i64)x >> shift);  return true;
        default:                                      return false;
        }
}

static bool
float_fold(LirOp op, double x, double y, double *out)
{
        switch (op) {
        case LIR_FADD: *out = x + y; return true;
        case LIR_FSUB: *out = x - y; return true;
        case LIR_FMUL: *out = x * y; return true;
        case LIR_FDIV: *out = x / y; return true;
        default:                     return false;
        }
}

static bool
holds(LirCC cc, u64 a, u64 b, double f, double g)
{
        i64 x = (i64)a;
        i64 y = (i64)b;

        switch (cc) {
        case LIR_EQ:  return a == b;
        case LIR_NE:  return a != b;
        case LIR_LT:  return x <  y;
        case LIR_LE:  return x <= y;
        case LIR_GT:  return x >  y;
        case LIR_GE:  return x >= y;
        case LIR_ULT: return a <  b;
        case LIR_ULE: return a <= b;
        case LIR_UGT: return a >  b;
        case LIR_UGE: return a >= b;
        case LIR_FEQ: return f == g;
        case LIR_FNE: return f != g;
        case LIR_FLT: return f <  g;
        case LIR_FLE: return f <= g;
        case LIR_FGT: return f >  g;
        case LIR_FGE: return f >= g;
        case LIR_FUN: return isnan(f) || isnan(g);
        default:      return false;
        }
}

static bool
identity(LirInst *in, u64 const *a, u64 const *b)
{
        LirOpnd x = in->args[0];
        LirOpnd y = in->args[1];

        switch (in->op) {
        case LIR_ADD:
        case LIR_OR:
        case LIR_XOR:
                if (b != NULL && *b == 0) {
                        become(in, LIR_MOV, x);
                        return true;
                }
                if (a != NULL && *a == 0) {
                        become(in, LIR_MOV, y);
                        return true;
                }
                return false;

        case LIR_SUB:
        case LIR_SHL:
        case LIR_SHR:
        case LIR_SAR:
                if (b != NULL && (in->op == LIR_SUB ? *b == 0 : (*b & 63) == 0)) {
                        become(in, LIR_MOV, x);
                        return true;
                }
                return false;

        case LIR_MUL:
                if ((b != NULL && *b == 1) || (a != NULL && *a == 1)) {
                        become(in, LIR_MOV, (b != NULL && *b == 1) ? x : y);
                        return true;
                }
                if ((b != NULL && *b == 0) || (a != NULL && *a == 0)) {
                        become(in, LIR_LI, lir_i(0));
                        return true;
                }
                return false;

        case LIR_AND:
                if ((b != NULL && *b == 0) || (a != NULL && *a == 0)) {
                        become(in, LIR_LI, lir_i(0));
                        return true;
                }
                return false;

        default:
                return false;
        }
}

static bool
commutes(LirOp op)
{
        switch (op) {
        case LIR_ADD:
        case LIR_MUL:
        case LIR_AND:
        case LIR_OR:
        case LIR_XOR:
                return true;

        default:
                return false;
        }
}

static bool
immediate(LirOpnd *a, u64 v)
{
        if (a->kind != LO_REG || (i64)v < INT32_MIN || (i64)v > INT32_MAX) {
                return false;
        }

        *a = lir_i((i64)v);

        return true;
}

static bool
fold_inst(Lir const *L, u32 const *defs, LirInst *in, bool *drop)
{
        LirForm form = LirOps[in->op].form;
        u64     x;
        u64     y;
        double  f;
        double  g;

        if (form == LF_IBINARY && rcls(L, in->dst) == LIR_I64) {
                bool ca = constant(L, defs, in->args[0], LIR_I64, &x);
                bool cb = constant(L, defs, in->args[1], LIR_I64, &y);
                u64  r;

                if (ca && cb && integer_fold(in->op, x, y, &r)) {
                        become(in, LIR_LI, lir_i((i64)r));
                        return true;
                }

                if (identity(in, ca ? &x : NULL, cb ? &y : NULL)) {
                        return true;
                }

                if (ca && !cb && commutes(in->op)) {
                        LirOpnd t = in->args[0];

                        in->args[0] = in->args[1];
                        in->args[1] = t;
                        y           = x;
                        cb          = true;
                }

                return cb && immediate(&in->args[1], y);
        }

        if (form == LF_FBINARY && rcls(L, in->dst) == LIR_F64) {
                double r;

                if (
                        fconstant(L, defs, in->args[0], &f)
                     && fconstant(L, defs, in->args[1], &g)
                     && float_fold(in->op, f, g, &r)
                ) {
                        become(in, LIR_FLI, lir_f(r));
                        return true;
                }

                return false;
        }

        if (in->op == LIR_I2F && rcls(L, in->dst) == LIR_F64 && constant(L, defs, in->args[0], LIR_I64, &x)) {
                become(in, LIR_FLI, lir_f((double)(i64)x));
                return true;
        }

        bool branch = (in->op == LIR_BR) || (in->op == LIR_FBR);
        bool setcc  = (in->op == LIR_SETCC) || (in->op == LIR_FSETCC);

        if (!branch && !setcc) {
                return false;
        }

        LirCC cc    = in->args[0].cc;
        bool  real  = (in->op == LIR_FBR) || (in->op == LIR_FSETCC);
        bool  known = real
                    ? (fconstant(L, defs, in->args[1], &f) && fconstant(L, defs, in->args[2], &g))
                    : (constant(L, defs, in->args[1], LIR_I64, &x) && constant(L, defs, in->args[2], LIR_I64, &y));

        if (
                !known
             && !real
             && (in->args[1].kind == LO_REG)
             && (rcls(L, in->args[1].reg) == LIR_I64)
             && constant(L, defs, in->args[2], LIR_I64, &y)
        ) {
                return immediate(&in->args[2], y);
        }

        if (!known || (!real && setcc && rcls(L, in->dst) != LIR_I64)) {
                return false;
        }

        if (!real && in->args[1].kind == LO_REG && rcls(L, in->args[1].reg) != LIR_I64) {
                return false;
        }

        bool taken = real ? holds(cc, 0, 0, f, g) : holds(cc, x, y, 0.0, 0.0);

        if (setcc) {
                become(in, LIR_LI, lir_i(taken));
        } else if (taken) {
                become(in, LIR_JMP, in->args[3]);
        } else {
                *drop = true;
        }

        return true;
}

static void
rebuild(Lir *L, bool const *drop, u32 n, u32 *at)
{
        LirInst *old = lir_swap(L);

        for (u32 pc = 0; pc < n; ++pc) {
                at[pc] = vN(L->insts);
                if (!drop[pc]) {
                        lir_emit_owned(L, &old[pc]);
                }
        }

        at[n] = vN(L->insts);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                v_(L->labels, i)->pos = at[v__(L->labels, i).pos];
        }
}

static bool
idle(Lir const *L, LirInst const *in, u32 const *reads)
{
        if (in->dst == LIR_NONE || reads[in->dst] != 0 || in->flags != 0) {
                return false;
        }

        LirRegInfo ri = v__(L->regs, in->dst);

        if (ri.param != LIR_NONE || ri.pin != LIR_NONE) {
                return false;
        }

        switch (in->op) {
        case LIR_LI:
        case LIR_FLI:
        case LIR_MOV:
                return true;

        default:
                return false;
        }
}

static void
sweep(Ty *ty, Lir *L, bool *drop, u32 n)
{

        u32  *reads = stA0(u32, vN(L->regs));
        bool  again = true;

        for (u32 pc = 0; pc < n; ++pc) {
                if (!drop[pc]) {
                        each_read(v_(L->insts, pc), r) {
                                reads[r] += 1;
                        }
                }
        }

        while (again) {
                again = false;
                for (u32 pc = 0; pc < n; ++pc) {
                        LirInst const *in = v_(L->insts, pc);
                        if (drop[pc] || !idle(L, in, reads)) {
                                continue;
                        }
                        drop[pc] = true;
                        again    = true;
                        each_read(in, r) {
                                reads[r] -= 1;
                        }
                }
        }

}

static void
fold(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_FOLD") != NULL) {
                return;
        }

        u32   n    = vN(L->insts);
        u32  *defs = stA(u32, vN(L->regs));
        bool *drop = stA0(bool, n);
        u32  *at   = stA(u32, n + 1);
        bool  any  = false;

        memset(defs, 0xff, vN(L->regs) * sizeof *defs);

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                each_write(in, reg) {
                        defs[reg] = (defs[reg] == LIR_NONE) ? pc : n;
                }
        }

        for (u32 round = 0; round < 8; ++round) {
                bool changed = false;

                for (u32 pc = 0; pc < n; ++pc) {
                        if (!drop[pc] && fold_inst(L, defs, v_(L->insts, pc), &drop[pc])) {
                                changed = true;
                        }
                }

                any |= changed;

                if (!changed) {
                        break;
                }
        }

        if (any) {
                sweep(ty, L, drop, n);
        }

        bool dropped = false;

        for (u32 pc = 0; pc < n; ++pc) {
                dropped |= drop[pc];
        }

        if (any && dropped) {
                rebuild(L, drop, n, at);
        }

}

typedef struct {
        LirOp    op;
        LirClass cls;
        LirOpnd  args[3];
        u32      vers[3][2];
        LirReg   dst;
        u32      dver;
} Numbered;

static bool
numbered(LirInst const *in)
{
        if (in->dst == LIR_NONE || in->nargs > 3 || in->flags != 0) {
                return false;
        }

        switch (LirOps[in->op].form) {
        case LF_IBINARY:
        case LF_IUNARY:
        case LF_FBINARY:
        case LF_FUNARY:
        case LF_I2F:
        case LF_F2I:
        case LF_BITCAST:
        case LF_LEA:
        case LF_SETCC:
        case LF_FSETCC:
                return true;

        default:
                return false;
        }
}

static void
versions(LirOpnd a, u32 const *ver, u32 out[2])
{
        out[0] = (a.kind == LO_REG) ? ver[a.reg]
               : (a.kind == LO_MEM && a.mem.base != LIR_NONE) ? ver[a.mem.base]
               : 0;
        out[1] = (a.kind == LO_MEM && a.mem.index != LIR_NONE) ? ver[a.mem.index] : 0;
}

static bool
same_operand(LirOpnd a, LirOpnd b)
{
        if (a.kind != b.kind) {
                return false;
        }

        switch (a.kind) {
        case LO_NONE:  return true;
        case LO_REG:   return a.reg == b.reg;
        case LO_IMM:   return a.imm == b.imm;
        case LO_FIMM:  return memcmp(&a.fimm, &b.fimm, sizeof a.fimm) == 0;
        case LO_CC:    return a.cc == b.cc;
        case LO_MEM:   return (a.mem.base == b.mem.base)
                           && (a.mem.index == b.mem.index)
                           && (a.mem.scale == b.mem.scale)
                           && (a.mem.disp == b.mem.disp);
        default:       return false;
        }
}

static void
number(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_LVN") != NULL) {
                return;
        }

        enum { WINDOW = 64 };

        u32    n     = vN(L->insts);
        u32   *ver   = stA0(u32, vN(L->regs));
        bool  *start = stA0(bool, n + 1);
        Numbered *seen  = stA(Numbered, WINDOW);
        u32    count = 0;

        for (u32 i = 0; i < vN(L->labels); ++i) {
                u32 pos = v__(L->labels, i).pos;
                if (pos <= n) {
                        start[pos] = true;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst *in = v_(L->insts, pc);

                if (start[pc]) {
                        count = 0;
                }

                bool candidate = numbered(in);
                Numbered v     = { .op = in->op, .cls = rcls(L, in->dst) };

                if (candidate) {
                        for (u32 k = 0; k < 3; ++k) {
                                v.args[k] = (k < in->nargs) ? in->args[k] : (LirOpnd) { .kind = LO_NONE };
                                versions(v.args[k], ver, v.vers[k]);
                        }

                        for (u32 e = 0; e < count; ++e) {
                                Numbered const *w = &seen[e];
                                bool match = (w->op == v.op)
                                          && (w->cls == v.cls)
                                          && (ver[w->dst] == w->dver)
                                          && (w->dst != in->dst);

                                for (u32 k = 0; match && k < 3; ++k) {
                                        match = same_operand(w->args[k], v.args[k])
                                             && (w->vers[k][0] == v.vers[k][0])
                                             && (w->vers[k][1] == v.vers[k][1]);
                                }

                                if (match) {
                                        become(in, LIR_MOV, lir_r(w->dst));
                                        candidate = false;
                                        break;
                                }
                        }
                }

                each_write(in, reg) {
                        ver[reg] += 1;
                }

                if (candidate && v.cls != LIR_CLASS_COUNT) {
                        v.dst  = in->dst;
                        v.dver = ver[in->dst];

                        if (count == WINDOW) {
                                memmove(seen, seen + 1, (WINDOW - 1) * sizeof *seen);
                                count -= 1;
                        }

                        seen[count++] = v;
                }
        }

}

static bool
division(LirOp op)
{
        return (op == LIR_SDIV) || (op == LIR_UDIV)
            || (op == LIR_SREM) || (op == LIR_UREM);
}

static bool
jumps(LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_CHECKED:
        case LF_BR:
        case LF_FBR:
        case LF_BRZ:
        case LF_JMP:
        case LF_SWITCH:
        case LF_POLL:
        case LF_ENTRY:
                return true;

        default:
                return false;
        }
}

static bool
ends(LirInst const *in)
{
        return (in->op == LIR_JMP)
            || (in->op == LIR_SWITCH)
            || (in->op == LIR_RET)
            || (in->op == LIR_TAILCALL)
            || (in->flags & LIR_NORETURN);
}

static bool
prune_once(Lir const *L, bool *drop, bool *wanted, u32 n)
{
        bool changed = false;
        bool dead    = false;

        memset(wanted, 0, (n + 1) * sizeof *wanted);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                if (v__(L->labels, i).entry) {
                        wanted[v__(L->labels, i).pos] = true;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (drop[pc] || !jumps(in)) {
                        continue;
                }
                wanted[v__(L->labels, in->args[in->nargs - 1].label).pos] = true;
                for (u32 j = 0; j < in->ntargets; ++j) {
                        wanted[v__(L->labels, in->targets[j]).pos] = true;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                dead = dead && !wanted[pc];
                if (dead && !drop[pc]) {
                        drop[pc] = true;
                        changed  = true;
                }
                if (!drop[pc]) {
                        dead = ends(v_(L->insts, pc));
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                u32            to = pc + 1;

                if (drop[pc] || in->op != LIR_JMP) {
                        continue;
                }

                u32 at = v__(L->labels, in->args[0].label).pos;

                while (to < n && to < at && drop[to]) {
                        to += 1;
                }

                if (to == at) {
                        drop[pc] = true;
                        changed  = true;
                }
        }

        return changed;
}

static void
prune(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_PRUNE") != NULL) {
                return;
        }

        u32   n      = vN(L->insts);
        bool *drop   = stA0(bool, n);
        bool *wanted = stA(bool, n + 1);
        u32  *at     = stA(u32, n + 1);
        bool  any    = false;

        while (prune_once(L, drop, wanted, n)) {
                any = true;
        }

        if (any) {
                rebuild(L, drop, n, at);
        }

}

static u32
cold_end(Lir const *L, bool const *hot, u32 pc, u32 n)
{
        for (u32 to = pc; to < n; ++to) {
                if (to > pc && hot[to]) {
                        return to;
                }
                if (ends(v_(L->insts, to))) {
                        return to + 1;
                }
        }

        return LIR_NONE;
}

static LirLabel
label_at(Lir const *L, u32 pos)
{
        for (u32 i = 0; i < vN(L->labels); ++i) {
                if (v__(L->labels, i).pos == pos) {
                        return i;
                }
        }

        return LIR_NONE;
}

static void
sink(Ty *ty, Lir *L)
{
        u32 n = vN(L->insts);

        if (n == 0 || getenv("TY_LIR_NO_SINK") != NULL) {
                return;
        }

        bool     *hot   = stA0(bool, n + 1);
        bool     *cold  = stA0(bool, n + 1);
        bool     *moved = stA0(bool, n);
        LirLabel *exit  = stA(LirLabel, n);
        u32      *at    = stA(u32, n + 1);
        bool      any   = false;

        for (u32 i = 0; i < vN(L->labels); ++i) {
                LirLabelInfo l = v__(L->labels, i);
                if (l.pos == n) {
                        goto Done;
                }
                if (l.pos != LIR_NONE) {
                        *(l.cold ? &cold[l.pos] : &hot[l.pos]) = true;
                }
        }

        for (u32 pc = 1; pc < n; ++pc) {
                if (!cold[pc] || hot[pc] || !ends(v_(L->insts, pc - 1))) {
                        continue;
                }

                u32 end = cold_end(L, hot, pc, n);

                if (end == LIR_NONE) {
                        continue;
                }

                LirLabel out = ends(v_(L->insts, end - 1)) ? LIR_NONE : label_at(L, end);

                if (out == LIR_NONE && !ends(v_(L->insts, end - 1))) {
                        continue;
                }

                for (u32 i = pc; i < end; ++i) {
                        moved[i] = true;
                        exit[i]  = (i + 1 == end) ? out : LIR_NONE;
                }

                any = true;
                pc  = end - 1;
        }

        if (!any) {
                goto Done;
        }

        LirInst *old = lir_swap(L);

        for (u32 pass = 0; pass < 2; ++pass) {
                for (u32 pc = 0; pc < n; ++pc) {
                        if (moved[pc] != (pass == 1)) {
                                continue;
                        }
                        at[pc] = vN(L->insts);
                        lir_emit_owned(L, &old[pc]);
                        if (moved[pc] && exit[pc] != LIR_NONE) {
                                lvP(L->insts, ((LirInst) {
                                        .op     = LIR_JMP,
                                        .dst    = LIR_NONE,
                                        .args   = { lir_l(exit[pc]) },
                                        .nargs  = 1,
                                        .origin = old[pc].origin
                                }));
                        }
                }
        }

        at[n] = vN(L->insts);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                LirLabelInfo *l = v_(L->labels, i);
                if (l->pos != LIR_NONE) {
                        l->pos = at[l->pos];
                }
        }

Done:
}

typedef struct {
        u32 *refs;
        u32 *marks;
        u32 *defs;
        u32 *lo;
        u32 *hi;
} Shape;

static bool
plain(LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_IBINARY:
                return !division(in->op);

        case LF_IUNARY:
        case LF_LI:
        case LF_MOV:
        case LF_LEA:
                return in->flags == 0;

        default:
                return false;
        }
}

static bool
marked(Shape const *sh, u32 from, u32 to)
{
        for (u32 p = from; p < to; ++p) {
                if (sh->marks[p] != 0) {
                        return true;
                }
        }

        return false;
}

static bool
arm(Lir const *L, Shape const *sh, u32 lo, u32 end, LirReg out, LirInst const *br)
{
        if (end <= lo || end - lo > 5) {
                return false;
        }

        LirInst const *last = v_(L->insts, end - 1);

        if (last->op != LIR_MOV || last->dst != out) {
                return false;
        }

        for (u32 pc = lo; pc + 1 < end; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                LirReg         d  = in->dst;

                if (
                        !plain(in)
                     || (d == LIR_NONE)
                     || (d == out)
                     || (sh->defs[d] != 1)
                     || (sh->lo[d] < lo)
                     || (sh->hi[d] >= end && sh->hi[d] != LIR_NONE)
                     || (v__(L->regs, d).pin != LIR_NONE)
                     || (v__(L->regs, d).param != LIR_NONE)
                ) {
                        return false;
                }

                for (u32 k = 1; k <= 2; ++k) {
                        if (br->args[k].kind == LO_REG && br->args[k].reg == d) {
                                return false;
                        }
                }
        }

        return true;
}

static bool
diamond(Lir *L, Shape const *sh, u32 pc, bool *drop, u32 *skip)
{
        LirInst const *br = v_(L->insts, pc);
        u32            n  = vN(L->insts);

        if (br->op != LIR_BR || sh->refs[br->args[3].label] != 1) {
                return false;
        }

        u32 t = v__(L->labels, br->args[3].label).pos;
        u32 j = t - 1;

        if (t <= pc + 2 || t >= n || v__(L->insts, j).op != LIR_JMP) {
                return false;
        }

        LirLabel join = v__(L->insts, j).args[0].label;
        u32      k    = v__(L->labels, join).pos;

        if (
                (sh->refs[join] != 1)
             || (k <= t)
             || (k > n)
             || marked(sh, pc + 1, t)
             || (sh->marks[t] != 1)
             || marked(sh, t + 1, k)
        ) {
                return false;
        }

        LirReg out = v__(L->insts, j - 1).dst;

        if (
                (out == LIR_NONE)
             || (v__(L->insts, j - 1).op != LIR_MOV)
             || (v__(L->regs, out).cls != LIR_I64 && v__(L->regs, out).cls != LIR_I32)
             || !arm(L, sh, pc + 1, j, out, br)
             || !arm(L, sh, t, k, out, br)
        ) {
                return false;
        }

        LirInst *last = v_(L->insts, k - 1);
        LirInst  sel  = *last;

        sel.op      = LIR_SELECT;
        sel.nargs   = 5;
        sel.args[0] = br->args[0];
        sel.args[1] = br->args[1];
        sel.args[2] = br->args[2];
        sel.args[3] = last->args[0];
        sel.args[4] = v__(L->insts, j - 1).args[0];

        *last = sel;

        drop[pc]    = true;
        drop[j - 1] = true;
        drop[j]     = true;
        *skip       = k;

        return true;
}

static bool
diamonds_once(Ty *ty, Lir *L)
{

        u32   n     = vN(L->insts);
        u32   nregs = vN(L->regs);
        bool *drop  = stA0(bool, n);
        u32  *at    = stA(u32, n + 1);
        bool  any   = false;
        Shape sh    = {
                .refs  = stA0(u32, vN(L->labels) + 1),
                .marks = stA0(u32, n + 1),
                .defs  = stA0(u32, nregs + 1),
                .lo    = stA(u32, nregs + 1),
                .hi    = stA(u32, nregs + 1)
        };

        memset(sh.lo, 0xff, (nregs + 1) * sizeof *sh.lo);
        memset(sh.hi, 0xff, (nregs + 1) * sizeof *sh.hi);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                sh.refs[i] += v__(L->labels, i).entry;
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (jumps(in)) {
                        sh.refs[in->args[in->nargs - 1].label] += 1;
                        for (u32 j = 0; j < in->ntargets; ++j) {
                                sh.refs[in->targets[j]] += 1;
                        }
                }
                each_write(in, r) {
                        sh.defs[r] += 1;
                }
                each_read(in, r) {
                        sh.lo[r] = (sh.lo[r] == LIR_NONE || pc < sh.lo[r]) ? pc : sh.lo[r];
                        sh.hi[r] = (sh.hi[r] == LIR_NONE || pc > sh.hi[r]) ? pc : sh.hi[r];
                }
        }

        for (u32 i = 0; i < vN(L->labels); ++i) {
                if (sh.refs[i] != 0) {
                        sh.marks[v__(L->labels, i).pos] += 1;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                u32 skip = pc;

                if (diamond(L, &sh, pc, drop, &skip)) {
                        any = true;
                        pc  = skip;
                }
        }

        if (any) {
                rebuild(L, drop, n, at);
        }

        return any;
}

static void
diamonds(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_SELECT") != NULL) {
                return;
        }

        for (u32 round = 0; round < 4 && diamonds_once(ty, L); ++round) {
                continue;
        }
}

bool
lir_optimize(Ty *ty, Lir *L)
{
        ty = lir_scratch(ty);

        sink(ty, L);
        prune(ty, L);
        diamonds(ty, L);
        fold(ty, L);
        number(ty, L);

        u32 n = vN(L->insts);
        bool found = false;

        for (u32 pc = 0; pc < n; ++pc) {
                if (division(v__(L->insts, pc).op)) {
                        found = true;
                        break;
                }
        }

        if (!found) {
                return true;
        }

        ty = lir_scratch(ty);

        u32  *defs = stA(u32, vN(L->regs));
        u64  *divisors = stA(u64, n);
        bool *reduce = stA0(bool, n);
        u32  *at = stA(u32, n + 1);

        memset(defs, 0xff, vN(L->regs) * sizeof *defs);

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                each_write(in, reg) {
                        defs[reg] = (defs[reg] == LIR_NONE) ? pc : n;
                }
        }

        found = false;

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (division(in->op)) {
                        reduce[pc] = constant(L, defs, in->args[1], rcls(L, in->dst), &divisors[pc]);
                        found |= reduce[pc];
                }
        }

        if (found) {
                LirInst *old = lir_swap(L);

                for (u32 pc = 0; pc < n; ++pc) {
                        at[pc] = vN(L->insts);
                        if (reduce[pc]) {
                                divide(L, old[pc], divisors[pc]);
                        } else {
                                lir_emit_owned(L, &old[pc]);
                        }
                }

                at[n] = vN(L->insts);

                for (u32 i = 0; i < vN(L->labels); ++i) {
                        v_(L->labels, i)->pos = at[v__(L->labels, i).pos];
                }
        }

        return L->error.kind == LE_NONE;
}
