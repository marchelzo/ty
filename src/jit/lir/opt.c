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

static LirCC
mirror(LirCC cc)
{
        switch (cc) {
        case LIR_LT:  return LIR_GT;
        case LIR_GT:  return LIR_LT;
        case LIR_LE:  return LIR_GE;
        case LIR_GE:  return LIR_LE;
        case LIR_ULT: return LIR_UGT;
        case LIR_UGT: return LIR_ULT;
        case LIR_ULE: return LIR_UGE;
        case LIR_UGE: return LIR_ULE;
        default:      return cc;
        }
}

static bool
fold_address(Lir const *L, u32 const *defs, LirInst *in)
{
        bool any = false;
        u64  c;

        for (u32 k = 0; k < in->nargs; ++k) {
                LirMem *m = &in->args[k].mem;

                if (
                        (in->args[k].kind != LO_MEM)
                     || (m->base == LIR_NONE)
                     || (m->index == LIR_NONE)
                     || (rcls(L, m->index) != LIR_I64)
                     || !constant(L, defs, lir_r(m->index), LIR_I64, &c)
                     || ((i64)c < -(1 << 24) || (i64)c > (1 << 24))
                ) {
                        continue;
                }

                i64 disp = (i64)m->disp + (i64)c * m->scale;

                if (disp >= INT32_MIN && disp <= INT32_MAX) {
                        m->disp  = (i32)disp;
                        m->index = LIR_NONE;
                        m->scale = 1;
                        any      = true;
                }
        }

        LirMem m = in->args[0].mem;

        if (
                (in->op == LIR_LEA)
             && (m.base != LIR_NONE)
             && (m.index == LIR_NONE)
             && (m.disp == 0)
             && (rcls(L, m.base) == rcls(L, in->dst))
        ) {
                become(in, LIR_MOV, lir_r(m.base));
                any = true;
        }

        return any;
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
             && (in->args[2].kind == LO_REG)
             && (rcls(L, in->args[2].reg) == LIR_I64)
             && constant(L, defs, in->args[1], LIR_I64, &x)
             && ((i64)x >= INT32_MIN && (i64)x <= INT32_MAX)
        ) {
                in->args[0] = lir_cc(mirror(cc));
                in->args[1] = in->args[2];
                in->args[2] = lir_i((i64)x);
                return true;
        }

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

        switch (LirOps[in->op].form) {
        case LF_LI:
        case LF_FLI:
        case LF_MOV:
        case LF_LEA:
        case LF_IBINARY:
        case LF_IUNARY:
        case LF_FBINARY:
        case LF_FUNARY:
        case LF_I2F:
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
tidy(Ty *ty, Lir *L)
{
        u32   n    = vN(L->insts);
        bool *drop = stA0(bool, n);
        u32  *at   = stA(u32, n + 1);

        sweep(ty, L, drop, n);

        for (u32 pc = 0; pc < n; ++pc) {
                if (drop[pc]) {
                        rebuild(L, drop, n, at);
                        return;
                }
        }
}

static bool
fold(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_FOLD") != NULL) {
                return false;
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
                        if (drop[pc]) {
                                continue;
                        }
                        bool moved = fold_address(L, defs, v_(L->insts, pc));
                        if (fold_inst(L, defs, v_(L->insts, pc), &drop[pc]) || moved) {
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

        return any;
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

static void
referenced(Lir const *L, bool const *drop, bool *wanted, u32 n)
{
        memset(wanted, 0, (n + 1) * sizeof *wanted);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                if (v__(L->labels, i).entry) {
                        wanted[v__(L->labels, i).pos] = true;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if ((drop != NULL && drop[pc]) || !jumps(in)) {
                        continue;
                }
                wanted[v__(L->labels, in->args[in->nargs - 1].label).pos] = true;
                for (u32 j = 0; j < in->ntargets; ++j) {
                        wanted[v__(L->labels, in->targets[j]).pos] = true;
                }
        }
}

static bool
prune_once(Lir const *L, bool *drop, bool *wanted, u32 n)
{
        bool changed = false;
        bool dead    = false;

        referenced(L, drop, wanted, n);

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

enum { CELLS = 64, FACTS = 16, REACH = 64 };

typedef struct {
        LirReg  root;
        i64     off;
        u32     size;
        LirType type;
        bool    load;
        bool    known;
        u64     bits;
        LirReg  reg;
        u32     born;
} Cell;

typedef struct {
        LirReg reg;
        bool   eq;
        u64    bits;
} Fact;

typedef struct {
        Cell cells[CELLS];
        Fact facts[FACTS];
        u32  n;
        u32  nfacts;
        u64  fmask;
} State;

typedef struct {
        Cell *cells;
        Fact *facts;
        u32   n;
        u32   nfacts;
} Saved;

typedef struct {
        Lir const *L;
        u32 const *defs;
        LirReg    *root;
        i64       *off;
        u16       *refs;
        u32        pc;
        State      s;
} Fwd;

static void
anchor(Ty *ty, Lir const *L, LirReg *root, i64 *off)
{
        u32  nregs = vN(L->regs);
        u32  n     = vN(L->insts);
        u32 *count = stA0(u32, nregs + 1);

        for (u32 r = 0; r < nregs; ++r) {
                count[r] = (v__(L->regs, r).param != LIR_NONE);
                root[r]  = r;
                off[r]   = 0;
        }

        for (u32 pc = 0; pc < n; ++pc) {
                each_write(v_(L->insts, pc), r) {
                        count[r] += 1;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                LirOpnd const *a  = in->args;
                LirReg         r  = in->dst;
                LirReg         b  = LIR_NONE;
                i64            d  = 0;

                if (r == LIR_NONE || count[r] != 1) {
                        continue;
                }

                if (in->op == LIR_LEA && a[0].mem.index == LIR_NONE && a[0].mem.base != LIR_NONE) {
                        b = a[0].mem.base;
                        d = a[0].mem.disp;
                } else if (in->op == LIR_MOV && a[0].kind == LO_REG) {
                        b = a[0].reg;
                } else if (in->op == LIR_ADD && a[0].kind == LO_REG && a[1].kind == LO_IMM) {
                        b = a[0].reg;
                        d = a[1].imm;
                }

                if (
                        (b == LIR_NONE)
                     || (b == r)
                     || (count[root[b]] != 1)
                     || (v__(L->regs, root[b]).param == LIR_NONE)
                ) {
                        continue;
                }

                root[r] = root[b];
                off[r]  = off[b] + d;
        }
}

static bool
place(Fwd const *f, LirOpnd a, LirReg *root, i64 *off)
{
        if (a.kind != LO_MEM || a.mem.index != LIR_NONE || a.mem.base == LIR_NONE) {
                return false;
        }

        *root = f->root[a.mem.base];
        *off  = f->off[a.mem.base] + a.mem.disp;

        return true;
}

static void
forget(Fwd *f, u32 k)
{
        Cell const *c = &f->s.cells[k];

        f->refs[c->root] -= 1;

        if (!c->known) {
                f->refs[c->reg] -= 1;
        }

        f->s.cells[k] = f->s.cells[--f->s.n];
}

static void
remember(Fwd *f, Cell c)
{
        if (f->s.n == CELLS) {
                forget(f, 0);
        }

        f->refs[c.root] += 1;

        if (!c.known) {
                f->refs[c.reg] += 1;
        }

        f->s.cells[f->s.n++] = c;
}

static void
wipe(Fwd *f)
{
        while (f->s.n != 0) {
                forget(f, f->s.n - 1);
        }
}

inline static bool
factless(State const *s, LirReg r)
{
        return !((s->fmask >> (r & 63)) & 1);
}

static void
remask(State *s)
{
        s->fmask = 0;

        for (u32 k = 0; k < s->nfacts; ++k) {
                s->fmask |= 1ULL << (s->facts[k].reg & 63);
        }
}

static void
unfact(State *s, LirReg r)
{
        if (factless(s, r)) {
                return;
        }

        for (u32 k = s->nfacts; k-- > 0;) {
                if (s->facts[k].reg == r) {
                        s->facts[k] = s->facts[--s->nfacts];
                }
        }
}

static void
written(Fwd *f, LirReg r)
{
        unfact(&f->s, r);

        if (f->refs[r] == 0) {
                return;
        }

        for (u32 k = f->s.n; k-- > 0;) {
                Cell const *c = &f->s.cells[k];
                if (c->root == r || (!c->known && c->reg == r)) {
                        forget(f, k);
                }
        }
}

inline static bool
covers(Cell const *c, i64 lo, i64 hi)
{
        return (c->off <= lo) && (hi <= c->off + c->size);
}

static void
xsplice(Cell *c, i64 lo, u32 size, u64 bits)
{
        u32 shift = 8 * (lo - c->off);
        u64 mask  = (size == 8) ? UINT64_MAX : ((1ULL << (8 * size)) - 1);

        c->bits = (c->bits & ~(mask << shift)) | ((bits & mask) << shift);
}

static void
clobber(Fwd *f, LirReg root, i64 lo, i64 hi, Cell const *merge)
{
        for (u32 k = f->s.n; k-- > 0;) {
                Cell *c = &f->s.cells[k];

                if (c->root != root) {
                        forget(f, k);
                } else if (c->off < hi && lo < c->off + c->size) {
                        if (merge != NULL && c->known && covers(c, lo, hi)) {
                                xsplice(c, lo, merge->size, merge->bits);
                        } else {
                                forget(f, k);
                        }
                }
        }
}

static bool
literal(Fwd const *f, LirOpnd a, LirType type, u64 *bits)
{
        double d;

        if (a.kind == LO_IMM) {
                *bits = (u64)a.imm;
                return true;
        }

        if (a.kind == LO_FIMM && type == LT_F64) {
                memcpy(bits, &a.fimm, sizeof *bits);
                return true;
        }

        if (a.kind != LO_REG) {
                return false;
        }

        if (isint(rcls(f->L, a.reg))) {
                return constant(f->L, f->defs, a, rcls(f->L, a.reg), bits);
        }

        if (type == LT_F64 && fconstant(f->L, f->defs, a, &d)) {
                memcpy(bits, &d, sizeof *bits);
                return true;
        }

        return false;
}

static void
store(Fwd *f, LirInst const *in)
{
        LirType type = LirOps[in->op].type;
        u32     size = lir_type_size(type);
        LirReg  root;
        i64     lo;

        if (!place(f, in->args[0], &root, &lo)) {
                wipe(f);
                return;
        }

        Cell c = {
                .root = root,
                .off  = lo,
                .size = size,
                .type = type,
                .reg  = (in->args[1].kind == LO_REG) ? in->args[1].reg : LIR_NONE,
                .born = f->pc
        };

        c.known = literal(f, in->args[1], type, &c.bits);

        if (c.known && size < 8) {
                c.bits &= (1ULL << (8 * size)) - 1;
        }

        clobber(f, root, lo, lo + size, c.known ? &c : NULL);

        if (c.known || c.reg != LIR_NONE) {
                remember(f, c);
        }
}

static bool
unpack(Fwd const *f, LirInst const *in, LirReg root, i64 lo, LirInst out[static 4])
{
        LirMem m = in->args[0].mem;

        for (u32 k = 0; k < 4; ++k) {
                Cell const *hit = NULL;

                for (u32 j = 0; j < f->s.n && hit == NULL; ++j) {
                        Cell const *c = &f->s.cells[j];
                        if (c->root == root && c->off == lo + 8 * k && c->size == 8) {
                                hit = c;
                        }
                }

                if (hit == NULL) {
                        return false;
                }

                LirClass cls = hit->known ? LIR_I64 : rcls(f->L, hit->reg);

                if (!isint(cls) && !isptr(cls) && cls != LIR_F64) {
                        return false;
                }

                out[k] = (LirInst) {
                        .op     = (cls == LIR_F64) ? LIR_ST_F64 : LIR_ST64,
                        .dst    = LIR_NONE,
                        .args   = {
                                lir_m(m.base, LIR_NONE, 1, m.disp + 8 * k),
                                hit->known ? lir_i((i64)hit->bits) : lir_r(hit->reg)
                        },
                        .nargs  = 2,
                        .tag    = in->tag,
                        .origin = in->origin,
                        .span   = in->span
                };
        }

        return true;
}

static bool
copy(Fwd *f, LirInst const *in, LirInst out[static 4])
{
        LirReg droot;
        LirReg sroot;
        i64    dlo;
        i64    slo;
        Cell   moved[CELLS];
        u32    nmoved = 0;

        if (!place(f, in->args[0], &droot, &dlo)) {
                wipe(f);
                return false;
        }

        bool src  = place(f, in->args[1], &sroot, &slo)
                 && !(sroot == droot && slo < dlo + 32 && dlo < slo + 32);
        bool flat = src && unpack(f, in, sroot, slo, out);

        for (u32 k = 0; src && k < f->s.n; ++k) {
                Cell c = f->s.cells[k];
                if (c.root == sroot && slo <= c.off && c.off + c.size <= slo + 32) {
                        c.root = droot;
                        c.off  = c.off - slo + dlo;
                        moved[nmoved++] = c;
                }
        }

        clobber(f, droot, dlo, dlo + 32, NULL);

        for (u32 k = 0; k < nmoved; ++k) {
                remember(f, moved[k]);
        }

        return flat;
}

static bool
reusable(Lir const *L, Cell const *c, LirInst const *in, LirType type)
{
        if (c->known || rcls(L, c->reg) != rcls(L, in->dst)) {
                return false;
        }

        if (c->load) {
                return c->type == type;
        }

        LirClass cls = rcls(L, c->reg);

        return (c->type == type)
            && (
                       (type == LT_I64 && (cls == LIR_I64 || isptr(cls)))
                    || (type == LT_I32 && cls == LIR_I32)
                    || (type == LT_F64 && cls == LIR_F64)
                    || (type == LT_F32 && cls == LIR_F32)
               );
}

static bool
extend(u64 bits, LirType type, u64 *out)
{
        switch (type) {
        case LT_I8:  *out = (u64)(i64)(i8)bits;  return true;
        case LT_U8:  *out = (u8)bits;            return true;
        case LT_I16: *out = (u64)(i64)(i16)bits; return true;
        case LT_U16: *out = (u16)bits;           return true;
        case LT_I32: *out = (u64)(i64)(i32)bits; return true;
        case LT_U32: *out = (u32)bits;           return true;
        case LT_I64: *out = bits;                return true;
        case LT_F64: *out = bits;                return true;
        default:                                 return false;
        }
}

static void
alias(Fwd *f, LirReg d, LirReg s)
{
        u32 n = vN(f->L->insts);

        if (f->defs[d] < n && f->defs[s] < n && f->root[s] != d) {
                f->root[d] = f->root[s];
                f->off[d]  = f->off[s];
        }
}

static bool
load(Fwd *f, LirInst *in)
{
        Lir const *L    = f->L;
        LirType    type = LirOps[in->op].type;
        u32        size = lir_type_size(type);
        LirClass   cls  = rcls(L, in->dst);
        LirReg     root;
        i64        lo;
        u64        v;
        double     d;

        if (in->flags != 0 || !place(f, in->args[0], &root, &lo)) {
                return false;
        }

        for (u32 k = 0; k < f->s.n; ++k) {
                Cell const *c = &f->s.cells[k];

                if (c->root != root) {
                        continue;
                }

                if (
                        c->known
                     && covers(c, lo, lo + size)
                     && extend(c->bits >> (8 * (lo - c->off)), type, &v)
                ) {
                        if (type == LT_F64 && cls == LIR_F64) {
                                memcpy(&d, &v, sizeof d);
                                become(in, LIR_FLI, lir_f(d));
                                return true;
                        }
                        if (type != LT_F64 && (isint(cls) || cls == LIR_PTR)) {
                                become(in, LIR_LI, lir_i((i64)v));
                                return true;
                        }
                }

                if (
                        (c->off == lo)
                     && (c->size == size)
                     && (f->pc - c->born <= REACH)
                     && reusable(L, c, in, type)
                ) {
                        alias(f, in->dst, c->reg);
                        become(in, LIR_MOV, lir_r(c->reg));
                        return true;
                }
        }

        return false;
}

static bool
opaque(LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_CAS:
        case LF_ATOMIC:
        case LF_CALL:
        case LF_TAILCALL:
        case LF_POLL:
        case LF_RAW:
        case LF_FENCE:
        case LF_ENTRY:
        case LF_RET:
                return true;

        default:
                return false;
        }
}

inline static bool
factual(LirClass cls)
{
        return (cls == LIR_I64) || (cls == LIR_PTR);
}

inline static bool
wide(Lir const *L, LirOpnd a)
{
        return (a.kind == LO_IMM) || (a.kind == LO_REG && factual(rcls(L, a.reg)));
}

static Fact const *
known_fact(State const *s, LirReg r, bool eq)
{
        for (u32 k = 0; k < s->nfacts && !factless(s, r); ++k) {
                if (s->facts[k].reg == r && s->facts[k].eq == eq) {
                        return &s->facts[k];
                }
        }

        return NULL;
}

static bool
valued(Fwd const *f, State const *s, LirOpnd a, u64 *out)
{
        Fact const *x;

        if (a.kind == LO_IMM) {
                *out = (u64)a.imm;
                return true;
        }

        if (a.kind != LO_REG || !factual(rcls(f->L, a.reg))) {
                return false;
        }

        if (constant(f->L, f->defs, a, rcls(f->L, a.reg), out)) {
                return true;
        }

        if ((x = known_fact(s, a.reg, true)) != NULL) {
                *out = x->bits;
                return true;
        }

        return false;
}

static bool
differs(State const *s, LirReg r, u64 bits)
{
        for (u32 k = 0; k < s->nfacts && !factless(s, r); ++k) {
                Fact const *x = &s->facts[k];
                if (x->reg == r && (x->eq ? (x->bits != bits) : (x->bits == bits))) {
                        return true;
                }
        }

        return false;
}

static bool
condition(LirInst const *in, LirCC *cc, LirOpnd *a, LirOpnd *b)
{
        switch (in->op) {
        case LIR_BR:
                *cc = in->args[0].cc;
                *a  = in->args[1];
                *b  = in->args[2];
                return true;

        case LIR_BRZ:
        case LIR_BRNZ:
                *cc = (in->op == LIR_BRZ) ? LIR_EQ : LIR_NE;
                *a  = in->args[0];
                *b  = lir_i(0);
                return true;

        default:
                return false;
        }
}

static bool
decide(Fwd const *f, LirInst const *in, bool *taken)
{
        LirCC   cc;
        LirOpnd a;
        LirOpnd b;
        u64     x;
        u64     y;

        if (!condition(in, &cc, &a, &b) || !wide(f->L, a) || !wide(f->L, b)) {
                return false;
        }

        bool ka = valued(f, &f->s, a, &x);
        bool kb = valued(f, &f->s, b, &y);

        if (ka && kb) {
                *taken = holds(cc, x, y, 0.0, 0.0);
                return true;
        }

        if ((cc != LIR_EQ && cc != LIR_NE) || ka == kb) {
                return false;
        }

        LirOpnd r = ka ? b : a;

        if (r.kind == LO_REG && differs(&f->s, r.reg, ka ? x : y)) {
                *taken = (cc == LIR_NE);
                return true;
        }

        return false;
}

static bool
settled(State const *s, LirReg r, u64 bits)
{
        for (u32 k = 0; k < s->nfacts && !factless(s, r); ++k) {
                Fact const *x = &s->facts[k];
                if (x->reg == r && (x->eq || x->bits == bits)) {
                        return true;
                }
        }

        return false;
}

static void
assume(State *s, u16 *refs, LirReg r, bool eq, u64 bits)
{
        if (settled(s, r, bits)) {
                return;
        }

        if (s->nfacts == FACTS) {
                s->facts[0] = s->facts[--s->nfacts];
        }

        s->facts[s->nfacts++] = (Fact) { r, eq, bits };
        s->fmask             |= 1ULL << (r & 63);

        for (u32 k = 0; eq && k < s->n; ++k) {
                Cell *c    = &s->cells[k];
                u64   mask = (c->size == 8) ? UINT64_MAX : ((1ULL << (8 * c->size)) - 1);
                u64   v;

                if (
                        !c->known
                     && (c->reg == r)
                     && (c->type != LT_F64)
                     && extend(bits & mask, c->type, &v)
                     && (v == bits)
                ) {
                        c->known = true;
                        c->bits  = bits & mask;
                        if (refs != NULL) {
                                refs[r] -= 1;
                        }
                }
        }
}

static void
implied(Fwd const *f, LirInst const *in, bool taken, State *s, u16 *refs)
{
        LirCC   cc;
        LirOpnd a;
        LirOpnd b;
        u64     k;

        if (!condition(in, &cc, &a, &b) || (cc != LIR_EQ && cc != LIR_NE)) {
                return;
        }

        if (valued(f, s, a, &k)) {
                SWAP(LirOpnd, a, b);
        }

        if (
                (a.kind == LO_REG)
             && factual(rcls(f->L, a.reg))
             && wide(f->L, b)
             && valued(f, s, b, &k)
        ) {
                assume(s, refs, a.reg, (cc == LIR_EQ) == taken, k);
        }
}

static void
retain(Fwd *f, LirInst const *in)
{
        LirReg d = in->dst;
        u64    k;

        if (d == LIR_NONE || !factual(rcls(f->L, d))) {
                return;
        }

        if (in->op == LIR_LI && valued(f, &f->s, in->args[0], &k)) {
                assume(&f->s, f->refs, d, true, k);
                return;
        }

        if (in->op != LIR_MOV || in->args[0].kind != LO_REG || in->args[0].reg == d) {
                return;
        }

        for (u32 j = 0, n = f->s.nfacts; j < n && !factless(&f->s, in->args[0].reg); ++j) {
                Fact x = f->s.facts[j];
                if (x.reg == in->args[0].reg) {
                        assume(&f->s, f->refs, d, x.eq, x.bits);
                }
        }
}

static bool
same_cell(Cell *a, Cell const *b)
{
        bool same = (a->root == b->root)
                 && (a->off == b->off)
                 && (a->size == b->size)
                 && (a->type == b->type)
                 && (a->load == b->load)
                 && (a->known == b->known)
                 && (a->known ? (a->bits == b->bits) : (a->reg == b->reg));

        if (same) {
                a->born = min(a->born, b->born);
        }

        return same;
}

static void
meet(State *acc, State const *x)
{
        for (u32 k = acc->n; k-- > 0;) {
                bool hit = false;
                for (u32 j = 0; j < x->n && !hit; ++j) {
                        hit = same_cell(&acc->cells[k], &x->cells[j]);
                }
                if (!hit) {
                        acc->cells[k] = acc->cells[--acc->n];
                }
        }

        for (u32 k = acc->nfacts; k-- > 0;) {
                Fact const *a   = &acc->facts[k];
                bool        hit = false;
                for (u32 j = 0; j < x->nfacts && !hit; ++j) {
                        Fact const *b = &x->facts[j];
                        hit = (a->reg == b->reg) && (a->eq == b->eq) && (a->bits == b->bits);
                }
                if (!hit) {
                        acc->facts[k] = acc->facts[--acc->nfacts];
                }
        }

        remask(acc);
}

static void
save(Ty *ty, Saved *out, State const *s)
{
        out->cells  = stA(Cell, s->n + 1);
        out->facts  = stA(Fact, s->nfacts + 1);
        out->n      = s->n;
        out->nfacts = s->nfacts;

        memcpy(out->cells, s->cells, s->n * sizeof *s->cells);
        memcpy(out->facts, s->facts, s->nfacts * sizeof *s->facts);
}

static void
restore(State *s, Saved const *x)
{
        s->n      = x->n;
        s->nfacts = x->nfacts;

        memcpy(s->cells, x->cells, x->n * sizeof *x->cells);
        memcpy(s->facts, x->facts, x->nfacts * sizeof *x->facts);

        remask(s);
}

static void
adopt(Fwd *f, State const *s)
{
        wipe(f);

        for (u32 k = 0; k < s->n; ++k) {
                remember(f, s->cells[k]);
        }

        f->s.nfacts = s->nfacts;
        f->s.fmask  = s->fmask;
        memcpy(f->s.facts, s->facts, s->nfacts * sizeof *s->facts);
}

typedef struct {
        u32  *first;
        u32  *block;
        u32  *start;
        u32  *from;
        bool *taken;
        bool *cold;
        bool *need;
        bool *dead;
        bool *gone;
        u32   nblocks;
        bool  local;
} Flow;

static bool
cuts(LirInst const *in)
{
        return jumps(in) || ends(in);
}

static void
edge(Flow *g, u32 *count, u32 *ne, bool fill, u32 b, u32 to, bool taken)
{
        if (!fill) {
                count[to] += 1;
                *ne       += 1;
                return;
        }

        u32 at = g->start[to] + --count[to];

        g->from[at]  = b;
        g->taken[at] = taken;
}

static void
blocks(Ty *ty, Lir const *L, bool const *wanted, Flow *g)
{
        u32  n     = vN(L->insts);
        u32  nb    = 0;
        u32  ne    = 0;
        u32 *count;

        g->block = stA(u32, n + 1);
        g->first = stA(u32, n + 2);

        for (u32 pc = 0; pc < n; ++pc) {
                if (pc == 0 || wanted[pc] || cuts(v_(L->insts, pc - 1))) {
                        g->first[nb++] = pc;
                }
                g->block[pc] = nb - 1;
        }

        g->first[nb] = n;
        g->nblocks   = nb;

        count = stA0(u32, nb + 1);

        for (u32 pass = 0; pass < 2; ++pass) {
                for (u32 b = 0; b < nb; ++b) {
                        LirInst const *t = v_(L->insts, g->first[b + 1] - 1);
                        u32            pos;

                        if (!ends(t) && b + 1 < nb) {
                                edge(g, count, &ne, pass == 1, b, b + 1, false);
                        }

                        if (!jumps(t)) {
                                continue;
                        }

                        pos = v__(L->labels, t->args[t->nargs - 1].label).pos;

                        if (pos < n) {
                                edge(g, count, &ne, pass == 1, b, g->block[pos], t->ntargets == 0);
                        }

                        for (u32 j = 0; j < t->ntargets; ++j) {
                                pos = v__(L->labels, t->targets[j]).pos;
                                if (pos < n) {
                                        edge(g, count, &ne, pass == 1, b, g->block[pos], false);
                                }
                        }
                }

                if (pass == 1) {
                        break;
                }

                g->start = stA(u32, nb + 2);
                g->from  = stA(u32, ne + 1);
                g->taken = stA(bool, ne + 1);

                g->start[0] = 0;

                for (u32 b = 0; b < nb; ++b) {
                        g->start[b + 1] = g->start[b] + count[b];
                }
        }
}

enum { FALL, TAKEN, EVERY };

static u32
live(Flow const *g, u32 b, u32 *only)
{
        u32 n = 0;

        for (u32 e = g->start[b]; e < g->start[b + 1]; ++e) {
                if (!g->dead[e]) {
                        *only  = e;
                        n     += 1;
                }
        }

        return n;
}

static bool
joinable(Flow const *g, bool const *entry, u32 b)
{
        u32  only;
        bool ok = !entry[g->first[b]] && !g->cold[b] && !g->local && (live(g, b, &only) != 0);

        for (u32 e = g->start[b]; ok && e < g->start[b + 1]; ++e) {
                ok = g->dead[e] || (g->from[e] < b);
        }

        return ok;
}

static bool
straight(Flow const *g, u32 b)
{
        u32 only;

        return (live(g, b, &only) == 1) && (g->from[only] + 1 == b);
}

static void
sever(Flow *g, u32 p, u32 s, int which)
{
        for (u32 e = g->start[s]; e < g->start[s + 1]; ++e) {
                if (g->from[e] == p && (which == EVERY || g->taken[e] == (which == TAKEN))) {
                        g->dead[e] = true;
                }
        }
}

static u32
target_block(Lir const *L, Flow const *g, LirLabel l)
{
        u32 pos = v__(L->labels, l).pos;

        return (pos < vN(L->insts)) ? g->block[pos] : LIR_NONE;
}

static void
abandon(Lir const *L, Flow *g, u32 p)
{
        LirInst const *t = v_(L->insts, g->first[p + 1] - 1);
        u32            s;

        if (p + 1 < g->nblocks) {
                sever(g, p, p + 1, EVERY);
        }

        if (!jumps(t)) {
                return;
        }

        if ((s = target_block(L, g, t->args[t->nargs - 1].label)) != LIR_NONE) {
                sever(g, p, s, EVERY);
        }

        for (u32 j = 0; j < t->ntargets; ++j) {
                if ((s = target_block(L, g, t->targets[j])) != LIR_NONE) {
                        sever(g, p, s, EVERY);
                }
        }
}

static void
plan(Ty *ty, Lir const *L, bool const *entry, Flow *g)
{
        u32   n    = vN(L->insts);
        bool *hot  = stA0(bool, n + 1);
        bool *cold = stA0(bool, n + 1);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                LirLabelInfo l = v__(L->labels, i);
                if (l.pos < n) {
                        *(l.cold ? &cold[l.pos] : &hot[l.pos]) = true;
                }
        }

        g->cold = stA0(bool, g->nblocks + 1);
        g->need = stA0(bool, g->nblocks + 1);
        g->gone = stA0(bool, g->nblocks + 1);
        g->dead = stA0(bool, g->start[g->nblocks] + 1);

        for (u32 b = 0; b < g->nblocks; ++b) {
                u32 pos = g->first[b];
                g->cold[b] = cold[pos] && !hot[pos];
        }

        for (u32 b = 0; b < g->nblocks; ++b) {
                if (!joinable(g, entry, b) || straight(g, b)) {
                        continue;
                }
                for (u32 e = g->start[b]; e < g->start[b + 1]; ++e) {
                        g->need[g->from[e]] = true;
                }
        }
}

static void
enter(Fwd *f, Flow *g, Saved const *out, bool const *entry, u32 b, State *acc, State *x)
{
        Lir const *L    = f->L;
        u32        only;
        bool       some = (live(g, b, &only) != 0);
        bool       open = (b == 0) || entry[g->first[b]];

        g->gone[b] = !some && !open && !g->local && (g->start[b] < g->start[b + 1]);

        if (!joinable(g, entry, b)) {
                wipe(f);
                f->s.nfacts = 0;
                f->s.fmask  = 0;
                return;
        }

        if (straight(g, b)) {
                implied(f, v_(L->insts, g->first[b] - 1), g->taken[only], &f->s, f->refs);
                return;
        }

        bool first = true;

        for (u32 e = g->start[b]; e < g->start[b + 1]; ++e) {
                if (g->dead[e]) {
                        continue;
                }

                u32            p    = g->from[e];
                LirInst const *t    = v_(L->insts, g->first[p + 1] - 1);
                State         *into = first ? acc : x;

                restore(into, &out[p]);
                implied(f, t, g->taken[e], into, NULL);

                if (!first) {
                        meet(acc, x);
                }

                first = false;
        }

        adopt(f, acc);
}

enum { STILL, MOVED, OPENED };

static int
forward(Ty *ty, Lir *L, LirReg *root, i64 *off)
{
        u32    n      = vN(L->insts);
        u32   *defs   = stA(u32, vN(L->regs) + 1);
        bool  *wanted = stA(bool, n + 1);
        bool  *entry  = stA0(bool, n + 1);
        bool  *drop   = stA0(bool, n + 1);
        Fwd   *f      = stA(Fwd, 1);
        State *acc    = stA(State, 2);
        int    any    = STILL;
        bool   cut    = false;
        Flow   g;

        f->L        = L;
        f->defs     = defs;
        f->root     = root;
        f->off      = off;
        f->refs     = stA0(u16, vN(L->regs) + 1);
        f->s.n      = 0;
        f->s.nfacts = 0;
        f->s.fmask  = 0;

        u32      ncopy = 0;
        u32      nflat = 0;
        u32     *flat  = stA(u32, n + 1);
        LirInst *parts;

        memset(defs, 0xff, vN(L->regs) * sizeof *defs);
        memset(flat, 0xff, (n + 1) * sizeof *flat);

        for (u32 pc = 0; pc < n; ++pc) {
                each_write(v_(L->insts, pc), reg) {
                        defs[reg] = (defs[reg] == LIR_NONE) ? pc : n;
                }
                ncopy += (v__(L->insts, pc).op == LIR_COPY32);
        }

        for (u32 i = 0; i < vN(L->labels); ++i) {
                LirLabelInfo l = v__(L->labels, i);
                if (l.entry && l.pos <= n) {
                        entry[l.pos] = true;
                }
        }

        parts = stA(LirInst, 4 * ncopy + 1);

        referenced(L, NULL, wanted, n);

        if (n == 0) {
                return STILL;
        }

        blocks(ty, L, wanted, &g);

        g.local = (getenv("TY_LIR_NO_GLOBAL") != NULL);

        plan(ty, L, entry, &g);

        Saved *out = stA(Saved, g.nblocks + 1);

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst *in   = v_(L->insts, pc);
                LirForm  form = LirOps[in->op].form;
                bool     hit  = false;
                bool     taken;

                if (g.first[g.block[pc]] == pc && (!g.local || wanted[pc])) {
                        enter(f, &g, out, entry, g.block[pc], &acc[0], &acc[1]);
                }

                u32  blk  = g.block[pc];
                bool last = (g.first[blk + 1] == pc + 1);

                if (last && g.gone[blk]) {
                        abandon(L, &g, blk);
                } else if (last && decide(f, in, &taken)) {
                        u32 to = target_block(L, &g, in->args[in->nargs - 1].label);
                        if (taken && blk + 1 < g.nblocks) {
                                sever(&g, blk, blk + 1, FALL);
                        }
                        if (!taken && to != LIR_NONE) {
                                sever(&g, blk, to, TAKEN);
                        }
                        if (taken) {
                                become(in, LIR_JMP, in->args[in->nargs - 1]);
                        } else {
                                drop[pc] = true;
                        }
                        any = OPENED;
                        cut = cut || !taken;
                }

                f->pc = pc;

                switch (form) {
                case LF_LD:   hit = load(f, in);  break;
                case LF_ST:   store(f, in);       break;
                case LF_COPY:
                        if (copy(f, in, &parts[4 * nflat])) {
                                flat[pc] = nflat++;
                        }
                        break;
                default:
                        if (opaque(in)) {
                                wipe(f);
                        }
                        break;
                }

                if (hit) {
                        any = max(any, (in->op == LIR_MOV) ? MOVED : OPENED);
                }

                each_write(in, r) {
                        written(f, r);
                }

                retain(f, in);

                LirReg root;
                i64    lo;

                if (
                        (form == LF_LD)
                     && !hit
                     && place(f, in->args[0], &root, &lo)
                     && (root != in->dst)
                ) {
                        remember(f, (Cell) {
                                .root = root,
                                .off  = lo,
                                .size = lir_type_size(LirOps[in->op].type),
                                .type = LirOps[in->op].type,
                                .load = true,
                                .reg  = in->dst,
                                .born = pc
                        });
                }

                if (g.first[g.block[pc] + 1] == pc + 1 && g.need[g.block[pc]]) {
                        save(ty, &out[g.block[pc]], &f->s);
                }
        }

        if (nflat == 0 && !cut) {
                return any;
        }

        any = OPENED;

        LirInst *old = lir_swap(L);

        for (u32 pc = 0; pc < n; ++pc) {
                flat[pc] = (flat[pc] == LIR_NONE) ? LIR_NONE : 4 * flat[pc];
                u32 here = vN(L->insts);
                if (flat[pc] == LIR_NONE && !drop[pc]) {
                        lir_emit_owned(L, &old[pc]);
                }
                for (u32 k = 0; flat[pc] != LIR_NONE && k < 4; ++k) {
                        lir_emit(L, &parts[flat[pc] + k]);
                }
                flat[pc] = here;
        }

        flat[n] = vN(L->insts);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                v_(L->labels, i)->pos = flat[v__(L->labels, i).pos];
        }

        return any;
}

typedef struct {
        LirReg root;
        i64    lo;
        i64    hi;
} Span;

typedef struct {
        Lir const *L;
        LirReg    *root;
        i64       *off;
        Span      *keep;
        u32        nkeep;
        u16       *refs;
        Span       dead[CELLS];
        u32        n;
} Dse;

inline static bool
stacky(Lir const *L, LirReg r)
{
        u32 pin = v__(L->regs, r).pin;
        return (pin < 8) && ((L->stack_pins >> pin) & 1);
}

static bool
spot(Dse const *s, LirOpnd a, Span *out)
{
        if (a.kind != LO_MEM || a.mem.index != LIR_NONE || a.mem.base == LIR_NONE) {
                return false;
        }

        out->root = s->root[a.mem.base];
        out->lo   = s->off[a.mem.base] + a.mem.disp;

        return true;
}

static void
unbury(Dse *s, u32 k)
{
        s->refs[s->dead[k].root] -= 1;
        s->dead[k] = s->dead[--s->n];
}

static void
exhume(Dse *s)
{
        while (s->n != 0) {
                unbury(s, s->n - 1);
        }
}

static void
revive(Dse *s, Span x)
{
        for (u32 k = s->n; k-- > 0;) {
                Span const *d = &s->dead[k];
                if (d->root != x.root || (d->lo < x.hi && x.lo < d->hi)) {
                        unbury(s, k);
                }
        }
}

static bool
buried(Dse const *s, Span x)
{
        for (i64 b = x.lo; b < x.hi; ++b) {
                bool hit = false;
                for (u32 k = 0; k < s->n && !hit; ++k) {
                        Span const *d = &s->dead[k];
                        hit = (d->root == x.root) && (d->lo <= b) && (b < d->hi);
                }
                if (!hit) {
                        return false;
                }
        }

        return true;
}

static bool
kept(Dse const *s, Span x)
{
        for (u32 k = 0; k < s->nkeep; ++k) {
                Span const *p = &s->keep[k];
                if (p->root == LIR_NONE || p->root != x.root || (p->lo < x.hi && x.lo < p->hi)) {
                        return true;
                }
        }

        return false;
}

static void
inter(Dse *s, Span x)
{
        if (s->n == CELLS) {
                unbury(s, 0);
        }

        s->refs[x.root] += 1;
        s->dead[s->n++] = x;
}

static bool
inert(LirInst const *in)
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
                return in->flags == 0;

        default:
                return false;
        }
}

static bool
bury(Ty *ty, Lir *L, LirReg *root, i64 *off)
{
        u32   n    = vN(L->insts);
        bool *drop = stA0(bool, n);
        u32  *at   = stA(u32, n + 1);
        Dse  *s    = stA(Dse, 1);
        bool  any  = false;
        Span  x;

        s->L     = L;
        s->root  = root;
        s->off   = off;
        s->keep  = stA(Span, n + 1);
        s->nkeep = 0;
        s->refs  = stA0(u16, vN(L->regs) + 1);
        s->n     = 0;

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);

                if (LirOps[in->op].form != LF_LD || in->flags == 0) {
                        continue;
                }

                if (!spot(s, in->args[0], &x)) {
                        if (stacky(L, in->args[0].mem.base)) {
                                s->keep[s->nkeep++] = (Span) { LIR_NONE, 0, 0 };
                        }
                } else if (stacky(L, x.root)) {
                        x.hi = x.lo + lir_type_size(LirOps[in->op].type);
                        s->keep[s->nkeep++] = x;
                }
        }

        for (u32 pc = n; pc-- > 0;) {
                LirInst const *in   = v_(L->insts, pc);
                LirForm        form = LirOps[in->op].form;

                each_write(in, r) {
                        for (u32 k = s->n; s->refs[r] != 0 && k-- > 0;) {
                                if (s->dead[k].root == r) {
                                        unbury(s, k);
                                }
                        }
                }

                switch (form) {
                case LF_ST:
                case LF_COPY:
                        if (!spot(s, in->args[0], &x)) {
                                break;
                        }
                        x.hi = x.lo + ((form == LF_COPY) ? 32 : lir_type_size(LirOps[in->op].type));
                        if (in->flags == 0 && stacky(L, x.root) && buried(s, x) && !kept(s, x)) {
                                drop[pc] = true;
                                any      = true;
                                break;
                        }
                        inter(s, x);
                        if (form == LF_COPY) {
                                if (spot(s, in->args[1], &x)) {
                                        x.hi = x.lo + 32;
                                        revive(s, x);
                                } else {
                                        exhume(s);
                                }
                        }
                        break;

                case LF_LD:
                        if (spot(s, in->args[0], &x)) {
                                x.hi = x.lo + lir_type_size(LirOps[in->op].type);
                                revive(s, x);
                        } else {
                                exhume(s);
                        }
                        break;

                default:
                        if (!inert(in)) {
                                exhume(s);
                        }
                        break;
                }
        }

        if (any) {
                rebuild(L, drop, n, at);
        }

        return any;
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

static bool
having(Lir const *L, bool (*want)(LirInst const *))
{
        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                if (want(v_(L->insts, pc))) {
                        return true;
                }
        }

        return false;
}

static bool
copies(LirInst const *in)
{
        return (in->op == LIR_MOV) && (in->args[0].kind == LO_REG);
}

static bool
sets(LirInst const *in)
{
        return (in->op == LIR_SETCC) || (in->op == LIR_FSETCC);
}

static bool
jmps(LirInst const *in)
{
        return (in->op == LIR_JMP);
}

static bool
negate(LirCC cc, LirCC *out)
{
        switch (cc) {
        case LIR_EQ:  *out = LIR_NE;  return true;
        case LIR_NE:  *out = LIR_EQ;  return true;
        case LIR_LT:  *out = LIR_GE;  return true;
        case LIR_GE:  *out = LIR_LT;  return true;
        case LIR_LE:  *out = LIR_GT;  return true;
        case LIR_GT:  *out = LIR_LE;  return true;
        case LIR_ULT: *out = LIR_UGE; return true;
        case LIR_UGE: *out = LIR_ULT; return true;
        case LIR_ULE: *out = LIR_UGT; return true;
        case LIR_UGT: *out = LIR_ULE; return true;
        case LIR_FEQ: *out = LIR_FNE; return true;
        case LIR_FNE: *out = LIR_FEQ; return true;
        default:                      return false;
        }
}

static LirReg
tested(LirInst const *in, bool *truth)
{
        LirOpnd const *a = in->args;

        switch (in->op) {
        case LIR_BRZ:
        case LIR_BRNZ:
                *truth = (in->op == LIR_BRNZ);
                return (a[0].kind == LO_REG) ? a[0].reg : LIR_NONE;

        case LIR_BR:
        case LIR_SELECT:
                if (
                        (a[1].kind != LO_REG)
                     || (a[2].kind != LO_IMM)
                     || (a[2].imm != 0)
                     || (a[0].cc != LIR_EQ && a[0].cc != LIR_NE)
                ) {
                        return LIR_NONE;
                }
                *truth = (a[0].cc == LIR_NE);
                return a[1].reg;

        default:
                return LIR_NONE;
        }
}

static bool
untouched(Lir const *L, LirInst const *def, u32 from, u32 to, bool const *start)
{
        for (u32 pc = from; pc < to; ++pc) {
                if (start[pc]) {
                        return false;
                }
                each_write(v_(L->insts, pc), w) {
                        for (u32 k = 1; k <= 2; ++k) {
                                if (def->args[k].kind == LO_REG && def->args[k].reg == w) {
                                        return false;
                                }
                        }
                }
        }

        return !start[to];
}

static void
fuse(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_FUSE") != NULL || !having(L, sets)) {
                return;
        }

        u32   n     = vN(L->insts);
        u32   nregs = vN(L->regs);
        u32  *defs  = stA(u32, nregs + 1);
        u32  *reads = stA0(u32, nregs + 1);
        bool *start = stA0(bool, n + 1);
        bool  any   = false;

        memset(defs, 0xff, (nregs + 1) * sizeof *defs);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                u32 pos = v__(L->labels, i).pos;
                if (pos <= n) {
                        start[pos] = true;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                each_write(in, r) {
                        defs[r] = (defs[r] == LIR_NONE) ? pc : n;
                }
                each_read(in, r) {
                        reads[r] += 1;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst *in = v_(L->insts, pc);
                bool     truth;
                LirReg   r  = tested(in, &truth);
                u32      at = (r == LIR_NONE) ? n : defs[r];

                if (at >= pc || reads[r] != 1 || v__(L->regs, r).pin != LIR_NONE) {
                        continue;
                }

                LirInst const *def  = v_(L->insts, at);
                bool           real = (def->op == LIR_FSETCC);
                LirCC          cc   = def->args[0].cc;

                if (
                        (def->op != LIR_SETCC && !real)
                     || (in->op == LIR_SELECT && real)
                     || (!truth && !negate(cc, &cc))
                     || !untouched(L, def, at + 1, pc, start)
                ) {
                        continue;
                }

                if (in->op == LIR_SELECT) {
                        in->args[0] = lir_cc(cc);
                        in->args[1] = def->args[1];
                        in->args[2] = def->args[2];
                } else {
                        *in = (LirInst) {
                                .op     = real ? LIR_FBR : LIR_BR,
                                .dst    = LIR_NONE,
                                .args   = {
                                        lir_cc(cc),
                                        def->args[1],
                                        def->args[2],
                                        in->args[in->nargs - 1]
                                },
                                .nargs  = 4,
                                .flags  = in->flags,
                                .tag    = in->tag,
                                .origin = in->origin,
                                .span   = in->span
                        };
                }

                reads[r] = 0;
                any      = true;
        }

        if (any) {
                tidy(ty, L);
        }
}

static u32
substitute(LirInst *in, LirReg from, LirReg to)
{
        u32 n = 0;

        for (u32 j = 0; j < nopnd(in); ++j) {
                LirOpnd *a = opnd(in, j);

                if (a->kind == LO_REG && a->reg == from) {
                        a->reg  = to;
                        n      += 1;
                }

                if (a->kind != LO_MEM) {
                        continue;
                }

                if (a->mem.base  == from) { a->mem.base  = to; n += 1; }
                if (a->mem.index == from) { a->mem.index = to; n += 1; }
        }

        return n;
}

static void
propagate(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_COPYPROP") != NULL || !having(L, copies)) {
                return;
        }

        u32   n     = vN(L->insts);
        u32   nregs = vN(L->regs);
        u32  *defs  = stA0(u32, nregs + 1);
        u32  *reads = stA0(u32, nregs + 1);
        bool *start = stA0(bool, n + 1);
        bool  any   = false;

        for (u32 i = 0; i < vN(L->labels); ++i) {
                u32 pos = v__(L->labels, i).pos;
                if (pos <= n) {
                        start[pos] = true;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                each_write(in, r) {
                        defs[r] += 1;
                }
                each_read(in, r) {
                        reads[r] += 1;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *mv = v_(L->insts, pc);
                LirReg         d  = mv->dst;

                if (
                        (mv->op != LIR_MOV)
                     || (mv->flags != 0)
                     || (mv->args[0].kind != LO_REG)
                     || (defs[d] != 1)
                     || (reads[d] == 0)
                     || (v__(L->regs, d).pin != LIR_NONE)
                     || (v__(L->regs, d).param != LIR_NONE)
                     || (rcls(L, d) != rcls(L, mv->args[0].reg))
                ) {
                        continue;
                }

                LirReg s    = mv->args[0].reg;
                u32    left = reads[d];

                for (u32 q = pc + 1; q < n && q < pc + 64 && left != 0 && !start[q]; ++q) {
                        LirInst *in   = v_(L->insts, q);
                        bool     stop = jumps(in) || ends(in) || (in->op == LIR_RAW);
                        u32      k    = (in->op == LIR_RAW) ? 0 : substitute(in, d, s);

                        left -= k;
                        any  |= (k != 0);

                        each_write(in, w) {
                                stop = stop || (w == s);
                        }

                        if (stop) {
                                break;
                        }
                }

                reads[s] += reads[d] - left;
                reads[d]  = left;
        }

        if (any) {
                tidy(ty, L);
        }
}

static bool
invert(LirInst *br)
{
        LirCC cc;

        switch (br->op) {
        case LIR_BRZ:  br->op = LIR_BRNZ; return true;
        case LIR_BRNZ: br->op = LIR_BRZ;  return true;

        case LIR_BR:
        case LIR_FBR:
                if (!negate(br->args[0].cc, &cc)) {
                        return false;
                }
                br->args[0] = lir_cc(cc);
                return true;

        default:
                return false;
        }
}

static bool
copyable(LirInst const *in)
{
        switch (LirOps[in->op].form) {
        case LF_MOV:
                return (in->args[0].kind != LO_VSLOT) && (in->flags == 0);

        case LF_LI:
        case LF_FLI:
        case LF_LEA:
        case LF_IUNARY:
        case LF_SETCC:
                return in->flags == 0;

        case LF_IBINARY:
                return (in->flags == 0) && !division(in->op);

        default:
                return false;
        }
}

static void
rotate(Ty *ty, Lir *L)
{
        if (getenv("TY_LIR_NO_ROTATE") != NULL || !having(L, jmps)) {
                return;
        }

        enum { PREFIX = 4 };

        u32       n    = vN(L->insts);
        LirLabel *body = stA(LirLabel, n + 1);
        LirLabel *tail = stA(LirLabel, n + 1);
        u32      *from = stA(u32, n + 1);
        u32      *at   = stA(u32, n + 1);
        bool      any  = false;

        memset(body, 0xff, (n + 1) * sizeof *body);
        memset(tail, 0xff, (n + 1) * sizeof *tail);
        memset(from, 0xff, (n + 1) * sizeof *from);

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = v_(L->insts, pc);
                u32            h  = (in->op == LIR_JMP) ? v__(L->labels, in->args[0].label).pos : n;
                u32            k  = h;

                while (k < pc && k < h + PREFIX && copyable(v_(L->insts, k))) {
                        k += 1;
                }

                if (k >= pc || k + 1 >= n || v__(L->insts, k + 1).op == LIR_ENTRY) {
                        continue;
                }

                LirInst  br = v__(L->insts, k);
                LirLabel to = br.args[br.nargs - 1].label;

                if (
                        (LirOps[br.op].form == LF_JMP)
                     || !invert(&br)
                     || (v__(L->labels, to).pos <= k + 1)
                ) {
                        continue;
                }

                if (body[k] == LIR_NONE) {
                        body[k] = label_at(L, k + 1);
                }

                if (body[k] == LIR_NONE) {
                        body[k] = lir_label(L);
                        v_(L->labels, body[k])->pos = k + 1;
                }

                from[pc] = h;
                tail[pc] = (v__(L->labels, to).pos != pc + 1) ? to : LIR_NONE;
                any      = true;
        }

        if (!any) {
                return;
        }

        LirInst *old = lir_swap(L);

        for (u32 pc = 0; pc < n; ++pc) {
                at[pc] = vN(L->insts);

                if (from[pc] == LIR_NONE) {
                        lir_emit_owned(L, &old[pc]);
                        continue;
                }

                u32 k = from[pc];

                for (; LirOps[old[k].op].form != LF_BR
                    && LirOps[old[k].op].form != LF_FBR
                    && LirOps[old[k].op].form != LF_BRZ; ++k) {
                        LirInst copy = old[k];
                        copy.origin  = old[pc].origin;
                        lir_emit(L, &copy);
                }

                LirInst br = old[k];

                invert(&br);
                br.args[br.nargs - 1] = lir_l(body[k]);
                br.origin             = old[pc].origin;

                lir_emit(L, &br);

                if (tail[pc] != LIR_NONE) {
                        lvP(L->insts, ((LirInst) {
                                .op     = LIR_JMP,
                                .dst    = LIR_NONE,
                                .args   = { lir_l(tail[pc]) },
                                .nargs  = 1,
                                .origin = old[pc].origin
                        }));
                }
        }

        at[n] = vN(L->insts);

        for (u32 i = 0; i < vN(L->labels); ++i) {
                LirLabelInfo *l = v_(L->labels, i);
                if (l->pos != LIR_NONE) {
                        l->pos = at[l->pos];
                }
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

        bool    fwd  = (getenv("TY_LIR_NO_FORWARD") == NULL);
        bool    dse  = (getenv("TY_LIR_NO_DSE") == NULL);
        LirReg *root = stA(LirReg, vN(L->regs) + 1);
        i64    *off  = stA(i64, vN(L->regs) + 1);

        if (fwd || dse) {
                anchor(ty, L, root, off);
        }

        for (u32 round = 0; fwd && round < 32; ++round) {
                int got = forward(ty, L, root, off);
                if (got == STILL) {
                        break;
                }
                bool folded = fold(ty, L);
                prune(ty, L);
                if (got == MOVED || !folded) {
                        break;
                }
        }

        if (dse && bury(ty, L, root, off)) {
                tidy(ty, L);
        }

        number(ty, L);
        propagate(ty, L);
        fuse(ty, L);
        rotate(ty, L);

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
