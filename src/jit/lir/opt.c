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
division(LirOp op)
{
        return (op == LIR_SDIV) || (op == LIR_UDIV)
            || (op == LIR_SREM) || (op == LIR_UREM);
}

bool
lir_optimize(Ty *ty, Lir *L)
{
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

        SCRATCH_SAVE();

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
                LirInst *old = vv(L->insts);

                v00(L->insts);

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

                xmF(old);
        }

        SCRATCH_RESTORE();

        return L->error.kind == LE_NONE;
}
