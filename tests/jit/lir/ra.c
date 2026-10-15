#include "test.h"

static LirTarget const Mock = {
        .arch        = LIR_ARCH_X64,
        .abi         = LIR_ABI_SYSV,
        .name        = "test",
        .gpr         = {
                .available    = 15,
                .callee_saved = 12,
                .args         = { 0, 1, 2, 3 },
                .nargs        = 4,
                .ret          = 0,
                .scratch      = { 11 },
                .nscratch     = 1
        },
        .fpr         = {
                .available = 15,
                .args      = { 0, 1, 2, 3 },
                .nargs     = 4,
                .ret       = 0
        },
        .pins        = { 3 },
        .npins       = 1,
        .stack_align = 16
};

static LirAlloc
allocate(Lir *L, LirTarget const *target, LirConstraint const *cs, u32 n)
{
        LirCFG   cfg;
        LirError err;
        LirAlloc alloc = {0};

        CHECK(lir_validate(ty, L, &err));

        bool ok = lir_cfg(ty, L, &cfg, &err);
        CHECK(ok);

        if (!ok) {
                exit(1);
        }

        ok = lir_allocate(ty, L, &cfg, target, cs, n, &alloc, &err);
        CHECK(ok);

        if (!ok) {
                fprintf(stderr, "%s\n", err.message);
                exit(1);
        }

        ok = lir_check_alloc(ty, L, &cfg, target, &alloc, &err);
        CHECK(ok);

        if (!ok) {
                fprintf(stderr, "%s\n", err.message);
                lir_dump(L, stderr);
                lir_dump_alloc(L, &alloc, stderr);
        }

        CHECK(alloc.nintervals == vN(L->regs));
        CHECK(alloc.frame_size % target->stack_align == 0);

        return alloc;
}

static bool
stacked(LirAlloc const *alloc, LirReg r)
{
        LirInterval const *i = &alloc->intervals[alloc->intervals[r].rep];

        for (u32 k = 0; k < i->npieces; ++k) {
                if (i->pieces[k].phys == LIR_PHYS_NONE) {
                        return true;
                }
        }

        return false;
}

static u32
count_moves(LirAlloc const *alloc, LirMovePhase phase, bool loads)
{
        u32 n = 0;

        for (u32 i = 0; i < alloc->nmoves; ++i) {
                LirMove const *m = &alloc->moves[i];
                if (m->kind == LIR_MOVE_COPY && m->phase == phase) {
                        n += !loads || (m->from_slot != LIR_NONE);
                }
        }

        return n;
}

static void
check_pressure(void)
{
        LirType types[48];

        for (u32 f = 0; f < 2; ++f) {
                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LT_F64 : LT_I64;
                }

                Lir   *L   = fna(types[0], types);
                LirReg acc = lir_reg(L, f ? LIR_F64 : LIR_I64);
                LirOp  add = f ? LIR_FADD : LIR_ADD;

                put(L, f ? LIR_FLI : LIR_LI, acc, f ? lir_f(0.0) : lir_i(0));

                for (u32 i = 0; i < countof(types); ++i) {
                        put(L, add, acc, lir_r(acc), lir_r(L->params[i]));
                }

                ret(L, acc);

                WITH_SCRATCH {
                        LirAlloc alloc   = allocate(L, &Mock, NULL, 0);
                        u32      spilled = 0;

                        for (u32 i = 0; i < countof(types); ++i) {
                                spilled += stacked(&alloc, L->params[i]);
                        }

                        CHECK(spilled >= 40);
                        CHECK(alloc.spill_size >= 40 * 8);
                        CHECK(!stacked(&alloc, acc));
                }

                lir_free(L);
        }
}

static void
check_loops(void)
{
        Lir     *L    = fn(LT_I64, LT_I64);
        LirReg   i    = lir_reg(L, LIR_I64);
        LirReg   sum  = lir_reg(L, LIR_I64);
        LirReg   dead = lir_reg(L, LIR_I64);
        LirLabel top  = lir_label(L);

        put(L, LIR_LI, i, lir_i(0));
        put(L, LIR_LI, sum, lir_i(0));
        here(L, top);
        put(L, LIR_ADD, sum, lir_r(sum), lir_r(i));
        put(L, LIR_ADD, i, lir_r(i), lir_i(1));
        put(L, LIR_BR, LIR_NONE, lir_cc(LIR_LT), lir_r(i), lir_r(L->params[0]), lir_l(top));
        ret(L, sum);

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &Mock, NULL, 0);
                LirInterval const *x = &alloc.intervals[i];
                LirInterval const *y = &alloc.intervals[sum];
                CHECK(x->nranges == 2 && x->ranges[0].start == LIR_OUT(0));
                CHECK(x->ranges[0].end == LIR_IN(3) + 1 && x->ranges[1].start == LIR_OUT(3));
                CHECK(x->ranges[1].end == LIR_IN(5));
                CHECK(y->ranges[y->nranges - 1].end > LIR_IN(5));
                CHECK(alloc.intervals[dead].nranges == 0);
                CHECK(alloc.nmoves == 0);
                CHECK(!stacked(&alloc, i) && !stacked(&alloc, sum));
        }

        lir_free(L);
}

static void
check_calls(void)
{
        LirTarget t = Mock;

        for (u32 saved = 0; saved < 2; ++saved) {
                Lir *L = fn(LT_I64, LT_I64, LT_I64);

                push(L, vcall(lir_i(1)));

                LirReg d = lir_reg(L, LIR_I64);

                put(L, LIR_ADD, d, lir_r(L->params[0]), lir_r(L->params[1]));
                ret(L, d);

                t.gpr.callee_saved = saved ? 12 : 0;

                WITH_SCRATCH {
                        LirAlloc alloc = allocate(L, &t, NULL, 0);
                        if (saved) {
                                CHECK(alloc.saved_gpr == 12);
                                CHECK(alloc.nmoves == 0);
                        } else {
                                CHECK(stacked(&alloc, L->params[0]));
                                CHECK(stacked(&alloc, L->params[1]));
                                CHECK(count_moves(&alloc, LIR_MOVE_BEFORE, true) == 2);
                        }
                }

                lir_free(L);
        }

        Lir    *L   = fn(LT_I64, LT_I64);
        LirReg  x   = L->params[0];
        LirOpnd arg = lir_r(x);

        push(L, call(lir_i(1), x, sig(LT_I64, T(LT_I64), 1), &arg));
        ret(L, x);

        t.gpr.callee_saved = 0;

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &t, NULL, 0);
                CHECK(alloc.nmoves == 0);
                CHECK(!stacked(&alloc, x));
        }

        lir_free(L);
}

static void
check_loop_calls(void)
{
        Lir     *L   = fn(LT_I64, LT_I64);
        LirReg   i   = lir_reg(L, LIR_I64);
        LirReg   sum = lir_reg(L, LIR_I64);
        LirLabel top = lir_label(L);
        LirLabel end = lir_label(L);

        put(L, LIR_LI, i, lir_i(0));
        put(L, LIR_LI, sum, lir_i(0));
        here(L, top);
        put(L, LIR_BR, LIR_NONE, lir_cc(LIR_GE), lir_r(i), lir_r(L->params[0]), lir_l(end));
        push(L, vcall(lir_i(1)));
        put(L, LIR_ADD, sum, lir_r(sum), lir_r(i));
        put(L, LIR_ADD, i, lir_r(i), lir_i(1));
        put(L, LIR_JMP, LIR_NONE, lir_l(top));
        here(L, end);
        ret(L, sum);

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &Mock, NULL, 0);
                u8       pi    = lir_where(&alloc, i, LIR_IN(3)).phys;
                u8       ps    = lir_where(&alloc, sum, LIR_IN(3)).phys;
                CHECK(pi != LIR_PHYS_NONE && (Mock.gpr.callee_saved >> pi) & 1);
                CHECK(ps != LIR_PHYS_NONE && (Mock.gpr.callee_saved >> ps) & 1);
                CHECK(count_moves(&alloc, LIR_MOVE_BEFORE, false) <= 2);
        }

        lir_free(L);
}

static void
check_remat(void)
{
        LirTarget t = Mock;
        Lir      *L = fn(LT_I64, LT_I64);
        LirReg    k = lir_reg(L, LIR_I64);
        LirReg    d = lir_reg(L, LIR_I64);

        t.gpr.callee_saved = 0;

        put(L, LIR_LI, k, lir_i(12345));
        push(L, vcall(lir_i(1)));
        push(L, vcall(lir_i(1)));
        put(L, LIR_ADD, d, lir_r(L->params[0]), lir_r(k));
        ret(L, d);

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &t, NULL, 0);
                u32      remat = 0;

                CHECK(alloc.intervals[k].remat == 0);
                CHECK(alloc.intervals[k].spill == LIR_NONE);

                for (u32 i = 0; i < alloc.nmoves; ++i) {
                        remat += (alloc.moves[i].remat == 0);
                }

                CHECK(remat == 1);
        }

        lir_free(L);
}

static void
check_coalesce(void)
{
        Lir   *L = fn(LT_I64, LT_I64);
        LirReg a = lir_reg(L, LIR_I64);
        LirReg b = lir_reg(L, LIR_I64);
        LirReg c = lir_reg(L, LIR_I64);

        put(L, LIR_ADD, a, lir_r(L->params[0]), lir_i(1));
        put(L, LIR_MOV, b, lir_r(a));
        put(L, LIR_MOV, c, lir_r(b));
        put(L, LIR_ADD, c, lir_r(c), lir_i(2));
        ret(L, c);

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &Mock, NULL, 0);
                CHECK(alloc.intervals[a].rep == alloc.intervals[b].rep);
                CHECK(alloc.intervals[b].rep == alloc.intervals[c].rep);
                CHECK(alloc.nmoves == 0);
        }

        lir_free(L);

        L = fn(LT_I64, LT_I64);
        a = lir_reg(L, LIR_I64);
        b = lir_reg(L, LIR_I64);

        put(L, LIR_ADD, a, lir_r(L->params[0]), lir_i(1));
        put(L, LIR_MOV, b, lir_r(a));
        put(L, LIR_ADD, a, lir_r(a), lir_i(1));
        put(L, LIR_ADD, b, lir_r(b), lir_r(a));
        ret(L, b);

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &Mock, NULL, 0);
                CHECK(alloc.intervals[a].rep != alloc.intervals[b].rep);
        }

        lir_free(L);
}

static void
check_roots(void)
{
        LirType types[48];

        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = LT_REF;
        }

        Lir    *L  = fna(LT_VOID, types);
        LirInst gc = vcall(lir_i(1));

        gc.flags = LIR_MAY_GC;
        push(L, gc);

        for (u32 i = 0; i < countof(types); ++i) {
                put(L, LIR_MOV, lir_reg(L, LIR_REF), lir_r(L->params[i]));
        }

        ret(L, LIR_NONE);

        WITH_SCRATCH {
                LirAlloc alloc   = allocate(L, &Mock, NULL, 0);
                u32      roots   = 0;
                u32      spilled = 0;

                CHECK(alloc.nvslots == 48);

                for (u32 i = 0; i < alloc.nmoves; ++i) {
                        LirMove const *m = &alloc.moves[i];
                        if (m->kind == LIR_MOVE_ROOT) {
                                roots   += 1;
                                spilled += (m->from_slot != LIR_NONE);
                                CHECK(m->op == 0 && m->phase == LIR_MOVE_BEFORE);
                                CHECK(m->to_slot < alloc.nvslots);
                        }
                }

                CHECK(roots == 48 && spilled >= 40);
        }

        lir_free(L);
}

static void
check_constraints(void)
{
        Lir   *L = fn(LT_I64, LT_I64, LT_I64);
        LirReg d = lir_reg(L, LIR_I64);
        LirReg e = lir_reg(L, LIR_I64);

        put(L, LIR_ADD, d, lir_r(L->params[0]), lir_r(L->params[1]));
        put(L, LIR_ADD, e, lir_r(d), lir_r(L->params[0]));
        put(L, LIR_ADD, e, lir_r(e), lir_r(L->params[1]));
        ret(L, e);

        LirConstraint cs[] = {
                { .reg = L->params[0], .phys = 2,                 .tied = LIR_NONE },
                { .reg = d,            .phys = 2, .output = true, .tied = LIR_NONE }
        };

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &Mock, cs, countof(cs));
                CHECK(alloc.nconstraints == 2);
                CHECK(lir_physical(&alloc, L->params[0], 0, false) == 2);
                CHECK(lir_physical(&alloc, d, 0, true) == 2);
                CHECK(lir_where(&alloc, L->params[0], LIR_IN(1)).phys != 2);
        }

        lir_free(L);

        L = fn(LT_PTR, LT_PTR);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));

        LirReg pin = lir_pinned(L, LIR_PIN_0);
        LirReg p   = lir_reg(L, LIR_PTR);

        put(L, LIR_ALLOCA, p, lir_i(31), lir_i(64));
        ret(L, pin);

        WITH_SCRATCH {
                LirAlloc alloc = allocate(L, &Mock, NULL, 0);
                CHECK(alloc.frame_align == 64 && alloc.alloca_offsets[0] % 64 == 0);
        }

        lir_free(L);
}

static void
check_branches(void)
{
        LirTarget t = Mock;
        u64       seed = 0x2545f4914f6cdd1d;

        t.gpr.callee_saved = 0;

        for (u32 n = 0; n < 300; ++n) {
                Lir     *L = fn(LT_I64, LT_I64, LT_I64, LT_I64);
                LirReg   x = lir_reg(L, LIR_I64);
                LirReg   y = lir_reg(L, LIR_I64);
                LirLabel labels[6];

                for (u32 k = 0; k < countof(labels); ++k) {
                        labels[k] = lir_label(L);
                }

                put(L, LIR_LI, x, lir_i(1));
                put(L, LIR_LI, y, lir_i(2));

                for (u32 k = 0; k < countof(labels); ++k) {
                        here(L, labels[k]);
                        LirReg  v = (xorshift(&seed) & 1) ? x : y;
                        LirReg  w = L->params[xorshift(&seed) % 3];
                        LirOpnd a = lir_r(w);

                        put(L, LIR_ADD, v, lir_r(v), lir_r(w));

                        switch (xorshift(&seed) % 4) {
                        case 0:
                                push(L, call(lir_i(1), v, sig(LT_I64, T(LT_I64), 1), &a));
                                break;
                        case 1:
                                put(L, LIR_BR, LIR_NONE, lir_cc(LIR_LT), lir_r(v), lir_r(w), lir_l(labels[xorshift(&seed) % countof(labels)]));
                                break;
                        case 2:
                                put(L, LIR_BRZ, LIR_NONE, lir_r(w), lir_l(labels[xorshift(&seed) % countof(labels)]));
                                break;
                        default:
                                put(L, LIR_ADD, w, lir_r(w), lir_i(-1));
                                break;
                        }
                }

                put(L, LIR_ADD, x, lir_r(x), lir_r(y));
                ret(L, x);

                WITH_SCRATCH {
                        allocate(L, &t, NULL, 0);
                        allocate(L, &Mock, NULL, 0);
                }

                lir_free(L);
        }
}

static LirMove
move(u32 from, u32 to, LirClass cls)
{
        return (LirMove) {
                .from      = LIR_NONE,
                .to        = LIR_NONE,
                .cls       = cls,
                .from_slot = LIR_NONE,
                .to_slot   = LIR_NONE,
                .remat     = LIR_NONE,
                .edge      = LIR_NONE,
                .stub      = LIR_NONE,
                .from_phys = from,
                .to_phys   = to
        };
}

static void
replay(LirMove const *ms, u32 n, bool f, u64 *gp, u64 *fr)
{
        for (u32 i = 0; i < n; ++i) {
                LirMove m   = ms[i];
                u64    *src = (f && !m.from_gpr) ? fr : gp;
                u64    *dst = (f && !m.to_gpr) ? fr : gp;
                dst[m.to_phys] = src[m.from_phys];
        }
}

static LirMove *
parallel(LirMove const *moves, u32 n, u32 *count)
{
        LirMove *out;
        LirError err;

        CHECK(lir_parallel_moves(ty, moves, n, &Mock.gpr, &out, count, &err));

        return out;
}

static u64 *
cell(u64 *regs, u64 *slots, u32 slot, u8 phys)
{
        return (slot == LIR_NONE) ? &regs[phys] : &slots[slot / 8];
}

static void
check_parallel(void)
{
        for (u32 f = 0; f < 2; ++f) {
                LirClass cls     = f ? LIR_F64 : LIR_I64;
                LirMove  moves[] = { move(1, 2, cls), move(2, 3, cls), move(3, 1, cls) };
                u64      gp[32]  = {0};
                u64      fr[32]  = {0};
                u64     *regs    = f ? fr : gp;
                u32      n;
                LirMove *out     = parallel(moves, countof(moves), &n);

                regs[1] = 11;
                regs[2] = 22;
                regs[3] = 33;

                CHECK(n == 4);
                replay(out, n, f, gp, fr);
                CHECK(regs[1] == 33 && regs[2] == 11 && regs[3] == 22);
        }

        LirMove  moves[] = { move(1, 2, LIR_I64), move(3, 2, LIR_I64) };
        LirMove *out;
        u32      n;
        LirError err;

        CHECK(!lir_parallel_moves(ty, moves, 2, &Mock.gpr, &out, &n, &err));
        CHECK(err.kind == LE_TARGET);

        moves[0] = move(0, 0, LIR_I64);
        out = parallel(moves, 1, &n);
        CHECK(n == 0);

        moves[0]           = move(0, 1, LIR_I64);
        moves[0].from_slot = 0;
        moves[0].from_phys = LIR_PHYS_NONE;
        moves[1]           = move(1, 0, LIR_I64);
        moves[1].to_slot   = 0;
        moves[1].to_phys   = LIR_PHYS_NONE;

        out = parallel(moves, 2, &n);

        u64 regs[32] = { [1] = 11 };
        u64 slots[1] = { 99 };

        for (u32 i = 0; i < n; ++i) {
                LirMove m   = out[i];
                u64    *src = cell(regs, slots, m.from_slot, m.from_phys);
                u64    *dst = cell(regs, slots, m.to_slot, m.to_phys);
                *dst = *src;
        }

        CHECK(regs[1] == 99 && slots[0] == 11);
}

static void
check_random(void)
{
        u64 seed = 0x964e275be31da5c7;

        for (u32 n = 0; n < 500; ++n) {
                bool     f   = n % 2;
                LirClass cls = f ? LIR_F64 : LIR_I64;
                LirType  types[10];

                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LT_F64 : LT_I64;
                }

                Lir *L = fna(types[0], types);

                for (u32 i = 0; i < 30; ++i) {
                        LirOpnd a = lir_r(L->params[xorshift(&seed) % 10]);
                        LirOpnd b = lir_r(L->params[xorshift(&seed) % 10]);
                        LirReg  d = L->params[xorshift(&seed) % 10];

                        put(L, f ? LIR_FADD : LIR_ADD, d, a, b);

                        if (i % 7 == 0) {
                                push(L, vcall(lir_i(1)));
                        }
                }

                ret(L, L->params[0]);

                WITH_SCRATCH {
                        allocate(L, &Mock, NULL, 0);
                }

                lir_free(L);

                u32 perm[10];

                for (u32 i = 0; i < countof(perm); ++i) {
                        perm[i] = i;
                }

                for (u32 i = countof(perm); i > 1; --i) {
                        u32 j = xorshift(&seed) % i;
                        SWAP(u32, perm[i - 1], perm[j]);
                }

                LirMove moves[10];
                u64     gp[32] = {0};
                u64     fr[32] = {0};
                u64    *regs   = f ? fr : gp;
                u32     count;

                for (u32 i = 0; i < countof(moves); ++i) {
                        moves[i] = move(i, perm[i], cls);
                        regs[i]  = 100 + i;
                }

                LirMove *out = parallel(moves, countof(moves), &count);

                replay(out, count, f, gp, fr);

                for (u32 i = 0; i < countof(moves); ++i) {
                        CHECK(regs[perm[i]] == 100 + i);
                }
        }
}

int
main(void)
{
        check_pressure();
        check_loops();
        check_calls();
        check_loop_calls();
        check_remat();
        check_coalesce();
        check_roots();
        check_constraints();
        check_branches();
        check_parallel();
        check_random();

        return report("LIR allocation");
}
