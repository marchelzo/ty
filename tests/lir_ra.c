#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "lir.h"

static u32 checks;
static u32 failures;

#define CHECK(expr) do { \
        ++checks; \
        if (!(expr)) { \
                fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #expr); \
                ++failures; \
        } \
} while (0)

static LirTarget
mock_target(void)
{
        return (LirTarget) {
                .arch = LIR_ARCH_X64, .abi = LIR_ABI_SYSV, .name = "test",
                .gpr = { .available = 15, .callee_saved = 12, .args = {0, 1, 2, 3},
                         .nargs = 4, .ret = 0, .scratch = {11}, .nscratch = 1 },
                .fpr = { .available = 15, .args = {0, 1, 2, 3}, .nargs = 4, .ret = 0 },
                .pins = {3}, .npins = 1, .stack_align = 16
        };
}

static Lir *
function(LirType ret, LirType const *types, u32 n)
{
        LirSig sig = { .ret = ret, .params = types, .nparams = n, .nfixed = n };
        LirError err;
        Lir *L = lir_new("alloc-test", &sig, LIR_MODE_AUTO, &err);
        CHECK(L != NULL);
        if (L == NULL) {
                exit(1);
        }
        return L;
}

static void
emit(Lir *L, LirOp op, LirReg dst, LirOpnd const *args, u32 n)
{
        CHECK(lir_emit_to(L, op, dst, args, n));
}

static void
ret(Lir *L, LirReg r)
{
        if (r == LIR_NONE) {
                emit(L, LIR_RET, LIR_NONE, NULL, 0);
        } else {
                emit(L, LIR_RET, LIR_NONE, (LirOpnd[]) { lir_r(r) }, 1);
        }
}

static bool
overlap(LirInterval const *a, LirInterval const *b)
{
        for (u32 i = 0; i < a->nranges; ++i) {
                for (u32 j = 0; j < b->nranges; ++j) {
                        if (a->ranges[i].start < b->ranges[j].end
                            && b->ranges[j].start < a->ranges[i].end) {
                                return true;
                        }
                }
        }
        return false;
}

static bool
float_reg(LirClass cls)
{
        return cls == LIR_F32 || cls == LIR_F64;
}

static LirAlloc
allocate(Lir *L, LirTarget const *target, LirConstraint const *constraints, u32 n)
{
        LirCFG cfg;
        LirError err;
        LirAlloc alloc = {0};
        CHECK(lir_validate(L, &err));
        bool ok = lir_cfg(L, &cfg, &err);
        CHECK(ok);
        if (!ok) {
                exit(1);
        }
        ok = lir_allocate(L, &cfg, target, constraints, n, &alloc, &err);
        CHECK(ok);
        if (!ok) {
                fprintf(stderr, "%s\n", err.message);
                exit(1);
        }
        lir_cfg_free(&cfg);
        CHECK(alloc.nintervals == L->nregs);
        CHECK(alloc.frame_size % target->stack_align == 0);
        for (u32 i = 0; i < alloc.nintervals; ++i) {
                LirInterval const *a = &alloc.intervals[i];
                if (a->spilled) {
                        CHECK(a->phys == LIR_PHYS_NONE && a->spill < alloc.spill_size);
                }
                for (u32 j = 0; j < i; ++j) {
                        LirInterval const *b = &alloc.intervals[j];
                        if (a->phys == LIR_PHYS_NONE || b->phys == LIR_PHYS_NONE
                            || a->phys != b->phys
                            || float_reg(L->regs[i].cls) != float_reg(L->regs[j].cls)) {
                                continue;
                        }
                        CHECK(!overlap(a, b));
                }
        }
        return alloc;
}

static void
check_pressure(void)
{
        LirType types[48];
        LirTarget target = mock_target();
        for (u32 f = 0; f < 2; ++f) {
                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LIR_TYPE_F64 : LIR_TYPE_I64;
                }
                Lir *L = function(types[0], types, countof(types));
                LirReg acc = lir_reg(L, f ? LIR_F64 : LIR_I64);
                LirOpnd init = f ? lir_f(0.0) : lir_i(0);
                emit(L, f ? LIR_FLI : LIR_LI, acc, &init, 1);
                for (u32 i = 0; i < countof(types); ++i) {
                        emit(L, f ? LIR_FADD : LIR_ADD, acc,
                             (LirOpnd[]) { lir_r(acc), lir_r(L->params[i]) }, 2);
                }
                ret(L, acc);
                LirAlloc alloc = allocate(L, &target, NULL, 0);
                u32 spilled = 0;
                for (u32 i = 0; i < alloc.nintervals; ++i) {
                        spilled += alloc.intervals[i].spilled;
                }
                CHECK(spilled >= 44);
                CHECK(alloc.spill_size >= 44 * 8);
                lir_alloc_free(&alloc);
                lir_free(L);
        }
}

static void
check_next_use(void)
{
        LirType types[] = { LIR_TYPE_I64, LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, 2);
        LirReg d = lir_reg(L, LIR_I64);
        emit(L, LIR_LI, d, (LirOpnd[]) { lir_i(1) }, 1);
        emit(L, LIR_ADD, d, (LirOpnd[]) { lir_r(d), lir_r(L->params[0]) }, 2);
        emit(L, LIR_ADD, d, (LirOpnd[]) { lir_r(d), lir_r(L->params[1]) }, 2);
        ret(L, d);
        LirTarget target = mock_target();
        target.gpr.available = 3;
        target.gpr.callee_saved = 0;
        LirAlloc alloc = allocate(L, &target, NULL, 0);
        CHECK(alloc.intervals[L->params[1]].spilled);
        CHECK(!alloc.intervals[L->params[0]].spilled);
        CHECK(!alloc.intervals[d].spilled);
        lir_alloc_free(&alloc);
        lir_free(L);
}

static void
check_loops(void)
{
        LirType type = LIR_TYPE_I64;
        Lir *L = function(type, &type, 1);
        LirReg i = lir_reg(L, LIR_I64);
        LirReg sum = lir_reg(L, LIR_I64);
        lir_reg(L, LIR_I64);
        LirLabel loop = lir_label(L);
        emit(L, LIR_LI, i, (LirOpnd[]) { lir_i(0) }, 1);
        emit(L, LIR_LI, sum, (LirOpnd[]) { lir_i(0) }, 1);
        CHECK(lir_bind(L, loop));
        emit(L, LIR_ADD, sum, (LirOpnd[]) { lir_r(sum), lir_r(i) }, 2);
        emit(L, LIR_ADD, i, (LirOpnd[]) { lir_r(i), lir_i(1) }, 2);
        emit(L, LIR_BR, LIR_NONE,
             (LirOpnd[]) { lir_cc(LIR_LT), lir_r(i), lir_r(L->params[0]), lir_l(loop) }, 4);
        ret(L, sum);
        LirTarget target = mock_target();
        LirAlloc alloc = allocate(L, &target, NULL, 0);
        CHECK(alloc.intervals[i].nranges == 1);
        CHECK(alloc.intervals[i].ranges[0].end >= 10);
        CHECK(alloc.intervals[sum].ranges[0].end >= 11);
        CHECK(alloc.intervals[L->nregs - 1].nranges == 0);
        lir_alloc_free(&alloc);
        lir_free(L);
}

static void
check_calls(void)
{
        LirType types[] = { LIR_TYPE_I64, LIR_TYPE_I64 };
        LirTarget target = mock_target();
        for (u32 saved = 0; saved < 2; ++saved) {
                Lir *L = function(LIR_TYPE_I64, types, 2);
                LirInst in = {
                        .op = LIR_CALL, .dst = LIR_NONE,
                        .args = { lir_i(1) }, .nargs = 1, .sig = { .ret = LIR_VOID }
                };
                CHECK(lir_emit(L, &in));
                LirReg d = lir_reg(L, LIR_I64);
                emit(L, LIR_ADD, d, (LirOpnd[]) { lir_r(L->params[0]), lir_r(L->params[1]) }, 2);
                ret(L, d);
                target.gpr.callee_saved = saved ? 12 : 0;
                LirAlloc alloc = allocate(L, &target, NULL, 0);
                if (saved) {
                        CHECK(alloc.saved_gpr == 12);
                        CHECK(alloc.nmoves == 0);
                } else {
                        CHECK(alloc.nmoves == 4);
                        CHECK(alloc.intervals[0].call_save != LIR_NONE);
                        CHECK(alloc.intervals[1].call_save != LIR_NONE);
                }
                lir_alloc_free(&alloc);
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_I64, types, 1);
        LirOpnd arg = lir_r(L->params[0]);
        LirInst in = {
                .op = LIR_CALL, .dst = L->params[0],
                .args = { lir_i(1) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_I64, .params = types, .nparams = 1, .nfixed = 1 },
                .call_args = &arg, .ncall_args = 1
        };
        CHECK(lir_emit(L, &in));
        ret(L, L->params[0]);
        target.gpr.callee_saved = 0;
        LirAlloc alloc = allocate(L, &target, NULL, 0);
        CHECK(alloc.nmoves == 0);
        CHECK(alloc.intervals[0].call_save == LIR_NONE);
        lir_alloc_free(&alloc);
        lir_free(L);
}

static void
check_roots(void)
{
        LirType types[48];
        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = LIR_TYPE_REF;
        }
        Lir *L = function(LIR_VOID, types, countof(types));
        LirInst in = {
                .op = LIR_CALL, .dst = LIR_NONE,
                .args = { lir_i(1) }, .nargs = 1,
                .sig = { .ret = LIR_VOID }, .flags = LIR_MAY_GC
        };
        CHECK(lir_emit(L, &in));
        for (u32 i = 0; i < countof(types); ++i) {
                LirReg d = lir_reg(L, LIR_REF);
                emit(L, LIR_MOV, d, (LirOpnd[]) { lir_r(L->params[i]) }, 1);
        }
        ret(L, LIR_NONE);
        LirTarget target = mock_target();
        LirAlloc alloc = allocate(L, &target, NULL, 0);
        CHECK(alloc.nvslots == 48);
        u32 roots = 0;
        u32 spilled_roots = 0;
        for (u32 i = 0; i < alloc.nmoves; ++i) {
                LirMove const *m = &alloc.moves[i];
                if (m->kind == LIR_MOVE_ROOT) {
                        ++roots;
                        spilled_roots += m->from_slot != LIR_NONE;
                        CHECK(m->op == 0 && m->phase == LIR_MOVE_BEFORE);
                        CHECK(m->to_slot < alloc.nvslots);
                }
        }
        CHECK(roots == 48 && spilled_roots >= 44);
        lir_alloc_free(&alloc);
        lir_free(L);
}

static void
check_constraints(void)
{
        LirType types[] = { LIR_TYPE_I64, LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, 2);
        LirReg d = lir_reg(L, LIR_I64);
        LirReg e = lir_reg(L, LIR_I64);
        emit(L, LIR_ADD, d, (LirOpnd[]) { lir_r(L->params[0]), lir_r(L->params[1]) }, 2);
        emit(L, LIR_ADD, e, (LirOpnd[]) { lir_r(d), lir_r(L->params[0]) }, 2);
        emit(L, LIR_ADD, e, (LirOpnd[]) { lir_r(e), lir_r(L->params[1]) }, 2);
        ret(L, e);
        LirConstraint constraints[] = {
                { .op = 0, .reg = L->params[0], .phys = 0, .tied = LIR_NONE },
                { .op = 0, .reg = d, .phys = 0, .output = true, .tied = LIR_NONE }
        };
        LirTarget target = mock_target();
        LirAlloc alloc = allocate(L, &target, constraints, countof(constraints));
        CHECK(alloc.intervals[L->params[0]].call_save != LIR_NONE);
        CHECK(alloc.nconstraints == 2);
        u32 after = 0;
        for (u32 i = 0; i < alloc.nmoves; ++i) {
                after += alloc.moves[i].phase == LIR_MOVE_AFTER;
        }
        CHECK(after >= 2);
        lir_alloc_free(&alloc);
        lir_free(L);
        LirType type = LIR_TYPE_PTR;
        L = function(type, &type, 1);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
        LirReg pin = lir_pinned(L, LIR_PIN_0);
        LirReg p = lir_reg(L, LIR_PTR);
        emit(L, LIR_ALLOCA, p, (LirOpnd[]) { lir_i(31), lir_i(64) }, 2);
        ret(L, pin);
        alloc = allocate(L, &target, NULL, 0);
        CHECK(alloc.intervals[pin].phys == 3);
        CHECK((alloc.saved_gpr & 8) != 0);
        CHECK(alloc.frame_align == 64 && alloc.alloca_offsets[0] % 64 == 0);
        lir_alloc_free(&alloc);
        lir_free(L);
}

static LirMove
move(u32 from, u32 to, LirClass cls)
{
        return (LirMove) {
                .from = LIR_NONE, .to = LIR_NONE, .cls = cls,
                .from_slot = LIR_NONE, .to_slot = LIR_NONE,
                .from_phys = from, .to_phys = to
        };
}

static void
check_parallel(void)
{
        LirTarget target = mock_target();
        for (u32 f = 0; f < 2; ++f) {
                LirClass cls = f ? LIR_F64 : LIR_I64;
                LirMove moves[] = { move(1, 2, cls), move(2, 3, cls), move(3, 1, cls) };
                LirMove *out;
                u32 n;
                LirError err;
                CHECK(lir_parallel_moves(moves, countof(moves), &target.gpr, &out, &n, &err));
                u64 gp[32] = {0};
                u64 fr[32] = {0};
                u64 *regs = f ? fr : gp;
                regs[1] = 11;
                regs[2] = 22;
                regs[3] = 33;
                CHECK(n == 4);
                for (u32 i = 0; i < n; ++i) {
                        LirMove m = out[i];
                        u64 *src = f && !m.from_gpr ? fr : gp;
                        u64 *dst = f && !m.to_gpr ? fr : gp;
                        dst[m.to_phys] = src[m.from_phys];
                }
                CHECK(regs[1] == 33 && regs[2] == 11 && regs[3] == 22);
                free(out);
        }
        LirMove moves[] = { move(1, 2, LIR_I64), move(3, 2, LIR_I64) };
        LirMove *out;
        u32 n;
        LirError err;
        CHECK(!lir_parallel_moves(moves, 2, &target.gpr, &out, &n, &err));
        CHECK(err.kind == LIR_ERROR_TARGET);
        moves[0] = move(0, 0, LIR_I64);
        CHECK(lir_parallel_moves(moves, 1, &target.gpr, &out, &n, &err));
        CHECK(n == 0);
        free(out);
        moves[0] = move(0, 1, LIR_I64);
        moves[0].from_slot = 0;
        moves[0].from_phys = LIR_PHYS_NONE;
        moves[1] = move(1, 0, LIR_I64);
        moves[1].to_slot = 0;
        moves[1].to_phys = LIR_PHYS_NONE;
        CHECK(lir_parallel_moves(moves, 2, &target.gpr, &out, &n, &err));
        u64 regs[32] = { [1] = 11 };
        u64 slots[1] = { 99 };
        for (u32 i = 0; i < n; ++i) {
                LirMove m = out[i];
                u64 value = m.from_slot == LIR_NONE ? regs[m.from_phys] : slots[m.from_slot / 8];
                if (m.to_slot == LIR_NONE) {
                        regs[m.to_phys] = value;
                } else {
                        slots[m.to_slot / 8] = value;
                }
        }
        CHECK(regs[1] == 99 && slots[0] == 11);
        free(out);
}

static u64
random_bits(u64 *seed)
{
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        return *seed;
}

static void
check_random(void)
{
        u64 seed = 0x964e275be31da5c7;
        LirTarget target = mock_target();
        for (u32 n = 0; n < 500; ++n) {
                bool f = n % 2;
                LirType types[10];
                for (u32 i = 0; i < countof(types); ++i) {
                        types[i] = f ? LIR_TYPE_F64 : LIR_TYPE_I64;
                }
                Lir *L = function(types[0], types, countof(types));
                for (u32 i = 0; i < 30; ++i) {
                        u32 a = random_bits(&seed) % 10;
                        u32 b = random_bits(&seed) % 10;
                        u32 d = random_bits(&seed) % 10;
                        emit(L, f ? LIR_FADD : LIR_ADD, L->params[d],
                             (LirOpnd[]) { lir_r(L->params[a]), lir_r(L->params[b]) }, 2);
                        if (i % 7 == 0) {
                                LirInst in = {
                                        .op = LIR_CALL, .dst = LIR_NONE,
                                        .args = { lir_i(1) }, .nargs = 1,
                                        .sig = { .ret = LIR_VOID }
                                };
                                CHECK(lir_emit(L, &in));
                        }
                }
                ret(L, L->params[0]);
                LirAlloc alloc = allocate(L, &target, NULL, 0);
                lir_alloc_free(&alloc);
                lir_free(L);
                u32 perm[10];
                for (u32 i = 0; i < countof(perm); ++i) {
                        perm[i] = i;
                }
                for (u32 i = countof(perm); i > 1; --i) {
                        u32 j = random_bits(&seed) % i;
                        u32 temp = perm[i - 1];
                        perm[i - 1] = perm[j];
                        perm[j] = temp;
                }
                LirMove moves[10];
                for (u32 i = 0; i < countof(moves); ++i) {
                        moves[i] = move(i, perm[i], f ? LIR_F64 : LIR_I64);
                }
                LirMove *out;
                u32 count;
                LirError err;
                CHECK(lir_parallel_moves(moves, countof(moves), &target.gpr, &out, &count, &err));
                u64 gp[32] = {0};
                u64 fr[32] = {0};
                u64 *regs = f ? fr : gp;
                for (u32 i = 0; i < countof(moves); ++i) {
                        regs[i] = 100 + i;
                }
                for (u32 i = 0; i < count; ++i) {
                        LirMove m = out[i];
                        u64 *src = f && !m.from_gpr ? fr : gp;
                        u64 *dst = f && !m.to_gpr ? fr : gp;
                        dst[m.to_phys] = src[m.from_phys];
                }
                for (u32 i = 0; i < countof(moves); ++i) {
                        CHECK(regs[perm[i]] == 100 + i);
                }
                free(out);
        }
}

int
main(void)
{
        check_pressure();
        check_next_use();
        check_loops();
        check_calls();
        check_roots();
        check_constraints();
        check_parallel();
        check_random();
        printf("LIR allocation: %u checks, %u failures\n", checks, failures);
        return failures != 0;
}
