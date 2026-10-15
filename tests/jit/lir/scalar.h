#ifndef LIR_SCALAR_H_INCLUDED
#define LIR_SCALAR_H_INCLUDED

#include <math.h>
#include <stdarg.h>
#include <setjmp.h>

#include "test.h"

typedef bool Backend(Ty *, Lir *, LirScalar const *, u32, LirScalar *, LirError *);

static Backend *Exec;
static bool     Native;

#define run(L, ...) invoke(                                     \
        NULL,                                                   \
        (L),                                                    \
        (LirScalar[]) { __VA_ARGS__ },                          \
        countof(((LirScalar[]) { __VA_ARGS__ }))                \
)

static LirType const ClassType[] = {
        [LIR_I32] = LT_I32,
        [LIR_I64] = LT_I64,
        [LIR_F32] = LT_F32,
        [LIR_F64] = LT_F64
};

inline static bool
equal(LirClass cls, LirScalar a, LirScalar b)
{
        return (cls == LIR_F32) ? (a.f32 == b.f32) : (a.u == b.u);
}

static LirScalar
invoke(Ty *ty, Lir *L, LirScalar const *args, u32 n)
{
        LirError  err;
        LirScalar out = {0};
        bool      ok  = Exec(ty, L, args, n, &out, &err);

        CHECK(ok);

        if (!ok) {
                fprintf(stderr, "op %u: %s\n", err.op, err.message);
                lir_dump(L, stderr);
        }

        return out;
}

static LirScalar
numeric(LirOp op, LirClass cls, LirScalar a, LirScalar b, LirScalar c)
{
        LirType t = ClassType[cls];
        Lir    *L = fn(t, t, t, t);
        LirOpnd args[3];

        for (u32 i = 0; i < 3; ++i) {
                LirReg r = L->params[i];
                if (cls == LIR_I32) {
                        r = lir_reg(L, LIR_I32);
                        put(L, LIR_ZEXT32, r, lir_r(L->params[i]));
                }
                args[i] = lir_r(r);
        }

        LirReg d = lir_reg(L, cls);

        emit(L, op, d, args, LirOps[op].argc);
        ret(L, d);

        LirScalar out = run(L, a, b, c);
        lir_free(L);

        return out;
}

static void
check_integer(void)
{
        static struct {
                LirOp    op;
                LirClass cls;
                u64      a;
                u64      b;
                u64      want;
        } const cases[] = {
                { LIR_ADD,    LIR_I64, UINT64_MAX,         3,     2                  },
                { LIR_SUB,    LIR_I64, 1,                  3,     UINT64_MAX - 1     },
                { LIR_MUL,    LIR_I64, 0x12345678,         17,    0x13579bdf8        },
                { LIR_MULHS,  LIR_I64, -7,                 3,     UINT64_MAX         },
                { LIR_MULHU,  LIR_I64, UINT64_MAX,         2,     1                  },
                { LIR_SDIV,   LIR_I64, -101,               7,     -14                },
                { LIR_SREM,   LIR_I64, -101,               7,     -3                 },
                { LIR_UDIV,   LIR_I64, UINT64_MAX,         2,     INT64_MAX          },
                { LIR_UREM,   LIR_I64, UINT64_MAX,         2,     1                  },
                { LIR_AND,    LIR_I64, 0xcafe,             0xf0f, 0xa0e              },
                { LIR_OR,     LIR_I64, 0xcafe,             0xf0f, 0xcfff             },
                { LIR_XOR,    LIR_I64, 0xcafe,             0xf0f, 0xc5f1             },
                { LIR_SHL,    LIR_I64, 17,                 65,    34                 },
                { LIR_SHR,    LIR_I64, UINT64_MAX,         65,    INT64_MAX          },
                { LIR_SAR,    LIR_I64, -8,                 2,     -2                 },
                { LIR_ROTR,   LIR_I64, 1,                  1,     1ULL << 63         },
                { LIR_NEG,    LIR_I64, 7,                  0,     -7                 },
                { LIR_NOT,    LIR_I64, 0xcafe,             0,     ~0xcafeULL         },
                { LIR_CLZ,    LIR_I64, 1,                  0,     63                 },
                { LIR_CTZ,    LIR_I64, 0x800,              0,     11                 },
                { LIR_POPCNT, LIR_I64, 0xa55a,             0,     8                  },
                { LIR_BSWAP,  LIR_I64, 0x0123456789abcdef, 0,     0xefcdab8967452301 },
                { LIR_SEXT8,  LIR_I64, 0xfedcba9876543280, 0,     -128               },
                { LIR_SEXT16, LIR_I64, 0xdead8000,         0,     -32768             },
                { LIR_SEXT32, LIR_I64, 0xdeadbeef80000000, 0,     (i64)INT32_MIN     },
                { LIR_ZEXT8,  LIR_I64, UINT64_MAX,         0,     255                },
                { LIR_ZEXT16, LIR_I64, UINT64_MAX,         0,     65535              },
                { LIR_ZEXT32, LIR_I64, UINT64_MAX,         0,     UINT32_MAX         },
                { LIR_ADD,    LIR_I32, UINT32_MAX,         2,     1                  },
                { LIR_SDIV,   LIR_I32, (u32)-101,          7,     -14                },
                { LIR_ROTR,   LIR_I32, 1,                  1,     (i64)INT32_MIN     },
                { LIR_MULHU,  LIR_I32, UINT32_MAX,         2,     1                  },
                { LIR_CLZ,    LIR_I32, 0,                  0,     32                 },
                { LIR_CTZ,    LIR_I64, 0,                  0,     64                 },
                { LIR_SDIV,   LIR_I64, INT64_MIN,          -1,    INT64_MIN          },
                { LIR_SREM,   LIR_I64, INT64_MIN,          -1,    0                  }
        };

        for (u32 i = 0; i < countof(cases); ++i) {
                LirScalar a = S(u, cases[i].a);
                LirScalar b = S(u, cases[i].b);
                CHECK(numeric(cases[i].op, cases[i].cls, a, b, S0).u == cases[i].want);
        }
}

static void
check_float(void)
{
        static struct {
                LirOp  op;
                double a;
                double b;
                double c;
                double want;
        } const cases[] = {
                { LIR_FADD,  3.5,  2.0, 0.0, 5.5  },
                { LIR_FSUB,  3.5,  2.0, 0.0, 1.5  },
                { LIR_FMUL,  3.5,  2.0, 0.0, 7.0  },
                { LIR_FDIV,  3.5,  2.0, 0.0, 1.75 },
                { LIR_FMIN,  3.5,  2.0, 0.0, 2.0  },
                { LIR_FMAX,  3.5,  2.0, 0.0, 3.5  },
                { LIR_FSQRT, 25.0, 0.0, 0.0, 5.0  },
                { LIR_FABS,  -3.5, 0.0, 0.0, 3.5  },
                { LIR_FNEG,  3.5,  0.0, 0.0, -3.5 },
                { LIR_FMA,   3.5,  2.0, 1.0, 8.0  }
        };

        for (u32 i = 0; i < countof(cases); ++i) {
                LirOp  op = cases[i].op;
                double a  = cases[i].a;
                double b  = cases[i].b;
                double c  = cases[i].c;
                double    want = cases[i].want;
                LirScalar x64  = numeric(op, LIR_F64, S(f64, a), S(f64, b), S(f64, c));
                LirScalar x32  = numeric(op, LIR_F32, S(f32, a), S(f32, b), S(f32, c));
                CHECK(x64.f64 == want);
                CHECK(x32.f32 == want);
        }

        LirScalar fused = numeric(
                LIR_FMA,
                LIR_F64,
                S(f64, 0x1.0000000000001p0),
                S(f64, 0x1.fffffffffffffp-1),
                S(f64, -1.0)
        );
        CHECK(fused.f64 == 0x1.ffffffffffffep-54);

        fused = numeric(
                LIR_FMA,
                LIR_F32,
                S(f32, 0x1.000002p0f),
                S(f32, 0x1.fffffep-1f),
                S(f32, -1.0f)
        );
        CHECK(fused.f32 == 0x1.fffffcp-25f);

        CHECK(signbit(numeric(LIR_FNEG, LIR_F64, S(f64, 0.0), S0, S0).f64));
        CHECK(numeric(LIR_FMIN, LIR_F64, S(f64, NAN), S(f64, 3.0), S0).f64 == 3.0);
}

static void
check_conversions(void)
{
        static struct {
                LirOp     op;
                LirType   src;
                LirType   dst;
                LirScalar in;
                LirScalar want;
        } const cases[] = {
                { LIR_I2F,     LT_I64, LT_F64, { .i = -17 },            { .f64 = -17.0 }    },
                { LIR_U2F,     LT_U64, LT_F64, { .u = -1ULL },          { .f64 = 0x1p64 }   },
                { LIR_U2F,     LT_U64, LT_F32, { .u = -1ULL },          { .f32 = 0x1p64f }  },
                { LIR_F2I,     LT_F64, LT_I64, { .f64 = -17.9 },        { .i = -17 }        },
                { LIR_F2I,     LT_F64, LT_I64, { .f64 = NAN },          { .i = INT64_MIN }  },
                { LIR_FEXT,    LT_F32, LT_F64, { .f32 = 1.5f },         { .f64 = 1.5 }      },
                { LIR_FTRUNC,  LT_F64, LT_F32, { .f64 = 1.5 },          { .f32 = 1.5f }     },
                { LIR_BITCAST, LT_F64, LT_I64, { .f64 = -0.0 },         { .u = 1ULL << 63 } },
                { LIR_BITCAST, LT_I64, LT_F64, { .u = 0x3ffULL << 52 }, { .f64 = 1.0 }      }
        };

        for (u32 i = 0; i < countof(cases); ++i) {
                LirClass cls = lir_type_class(cases[i].dst);
                Lir     *L   = fn(cases[i].dst, cases[i].src);
                LirReg   r   = lir_reg(L, cls);

                put(L, cases[i].op, r, lir_r(L->params[0]));
                ret(L, r);

                LirScalar out = run(L, cases[i].in);
                bool      nan = (cases[i].op == LIR_F2I) && isnan(cases[i].in.f64);

                if (!(Native && nan)) {
                        CHECK(equal(cls, out, cases[i].want));
                }

                lir_free(L);
        }
}

static void
check_checked(void)
{
        static LirOp const ops[] = { LIR_ADDO, LIR_SUBO, LIR_MULO };

        for (u32 i = 0; i < countof(ops); ++i) {
                Lir     *L    = fn(LT_I64, LT_I64, LT_I64);
                LirReg   d    = lir_reg(L, LIR_I64);
                LirLabel over = lir_label(L);

                put(L, ops[i], d, lir_r(L->params[0]), lir_r(L->params[1]), lir_l(over));
                ret(L, lir_i(0));
                here(L, over);
                ret(L, lir_i(1));

                CHECK(run(L, S(i, 2), S(i, 3)).i == 0);

                LirScalar x = S(i, (i == 1) ? INT64_MIN : INT64_MAX);
                LirScalar y = S(i, (i == 2) ? 2 : 1);
                CHECK(run(L, x, y).i == 1);

                lir_free(L);
        }
}

static void
check_conditions(void)
{
        static bool const want[] = {
                [LIR_EQ]  = false,
                [LIR_NE]  = true,
                [LIR_LT]  = true,
                [LIR_LE]  = true,
                [LIR_GT]  = false,
                [LIR_GE]  = false,
                [LIR_ULT] = false,
                [LIR_ULE] = false,
                [LIR_UGT] = true,
                [LIR_UGE] = true
        };

        for (LirCC cc = LIR_EQ; cc < LIR_CC_COUNT; ++cc) {
                bool    fp = (cc >= LIR_FEQ);
                LirType t  = fp ? LT_F64 : LT_I64;
                Lir    *L  = fn(LT_I64, t, t);
                LirReg  d  = lir_reg(L, LIR_I64);

                put(
                        L,
                        fp ? LIR_FSETCC : LIR_SETCC,
                        d,
                        lir_cc(cc),
                        lir_r(L->params[0]),
                        lir_r(L->params[1])
                );
                ret(L, d);

                if (fp) {
                        bool unordered = (cc == LIR_FNE) || (cc == LIR_FUN);
                        CHECK(run(L, S(f64, NAN), S(f64, 1.0)).i == unordered);
                } else {
                        CHECK(run(L, S(i, -1), S(i, 1)).i == want[cc]);
                }

                lir_free(L);
        }

        Lir    *L = fn(LT_I64, LT_I64);
        LirReg  d = lir_reg(L, LIR_I64);
        LirOpnd x = lir_r(L->params[0]);

        put(L, LIR_SELECT, d, lir_cc(LIR_GT), x, lir_i(0), lir_i(7), lir_i(9));
        ret(L, d);

        CHECK(run(L, S(i, 1)).i == 7);
        CHECK(run(L, S(i, -1)).i == 9);

        lir_free(L);
}

static double
mix12(
        i64 a, double b, i64 c, double d, i64 e, double f,
        i64 g, double h, i64 i, double j, i64 k, double l
)
{
        return a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h + 9*i + 10*j + 11*k + 12*l;
}

static double
sum_varargs(i32 n, ...)
{
        va_list ap;
        double  sum = 0.0;

        va_start(ap, n);

        for (i32 i = 0; i < n; ++i) {
                sum += (i % 2) ? va_arg(ap, double) : (double)va_arg(ap, i64);
        }

        va_end(ap);

        return sum;
}

static i8
signed_byte(i8 x)
{
        return x;
}

static double
promoted_sum(i32 unused, ...)
{
        va_list ap;

        va_start(ap, unused);

        i32    a = va_arg(ap, i32);
        i32    b = va_arg(ap, i32);
        i32    c = va_arg(ap, i32);
        double d = va_arg(ap, double);

        va_end(ap);

        return a + b + c + d;
}

static i64
bool_last(i64 a, i64 b, i64 c, i64 d, i64 e, i64 f, i64 g, i64 h, bool last)
{
        return last;
}

static void
check_stack_bool(void)
{
        LirType types[9];
        LirOpnd args[9];

        for (u32 i = 0; i < countof(types); ++i) {
                types[i] = (i == 8) ? LT_BOOL : LT_I64;
                args[i]  = lir_i((i == 8) ? 2 : 0);
        }

        Lir   *L = fn(LT_I64);
        LirReg d = lir_reg(L, LIR_I64);

        push(L, call(callee(bool_last), d, sig(LT_I64, types, countof(types)), args));
        ret(L, d);

        CHECK(run(L).i == 1);

        lir_free(L);
}

static void
check_promotions(void)
{
        LirType types[] = { LT_I32, LT_I8, LT_U16, LT_BOOL, LT_F32 };
        LirOpnd args[]  = { lir_i(0), lir_i(249), lir_i(65535), lir_i(2), lir_f(1.25) };
        LirSig  s       = vsig(LT_F64, types, countof(types), 1);
        Lir    *L       = fn(LT_F64);
        LirReg  d       = lir_reg(L, LIR_F64);

        push(L, call(callee(promoted_sum), d, s, args));
        ret(L, d);

        CHECK(run(L).f64 == 65530.25);

        lir_free(L);
}

static void
check_calls(void)
{
        LirType types[13];
        LirOpnd args[13];

        for (u32 n = 0; n <= 12; ++n) {
                Lir   *L    = fn(LT_F64);
                double want = 0.0;

                types[0] = LT_I32;
                args[0]  = lir_i(n);

                for (u32 i = 0; i < n; ++i) {
                        bool odd = i % 2;
                        types[i + 1] = odd ? LT_F64 : LT_I64;
                        args[i + 1]  = odd ? lir_f(i + 0.25) : lir_i(-(i64)i);
                        want        += odd ? i + 0.25 : -(double)i;
                }

                LirReg d = lir_reg(L, LIR_F64);

                push(L, call(callee(sum_varargs), d, vsig(LT_F64, types, n + 1, 1), args));
                ret(L, d);

                CHECK(run(L).f64 == want);

                lir_free(L);
        }

        for (u32 i = 0; i < 12; ++i) {
                types[i] = (i % 2) ? LT_F64 : LT_I64;
                args[i]  = (i % 2) ? lir_f(i + 0.25) : lir_i(i);
        }

        Lir   *L = fn(LT_F64);
        LirReg d = lir_reg(L, LIR_F64);

        push(L, call(callee(mix12), d, sig(LT_F64, types, 12), args));
        ret(L, d);

        double mixed = mix12(0, 1.25, 2, 3.25, 4, 5.25, 6, 7.25, 8, 9.25, 10, 11.25);
        CHECK(run(L).f64 == mixed);

        lir_free(L);

        types[0] = LT_I8;
        args[0]  = lir_i(249);

        L = fn(LT_I64);
        d = lir_reg(L, LIR_I64);

        push(L, call(callee(signed_byte), d, sig(LT_I8, types, 1), args));
        ret(L, d);

        CHECK(run(L).i == -7);

        lir_free(L);

        types[0] = LT_F64;
        args[0]  = lir_f(0.0);

        L = fn(LT_F64);

        push(L, tail(callee(cos), sig(LT_F64, types, 1), args));

        CHECK(run(L).f64 == 1.0);

        lir_free(L);
}

static void
check_memory(void)
{
        static struct {
                LirOp     ld;
                LirOp     st;
                LirScalar in;
                LirScalar want;
        } const cases[] = {
                { LIR_LD_I8,  LIR_ST8,    { .u = 255 },        { .i = -1 }         },
                { LIR_LD_U8,  LIR_ST8,    { .u = 255 },        { .u = 255 }        },
                { LIR_LD_I16, LIR_ST16,   { .u = 65535 },      { .i = -1 }         },
                { LIR_LD_U16, LIR_ST16,   { .u = 65535 },      { .u = 65535 }      },
                { LIR_LD_I32, LIR_ST32,   { .u = UINT32_MAX }, { .i = -1 }         },
                { LIR_LD_U32, LIR_ST32,   { .u = UINT32_MAX }, { .u = UINT32_MAX } },
                { LIR_LD_I64, LIR_ST64,   { .u = UINT64_MAX }, { .i = -1 }         },
                { LIR_LD_F32, LIR_ST_F32, { .f32 = 1.25f },    { .f32 = 1.25f }    },
                { LIR_LD_F64, LIR_ST_F64, { .f64 = 1.25 },     { .f64 = 1.25 }     }
        };

        for (u32 i = 0; i < countof(cases); ++i) {
                LirType  width = LirOps[cases[i].st].type;
                LirClass cls   = lir_type_class(width);
                LirType  type  = ClassType[cls];
                Lir     *L     = fn(type, LT_PTR, type);
                LirReg   index = lir_reg(L, LIR_I64);
                LirOpnd  mem   = lir_m(L->params[0], index, 4, -5);

                put(L, LIR_LI, index, lir_i(2));
                put(L, cases[i].st, LIR_NONE, mem, lir_r(L->params[1]));

                LirReg d = lir_reg(L, cls);

                put(L, cases[i].ld, d, mem);
                ret(L, d);

                u8 buf[32];
                memset(buf, 0xa5, sizeof buf);

                LirScalar out = run(L, S(ptr, buf), cases[i].in);

                CHECK(equal(cls, out, cases[i].want));
                CHECK(buf[2] == 0xa5 && buf[3 + lir_type_size(width)] == 0xa5);

                lir_free(L);
        }

        Lir    *L   = fn(LT_I64);
        LirReg  p   = lir_reg(L, LIR_PTR);
        LirReg  q   = lir_reg(L, LIR_PTR);
        LirReg  d   = lir_reg(L, LIR_I64);
        LirOpnd mem = deref(q, 56);

        put(L, LIR_ALLOCA, p, lir_i(8), lir_i(8));
        put(L, LIR_ALLOCA, q, lir_i(64), lir_i(64));
        put(L, LIR_ST64, LIR_NONE, mem, lir_i(789));
        put(L, LIR_LD_I64, d, mem);
        ret(L, d);

        CHECK(run(L).i == 789);

        lir_free(L);
}

static Lir *
triangle(void)
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
        put(L, LIR_ADD, sum, lir_r(sum), lir_r(i));
        put(L, LIR_ADD, i, lir_r(i), lir_i(1));
        put(L, LIR_JMP, LIR_NONE, lir_l(top));
        here(L, end);
        ret(L, sum);

        return L;
}

static void
check_flow(void)
{
        LirError err;
        LirBytes bytes;
        Lir     *L = triangle();

        CHECK(run(L, S(i, 1000)).i == 499500);
        CHECK(lir_serialize(ty, L, &bytes, &err));

        Lir *decoded = lir_deserialize(
                ty,
                bytes.items,
                bytes.count,
                bytes.holes,
                bytes.nholes,
                &err
        );

        CHECK(decoded != NULL);

        if (decoded != NULL) {
                CHECK(run(decoded, S(i, 1000)).i == 499500);
                lir_free(decoded);
        }

        lir_free(L);

        L = fn(LT_I64, LT_I64);

        LirLabel targets[3];
        for (u32 n = 0; n < 3; ++n) {
                targets[n] = lir_label(L);
        }

        LirLabel end = lir_label(L);

        push(L, jump_table(lir_r(L->params[0]), end, targets, 3));

        for (u32 n = 0; n < 3; ++n) {
                here(L, targets[n]);
                ret(L, lir_i(100 + n));
        }

        here(L, end);
        ret(L, lir_i(-1));

        for (i64 n = -1; n < 4; ++n) {
                CHECK(run(L, S(i, n)).i == ((n >= 0 && n < 3) ? 100 + n : -1));
        }

        lir_free(L);

        L = fn(LT_I64, LT_I64);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));

        LirReg   pin   = lir_pinned(L, LIR_PIN_0);
        LirLabel entry = lir_label(L);

        ret(L, lir_i(123));
        CHECK(lir_entry(L, entry));
        ret(L, pin);

        LirScalar out;
        LirScalar arg = S(i, 456);

        CHECK(lir_interpret_entry(NULL, L, entry, &arg, 1, &out, &err));
        CHECK(out.i == 456);
        CHECK(run(L, arg).i == 123);

        lir_free(L);
}

static void
check_atomics(void)
{
        static LirOp const ops[]  = { LIR_CAS, LIR_XADD, LIR_XCHG };
        static u64 const   after[] = { 11, 14, 7 };

        for (u32 n = 0; n < countof(ops); ++n) {
                Lir    *L   = fn(LT_I64, LT_PTR);
                LirReg  d   = lir_reg(L, LIR_I64);
                LirOpnd mem = deref(L->params[0], 0);

                emit(L, ops[n], d, O(mem, lir_i(7), lir_i(11)), LirOps[ops[n]].argc);
                put(L, LIR_FENCE, LIR_NONE);
                ret(L, d);

                u64 value = 7;

                CHECK(run(L, S(ptr, &value)).u == 7);
                CHECK(value == after[n]);

                if (ops[n] == LIR_CAS) {
                        value = 5;
                        CHECK(run(L, S(ptr, &value)).u == 5);
                        CHECK(value == 5);
                }

                lir_free(L);
        }
}

_Noreturn static void
jump_seven(void *env)
{
        _longjmp(*(jmp_buf *)env, 7);
}

static void
check_returns_twice(void)
{
        Lir *L = fn(LT_I64, LT_PTR);

        CHECK(lir_pin_param(L, LIR_PIN_0, 0));

        LirReg   env   = lir_pinned(L, LIR_PIN_0);
        LirReg   d     = lir_reg(L, LIR_I64);
        LirLabel again = lir_label(L);
        LirOpnd  args  = lir_r(env);
        LirInst  in    = call(callee(_setjmp), d, sig(LT_I32, T(LT_PTR), 1), &args);

        in.flags = LIR_RETURNS_TWICE | LIR_CALL_SITE;
        push(L, in);

        put(L, LIR_BRNZ, LIR_NONE, lir_r(d), lir_l(again));

        in = call(callee(jump_seven), LIR_NONE, sig(LT_VOID, T(LT_PTR), 1), &args);
        in.flags = LIR_NORETURN | LIR_CALL_SITE;
        push(L, in);

        here(L, again);
        ret(L, d);

        jmp_buf buf;
        CHECK(run(L, S(ptr, &buf)).i == 7);

        lir_free(L);
}

static void
check_vm(void)
{
        static LirRuntime const rt = {
                .interrupt  = &Interrupt,
                .poll       = handle_poll,
                .current_ty = current_ty
        };

        lir_set_runtime(&rt);

        Lir     *L     = fn(LT_I64);
        LirLabel deopt = lir_label(L);

        put(L, LIR_POLL, LIR_NONE, lir_i(0), lir_i(0), lir_i(17), lir_l(deopt));
        ret(L, lir_i(0));
        here(L, deopt);
        ret(L, lir_i(1));

        Interrupt = 0;
        CHECK(run(L).i == 0);
        CHECK(Polls == 0);

        Interrupt = 1;
        CHECK(run(L).i == 1);
        CHECK(Polls == 1 && LastInfo == (void *)17);

        lir_free(L);

        L = fn(LT_I64);
        L->mode = LIR_MODE_ATTACHED;

        LirReg   i   = lir_reg(L, LIR_I64);
        LirLabel top = lir_label(L);

        put(L, LIR_LI, i, lir_i(0));
        here(L, top);
        put(L, LIR_ADD, i, lir_r(i), lir_i(1));
        put(L, LIR_BR, LIR_NONE, lir_cc(LIR_LT), lir_r(i), lir_i(10), lir_l(top));
        ret(L, i);

        Interrupt = 1;
        CHECK(run(L).i == 10);
        CHECK(Polls == 2 && LastInfo == NULL);

        lir_free(L);

        L = fn(LT_I64);

        LirReg  p   = lir_vslot(L);
        LirReg  d   = lir_reg(L, LIR_I64);
        LirOpnd mem = field(p, z);

        put(L, LIR_ST64, LIR_NONE, mem, lir_i(42));
        put(L, LIR_LD_I64, d, mem);
        ret(L, d);

        Value slots[1] = {0};
        Ty    vm       = { .stack = { .items = slots, .count = 1, .capacity = 1 } };

        CurrentTy = &vm;
        CHECK(invoke(&vm, L, NULL, 0).i == 42);
        CHECK(slots[0].z == 42 && vm.stack.count == 1);

        lir_free(L);

        CurrentTy = &EmptyTy;
        lir_set_runtime(NULL);
}

static void
scalar_suite(Backend *exec, bool native)
{
        Exec   = exec;
        Native = native;

        check_integer();
        check_float();
        check_conversions();
        check_checked();
        check_conditions();
        check_calls();
        check_promotions();
        check_stack_bool();
        check_memory();
        check_flow();
        check_atomics();
        check_returns_twice();
        check_vm();
}

#endif
