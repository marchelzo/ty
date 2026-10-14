#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdarg.h>
#include <setjmp.h>

#include "ty.h"
#include "lir.h"

static u32 checks;
static u32 failures;
static Ty EmptyTy;
static Ty *CurrentTy = &EmptyTy;

static Ty *
current_ty(void)
{
        return CurrentTy;
}

#define CHECK(expr) do { \
        ++checks; \
        if (!(expr)) { \
                fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #expr); \
                ++failures; \
        } \
} while (0)

static Lir *
function(LirType ret, LirType const *types, u32 n)
{
        LirSig sig = { .ret = ret, .params = types, .nparams = n, .nfixed = n };
        LirError err;
        Lir *L = lir_new("interp-test", &sig, LIR_MODE_AUTO, &err);
        CHECK(L != NULL);
        if (L == NULL) {
                exit(1);
        }
        return L;
}

static void
emit(Lir *L, LirOp op, LirReg d, LirOpnd const *args, u32 n)
{
        CHECK(lir_emit_to(L, op, d, args, n));
}

static void
ret(Lir *L, LirOpnd x)
{
        emit(L, LIR_RET, LIR_NONE, &x, 1);
}

#ifdef LIR_NATIVE
static ffi_type *
native_type(LirType type)
{
        switch (type) {
        case LIR_VOID: return &ffi_type_void;
        case LIR_TYPE_I8: return &ffi_type_sint8;
        case LIR_TYPE_U8:
        case LIR_TYPE_BOOL: return &ffi_type_uint8;
        case LIR_TYPE_I16: return &ffi_type_sint16;
        case LIR_TYPE_U16: return &ffi_type_uint16;
        case LIR_TYPE_I32: return &ffi_type_sint32;
        case LIR_TYPE_U32: return &ffi_type_uint32;
        case LIR_TYPE_I64: return &ffi_type_sint64;
        case LIR_TYPE_U64: return &ffi_type_uint64;
        case LIR_TYPE_F32: return &ffi_type_float;
        case LIR_TYPE_F64: return &ffi_type_double;
        default: return &ffi_type_pointer;
        }
}

static bool
native_execute(Lir *L, LirScalar const *args, u32 nargs, LirScalar *out, LirError *err)
{
        LirCode *code = lir_finish(L, false, err);
        if (code == NULL) {
                return false;
        }
        ffi_type **types = __builtin_alloca(((usize)nargs + 1) * sizeof *types);
        void **values = __builtin_alloca(((usize)nargs + 1) * sizeof *values);
        ffi_cif cif;
        for (u32 i = 0; i < nargs; ++i) {
                types[i] = native_type(L->sig.params[i]);
                values[i] = (void *)&args[i];
        }
        CHECK(ffi_prep_cif(&cif, FFI_DEFAULT_ABI, nargs, native_type(L->sig.ret), types) == FFI_OK);
        ffi_call(&cif, FFI_FN(code->body), out, values);
        if (L->sig.ret == LIR_TYPE_I32) {
                out->i = (i32)out->u;
        }
        lir_code_free(code);
        return true;
}
#endif

static LirScalar
execute(Ty *ty, Lir *L, LirScalar const *args, u32 nargs)
{
        LirError err;
        LirScalar result = {0};
#ifdef LIR_NATIVE
        bool ok = native_execute(L, args, nargs, &result, &err);
        (void)ty;
#else
        bool ok = lir_interpret(ty, L, args, nargs, &result, &err);
#endif
        CHECK(ok);
        if (!ok) {
                fprintf(stderr, "op %u: %s\n", err.op, err.message);
                lir_dump(L, stderr);
        }
        return result;
}

static LirScalar
numeric(LirOp op, LirClass cls, LirScalar a, LirScalar b, LirScalar c)
{
        LirType type = cls == LIR_I32 ? LIR_TYPE_I32 : LIR_TYPE_I64;
        LirType types[3];
        if (cls == LIR_F32) {
                type = LIR_TYPE_F32;
        } else if (cls == LIR_F64) {
                type = LIR_TYPE_F64;
        }
        for (u32 i = 0; i < 3; ++i) {
                types[i] = type;
        }
        Lir *L = function(type, types, 3);
        LirReg r[3];
        LirOpnd args[3];
        for (u32 i = 0; i < 3; ++i) {
                r[i] = L->params[i];
                if (cls == LIR_I32) {
                        r[i] = lir_reg(L, LIR_I32);
                        emit(L, LIR_ZEXT32, r[i], (LirOpnd[]) { lir_r(L->params[i]) }, 1);
                }
                args[i] = lir_r(r[i]);
        }
        LirReg d = lir_reg(L, cls);
        emit(L, op, d, args, LirOps[op].argc);
        ret(L, lir_r(d));
        LirScalar values[] = { a, b, c };
        LirScalar result = execute(NULL, L, values, 3);
        lir_free(L);
        return result;
}

static void
check_integer(void)
{
        struct integer_case {
                LirOp op;
                u64 a;
                u64 b;
                u64 expected;
        } cases[] = {
                { LIR_ADD, UINT64_MAX, 3, 2 },
                { LIR_SUB, 1, 3, UINT64_MAX - 1 },
                { LIR_MUL, 0x12345678, 17, 0x13579bdf8 },
                { LIR_MULHS, (u64)-7, 3, UINT64_MAX },
                { LIR_MULHU, UINT64_MAX, 2, 1 },
                { LIR_SDIV, (u64)-101, 7, (u64)-14 },
                { LIR_SREM, (u64)-101, 7, (u64)-3 },
                { LIR_UDIV, UINT64_MAX, 2, INT64_MAX },
                { LIR_UREM, UINT64_MAX, 2, 1 },
                { LIR_AND, 0xcafe, 0xf0f, 0xa0e },
                { LIR_OR, 0xcafe, 0xf0f, 0xcfff },
                { LIR_XOR, 0xcafe, 0xf0f, 0xc5f1 },
                { LIR_SHL, 17, 65, 34 },
                { LIR_SHR, UINT64_MAX, 65, INT64_MAX },
                { LIR_SAR, (u64)-8, 2, (u64)-2 },
                { LIR_ROTR, 1, 1, (u64)1 << 63 },
                { LIR_NEG, 7, 0, (u64)-7 },
                { LIR_NOT, 0xcafe, 0, ~((u64)0xcafe) },
                { LIR_CLZ, 1, 0, 63 },
                { LIR_CTZ, 0x800, 0, 11 },
                { LIR_POPCNT, 0xa55a, 0, 8 },
                { LIR_BSWAP, 0x0123456789abcdef, 0, 0xefcdab8967452301 },
                { LIR_SEXT8, 0xfedcba9876543280, 0, (u64)-128 },
                { LIR_SEXT16, 0xdead8000, 0, (u64)-32768 },
                { LIR_SEXT32, 0xdeadbeef80000000, 0, (u64)INT32_MIN },
                { LIR_ZEXT8, UINT64_MAX, 0, 255 },
                { LIR_ZEXT16, UINT64_MAX, 0, 65535 },
                { LIR_ZEXT32, UINT64_MAX, 0, UINT32_MAX }
        };
        for (u32 i = 0; i < countof(cases); ++i) {
                LirScalar a = { .u = cases[i].a };
                LirScalar b = { .u = cases[i].b };
                LirScalar result = numeric(cases[i].op, LIR_I64, a, b, (LirScalar) {0});
                CHECK(result.u == cases[i].expected);
        }
        LirScalar result = numeric(LIR_ADD, LIR_I32, (LirScalar) { .u = UINT32_MAX },
                                   (LirScalar) { .u = 2 }, (LirScalar) {0});
        CHECK(result.i == 1);
        result = numeric(LIR_SDIV, LIR_I32, (LirScalar) { .u = (u32)-101 },
                         (LirScalar) { .u = 7 }, (LirScalar) {0});
        CHECK(result.i == -14);
        result = numeric(LIR_ROTR, LIR_I32, (LirScalar) { .u = 1 },
                         (LirScalar) { .u = 1 }, (LirScalar) {0});
        CHECK(result.i == INT32_MIN);
        result = numeric(LIR_MULHU, LIR_I32, (LirScalar) { .u = UINT32_MAX },
                         (LirScalar) { .u = 2 }, (LirScalar) {0});
        CHECK(result.u == 1);
        result = numeric(LIR_CLZ, LIR_I32, (LirScalar) {0}, (LirScalar) {0}, (LirScalar) {0});
        CHECK(result.i == 32);
        result = numeric(LIR_CTZ, LIR_I64, (LirScalar) {0}, (LirScalar) {0}, (LirScalar) {0});
        CHECK(result.i == 64);
        result = numeric(LIR_SDIV, LIR_I64, (LirScalar) { .i = INT64_MIN },
                         (LirScalar) { .i = -1 }, (LirScalar) {0});
        CHECK(result.i == INT64_MIN);
        result = numeric(LIR_SREM, LIR_I64, (LirScalar) { .i = INT64_MIN },
                         (LirScalar) { .i = -1 }, (LirScalar) {0});
        CHECK(result.i == 0);
}

static void
check_float(void)
{
        struct float_case {
                LirOp op;
                double a;
                double b;
                double c;
                double expected;
        } cases[] = {
                { LIR_FADD, 3.5, 2.0, 0.0, 5.5 },
                { LIR_FSUB, 3.5, 2.0, 0.0, 1.5 },
                { LIR_FMUL, 3.5, 2.0, 0.0, 7.0 },
                { LIR_FDIV, 3.5, 2.0, 0.0, 1.75 },
                { LIR_FMIN, 3.5, 2.0, 0.0, 2.0 },
                { LIR_FMAX, 3.5, 2.0, 0.0, 3.5 },
                { LIR_FSQRT, 25.0, 0.0, 0.0, 5.0 },
                { LIR_FABS, -3.5, 0.0, 0.0, 3.5 },
                { LIR_FNEG, 3.5, 0.0, 0.0, -3.5 },
                { LIR_FMA, 3.5, 2.0, 1.0, 8.0 }
        };
        for (u32 i = 0; i < countof(cases); ++i) {
                LirScalar result = numeric(cases[i].op, LIR_F64,
                                           (LirScalar) { .f64 = cases[i].a },
                                           (LirScalar) { .f64 = cases[i].b },
                                           (LirScalar) { .f64 = cases[i].c });
                CHECK(result.f64 == cases[i].expected);
                result = numeric(cases[i].op, LIR_F32,
                                 (LirScalar) { .f32 = cases[i].a },
                                 (LirScalar) { .f32 = cases[i].b },
                                 (LirScalar) { .f32 = cases[i].c });
                CHECK(result.f32 == cases[i].expected);
        }
        LirScalar result = numeric(LIR_FMA, LIR_F64,
                                   (LirScalar) { .f64 = 0x1.0000000000001p0 },
                                   (LirScalar) { .f64 = 0x1.fffffffffffffp-1 },
                                   (LirScalar) { .f64 = -1.0 });
        CHECK(result.f64 == 0x1.ffffffffffffep-54);
        result = numeric(LIR_FMA, LIR_F32,
                         (LirScalar) { .f32 = 0x1.000002p0f },
                         (LirScalar) { .f32 = 0x1.fffffep-1f },
                         (LirScalar) { .f32 = -1.0f });
        CHECK(result.f32 == 0x1.fffffcp-25f);
        result = numeric(LIR_FNEG, LIR_F64, (LirScalar) { .f64 = 0.0 },
                         (LirScalar) {0}, (LirScalar) {0});
        CHECK(signbit(result.f64));
        result = numeric(LIR_FMIN, LIR_F64, (LirScalar) { .f64 = NAN },
                         (LirScalar) { .f64 = 3.0 }, (LirScalar) {0});
        CHECK(result.f64 == 3.0);
}

static void
check_conversions(void)
{
        struct conversion_case {
                LirOp op;
                LirType src;
                LirType dst;
                LirClass cls;
                LirScalar input;
                LirScalar expected;
        } cases[] = {
                { LIR_I2F, LIR_TYPE_I64, LIR_TYPE_F64, LIR_F64, { .i = -17 }, { .f64 = -17.0 } },
                { LIR_U2F, LIR_TYPE_U64, LIR_TYPE_F64, LIR_F64, { .u = UINT64_MAX }, { .f64 = 0x1p64 } },
                { LIR_U2F, LIR_TYPE_U64, LIR_TYPE_F32, LIR_F32, { .u = UINT64_MAX }, { .f32 = 0x1p64f } },
                { LIR_F2I, LIR_TYPE_F64, LIR_TYPE_I64, LIR_I64, { .f64 = -17.9 }, { .i = -17 } },
                { LIR_F2I, LIR_TYPE_F64, LIR_TYPE_I64, LIR_I64, { .f64 = NAN }, { .i = INT64_MIN } },
                { LIR_FEXT, LIR_TYPE_F32, LIR_TYPE_F64, LIR_F64, { .f32 = 1.5f }, { .f64 = 1.5 } },
                { LIR_FTRUNC, LIR_TYPE_F64, LIR_TYPE_F32, LIR_F32, { .f64 = 1.5 }, { .f32 = 1.5f } },
                { LIR_BITCAST, LIR_TYPE_F64, LIR_TYPE_I64, LIR_I64, { .f64 = -0.0 }, { .u = 1ULL << 63 } },
                { LIR_BITCAST, LIR_TYPE_I64, LIR_TYPE_F64, LIR_F64,
                  { .u = 0x3ff0000000000000 }, { .f64 = 1.0 } }
        };
        for (u32 i = 0; i < countof(cases); ++i) {
                Lir *L = function(cases[i].dst, &cases[i].src, 1);
                LirReg r = lir_reg(L, cases[i].cls);
                emit(L, cases[i].op, r, (LirOpnd[]) { lir_r(L->params[0]) }, 1);
                ret(L, lir_r(r));
                LirScalar result = execute(NULL, L, &cases[i].input, 1);
#ifdef LIR_NATIVE
                if (cases[i].op == LIR_F2I && isnan(cases[i].input.f64)) {
                        lir_free(L);
                        continue;
                }
#endif
                if (cases[i].cls == LIR_F32) {
                        CHECK(result.f32 == cases[i].expected.f32);
                } else {
                        CHECK(result.u == cases[i].expected.u);
                }
                lir_free(L);
        }
}

static void
check_checked(void)
{
        LirOp ops[] = { LIR_ADDO, LIR_SUBO, LIR_MULO };
        for (u32 i = 0; i < countof(ops); ++i) {
                LirType types[] = { LIR_TYPE_I64, LIR_TYPE_I64 };
                Lir *L = function(LIR_TYPE_I64, types, 2);
                LirReg d = lir_reg(L, LIR_I64);
                LirLabel overflow = lir_label(L);
                emit(L, ops[i], d,
                     (LirOpnd[]) { lir_r(L->params[0]), lir_r(L->params[1]), lir_l(overflow) }, 3);
                ret(L, lir_i(0));
                CHECK(lir_bind(L, overflow));
                ret(L, lir_i(1));
                LirScalar args[] = { { .i = 2 }, { .i = 3 } };
                CHECK(execute(NULL, L, args, 2).i == 0);
                args[0].i = i == 1 ? INT64_MIN : INT64_MAX;
                args[1].i = i == 2 ? 2 : 1;
                CHECK(execute(NULL, L, args, 2).i == 1);
                lir_free(L);
        }
}

static void
check_conditions(void)
{
        for (LirCC cc = LIR_EQ; cc < LIR_CC_COUNT; ++cc) {
                bool fp = cc >= LIR_FEQ;
                LirType types[] = { fp ? LIR_TYPE_F64 : LIR_TYPE_I64,
                                    fp ? LIR_TYPE_F64 : LIR_TYPE_I64 };
                Lir *L = function(LIR_TYPE_I64, types, 2);
                LirReg d = lir_reg(L, LIR_I64);
                emit(L, fp ? LIR_FSETCC : LIR_SETCC, d,
                     (LirOpnd[]) { lir_cc(cc), lir_r(L->params[0]), lir_r(L->params[1]) }, 3);
                ret(L, lir_r(d));
                LirScalar args[] = { { .i = -1 }, { .i = 1 } };
                bool expected[] = { false, true, true, true, false, false,
                                    false, false, true, true };
                if (fp) {
                        args[0].f64 = NAN;
                        args[1].f64 = 1.0;
                        CHECK(execute(NULL, L, args, 2).i == (cc == LIR_FNE || cc == LIR_FUN));
                } else {
                        CHECK(execute(NULL, L, args, 2).i == expected[cc]);
                }
                lir_free(L);
        }
        LirType types[] = { LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, 1);
        LirReg d = lir_reg(L, LIR_I64);
        emit(L, LIR_SELECT, d,
             (LirOpnd[]) { lir_cc(LIR_GT), lir_r(L->params[0]), lir_i(0), lir_i(7), lir_i(9) }, 5);
        ret(L, lir_r(d));
        CHECK(execute(NULL, L, (LirScalar[]) { { .i = 1 } }, 1).i == 7);
        CHECK(execute(NULL, L, (LirScalar[]) { { .i = -1 } }, 1).i == 9);
        lir_free(L);
}

static double
mix12(i64 a, double b, i64 c, double d, i64 e, double f,
      i64 g, double h, i64 i, double j, i64 k, double l)
{
        return a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h + 9*i + 10*j + 11*k + 12*l;
}

static double
sum_varargs(i32 n, ...)
{
        va_list ap;
        double sum = 0.0;
        va_start(ap, n);
        for (i32 i = 0; i < n; ++i) {
                sum += i % 2 ? va_arg(ap, double) : (double)va_arg(ap, i64);
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
        i32 a = va_arg(ap, i32);
        i32 b = va_arg(ap, i32);
        i32 c = va_arg(ap, i32);
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
                types[i] = i == 8 ? LIR_TYPE_BOOL : LIR_TYPE_I64;
                args[i] = lir_i(i == 8 ? 2 : 0);
        }
        Lir *L = function(LIR_TYPE_I64, NULL, 0);
        LirReg d = lir_reg(L, LIR_I64);
        LirInst in = {
                .op = LIR_CALL, .dst = d,
                .args = { lir_i((iptr)bool_last) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_I64, .params = types, .nparams = countof(types),
                         .nfixed = countof(types) },
                .call_args = args, .ncall_args = countof(args)
        };
        CHECK(lir_emit(L, &in));
        ret(L, lir_r(d));
        CHECK(execute(NULL, L, NULL, 0).i == 1);
        lir_free(L);
}

static void
check_promotions(void)
{
        LirType types[] = { LIR_TYPE_I32, LIR_TYPE_I8, LIR_TYPE_U16, LIR_TYPE_BOOL, LIR_TYPE_F32 };
        LirOpnd args[] = { lir_i(0), lir_i(249), lir_i(65535), lir_i(2), lir_f(1.25) };
        Lir *L = function(LIR_TYPE_F64, NULL, 0);
        LirReg d = lir_reg(L, LIR_F64);
        LirInst in = {
                .op = LIR_CALL, .dst = d,
                .args = { lir_i((iptr)promoted_sum) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_F64, .params = types, .nparams = countof(types),
                         .nfixed = 1, .variadic = true },
                .call_args = args, .ncall_args = countof(args)
        };
        CHECK(lir_emit(L, &in));
        ret(L, lir_r(d));
        CHECK(execute(NULL, L, NULL, 0).f64 == 65530.25);
        lir_free(L);
}

static void
check_calls(void)
{
        LirType types[13];
        LirOpnd args[13];
        for (u32 n = 0; n <= 12; ++n) {
                Lir *L = function(LIR_TYPE_F64, NULL, 0);
                types[0] = LIR_TYPE_I32;
                args[0] = lir_i(n);
                double expected = 0.0;
                for (u32 i = 0; i < n; ++i) {
                        types[i+1] = i % 2 ? LIR_TYPE_F64 : LIR_TYPE_I64;
                        args[i+1] = i % 2 ? lir_f(i + 0.25) : lir_i(-(i64)i);
                        expected += i % 2 ? i + 0.25 : -(double)i;
                }
                LirReg d = lir_reg(L, LIR_F64);
                LirInst in = {
                        .op = LIR_CALL, .dst = d, .args = { lir_i((iptr)sum_varargs) }, .nargs = 1,
                        .sig = { .ret = LIR_TYPE_F64, .params = types, .nparams = n + 1,
                                 .nfixed = 1, .variadic = true },
                        .call_args = args, .ncall_args = n + 1
                };
                CHECK(lir_emit(L, &in));
                ret(L, lir_r(d));
                CHECK(execute(NULL, L, NULL, 0).f64 == expected);
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_F64, NULL, 0);
        for (u32 i = 0; i < 12; ++i) {
                types[i] = i % 2 ? LIR_TYPE_F64 : LIR_TYPE_I64;
                args[i] = i % 2 ? lir_f(i + 0.25) : lir_i(i);
        }
        LirReg d = lir_reg(L, LIR_F64);
        LirInst in = {
                .op = LIR_CALL, .dst = d, .args = { lir_i((iptr)mix12) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_F64, .params = types, .nparams = 12, .nfixed = 12 },
                .call_args = args, .ncall_args = 12
        };
        CHECK(lir_emit(L, &in));
        ret(L, lir_r(d));
        CHECK(execute(NULL, L, NULL, 0).f64 == mix12(0, 1.25, 2, 3.25, 4, 5.25, 6, 7.25, 8, 9.25, 10, 11.25));
        lir_free(L);
        types[0] = LIR_TYPE_I8;
        args[0] = lir_i(249);
        L = function(LIR_TYPE_I64, NULL, 0);
        d = lir_reg(L, LIR_I64);
        in = (LirInst) {
                .op = LIR_CALL, .dst = d, .args = { lir_i((iptr)signed_byte) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_I8, .params = types, .nparams = 1, .nfixed = 1 },
                .call_args = args, .ncall_args = 1
        };
        CHECK(lir_emit(L, &in));
        ret(L, lir_r(d));
        CHECK(execute(NULL, L, NULL, 0).i == -7);
        lir_free(L);
        L = function(LIR_TYPE_F64, NULL, 0);
        types[0] = LIR_TYPE_F64;
        args[0] = lir_f(0.0);
        in = (LirInst) {
                .op = LIR_TAILCALL, .dst = LIR_NONE, .args = { lir_i((iptr)cos) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_F64, .params = types, .nparams = 1, .nfixed = 1 },
                .call_args = args, .ncall_args = 1
        };
        CHECK(lir_emit(L, &in));
        CHECK(execute(NULL, L, NULL, 0).f64 == 1.0);
        lir_free(L);
}

static void
check_memory(void)
{
        struct memory_case {
                LirOp load;
                LirOp store;
                LirType type;
                LirClass cls;
                LirScalar value;
                LirScalar expected;
                usize size;
        } cases[] = {
                { LIR_LD_I8, LIR_ST8, LIR_TYPE_I64, LIR_I64, { .u = 255 }, { .i = -1 }, 1 },
                { LIR_LD_U8, LIR_ST8, LIR_TYPE_I64, LIR_I64, { .u = 255 }, { .u = 255 }, 1 },
                { LIR_LD_I16, LIR_ST16, LIR_TYPE_I64, LIR_I64, { .u = 65535 }, { .i = -1 }, 2 },
                { LIR_LD_U16, LIR_ST16, LIR_TYPE_I64, LIR_I64, { .u = 65535 }, { .u = 65535 }, 2 },
                { LIR_LD_I32, LIR_ST32, LIR_TYPE_I64, LIR_I64, { .u = UINT32_MAX }, { .i = -1 }, 4 },
                { LIR_LD_U32, LIR_ST32, LIR_TYPE_I64, LIR_I64, { .u = UINT32_MAX }, { .u = UINT32_MAX }, 4 },
                { LIR_LD_I64, LIR_ST64, LIR_TYPE_I64, LIR_I64, { .u = UINT64_MAX }, { .i = -1 }, 8 },
                { LIR_LD_F32, LIR_ST_F32, LIR_TYPE_F32, LIR_F32, { .f32 = 1.25f }, { .f32 = 1.25f }, 4 },
                { LIR_LD_F64, LIR_ST_F64, LIR_TYPE_F64, LIR_F64, { .f64 = 1.25 }, { .f64 = 1.25 }, 8 }
        };
        for (u32 i = 0; i < countof(cases); ++i) {
                LirType types[] = { LIR_TYPE_PTR, cases[i].type };
                Lir *L = function(cases[i].type, types, 2);
                LirReg index = lir_reg(L, LIR_I64);
                emit(L, LIR_LI, index, (LirOpnd[]) { lir_i(2) }, 1);
                LirOpnd mem = lir_m(L->params[0], index, 4, -5);
                emit(L, cases[i].store, LIR_NONE, (LirOpnd[]) { mem, lir_r(L->params[1]) }, 2);
                LirReg d = lir_reg(L, cases[i].cls);
                emit(L, cases[i].load, d, &mem, 1);
                ret(L, lir_r(d));
                u8 buf[32];
                memset(buf, 0xa5, sizeof buf);
                LirScalar args[] = { { .ptr = buf }, cases[i].value };
                LirScalar result = execute(NULL, L, args, 2);
                if (cases[i].cls == LIR_F32) {
                        CHECK(result.f32 == cases[i].expected.f32);
                } else {
                        CHECK(result.u == cases[i].expected.u);
                }
                CHECK(buf[2] == 0xa5 && buf[3 + cases[i].size] == 0xa5);
                lir_free(L);
        }
        Lir *L = function(LIR_TYPE_I64, NULL, 0);
        LirReg p = lir_reg(L, LIR_PTR);
        LirReg q = lir_reg(L, LIR_PTR);
        LirReg d = lir_reg(L, LIR_I64);
        emit(L, LIR_ALLOCA, p, (LirOpnd[]) { lir_i(8), lir_i(8) }, 2);
        emit(L, LIR_ALLOCA, q, (LirOpnd[]) { lir_i(64), lir_i(64) }, 2);
        LirOpnd mem = lir_m(q, LIR_NONE, 1, 56);
        emit(L, LIR_ST64, LIR_NONE, (LirOpnd[]) { mem, lir_i(789) }, 2);
        emit(L, LIR_LD_I64, d, &mem, 1);
        ret(L, lir_r(d));
        CHECK(execute(NULL, L, NULL, 0).i == 789);
        lir_free(L);
}

static void
check_flow(void)
{
        LirType type = LIR_TYPE_I64;
        Lir *L = function(type, &type, 1);
        LirReg i = lir_reg(L, LIR_I64);
        LirReg sum = lir_reg(L, LIR_I64);
        LirLabel loop = lir_label(L);
        LirLabel end = lir_label(L);
        emit(L, LIR_LI, i, (LirOpnd[]) { lir_i(0) }, 1);
        emit(L, LIR_LI, sum, (LirOpnd[]) { lir_i(0) }, 1);
        CHECK(lir_bind(L, loop));
        emit(L, LIR_BR, LIR_NONE,
             (LirOpnd[]) { lir_cc(LIR_GE), lir_r(i), lir_r(L->params[0]), lir_l(end) }, 4);
        emit(L, LIR_ADD, sum, (LirOpnd[]) { lir_r(sum), lir_r(i) }, 2);
        emit(L, LIR_ADD, i, (LirOpnd[]) { lir_r(i), lir_i(1) }, 2);
        emit(L, LIR_JMP, LIR_NONE, (LirOpnd[]) { lir_l(loop) }, 1);
        CHECK(lir_bind(L, end));
        ret(L, lir_r(sum));
        CHECK(execute(NULL, L, (LirScalar[]) { { .i = 1000 } }, 1).i == 499500);
        LirError err;
        LirBytes bytes;
        CHECK(lir_serialize(L, &bytes, &err));
        Lir *decoded = lir_deserialize(bytes.items, bytes.count, bytes.holes, bytes.nholes, &err);
        CHECK(decoded != NULL);
        if (decoded != NULL) {
                CHECK(execute(NULL, decoded, (LirScalar[]) { { .i = 1000 } }, 1).i == 499500);
                lir_free(decoded);
        }
        lir_bytes_free(&bytes);
        lir_free(L);
        L = function(type, &type, 1);
        LirLabel targets[3];
        for (u32 n = 0; n < 3; ++n) {
                targets[n] = lir_label(L);
        }
        end = lir_label(L);
        LirInst in = {
                .op = LIR_SWITCH, .dst = LIR_NONE,
                .args = { lir_r(L->params[0]), lir_l(end) }, .nargs = 2,
                .targets = targets, .ntargets = 3
        };
        CHECK(lir_emit(L, &in));
        for (u32 n = 0; n < 3; ++n) {
                CHECK(lir_bind(L, targets[n]));
                ret(L, lir_i(100 + n));
        }
        CHECK(lir_bind(L, end));
        ret(L, lir_i(-1));
        for (i64 n = -1; n < 4; ++n) {
                CHECK(execute(NULL, L, (LirScalar[]) { { .i = n } }, 1).i == (n >= 0 && n < 3 ? 100 + n : -1));
        }
        lir_free(L);
        L = function(type, &type, 1);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
        LirReg pin = lir_pinned(L, LIR_PIN_0);
        ret(L, lir_i(123));
        LirLabel entry = lir_label(L);
        CHECK(lir_entry(L, entry));
        ret(L, lir_r(pin));
        LirScalar out;
        CHECK(lir_interpret_entry(NULL, L, entry, (LirScalar[]) { { .i = 456 } }, 1, &out, &err));
        CHECK(out.i == 456);
        CHECK(execute(NULL, L, (LirScalar[]) { { .i = 456 } }, 1).i == 123);
        lir_free(L);
}

static void
check_atomics(void)
{
        LirType type = LIR_TYPE_PTR;
        LirOp ops[] = { LIR_CAS, LIR_XADD, LIR_XCHG };
        for (u32 n = 0; n < countof(ops); ++n) {
                Lir *L = function(LIR_TYPE_I64, &type, 1);
                LirReg d = lir_reg(L, LIR_I64);
                LirOpnd mem = lir_m(L->params[0], LIR_NONE, 1, 0);
                emit(L, ops[n], d, (LirOpnd[]) { mem, lir_i(7), lir_i(11) }, LirOps[ops[n]].argc);
                emit(L, LIR_FENCE, LIR_NONE, NULL, 0);
                ret(L, lir_r(d));
                u64 value = 7;
                LirScalar args[] = { { .ptr = &value } };
                CHECK(execute(NULL, L, args, 1).u == 7);
                CHECK(value == (n == 0 ? 11 : n == 1 ? 14 : 7));
                if (n == 0) {
                        value = 5;
                        CHECK(execute(NULL, L, args, 1).u == 5);
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
        LirType type = LIR_TYPE_PTR;
        Lir *L = function(LIR_TYPE_I64, &type, 1);
        CHECK(lir_pin_param(L, LIR_PIN_0, 0));
        LirReg env = lir_pinned(L, LIR_PIN_0);
        LirReg d = lir_reg(L, LIR_I64);
        LirLabel again = lir_label(L);
        LirOpnd args[] = { lir_r(env) };
        LirInst in = {
                .op = LIR_CALL, .dst = d,
                .args = { lir_i((iptr)_setjmp) }, .nargs = 1,
                .sig = { .ret = LIR_TYPE_I32, .params = &type, .nparams = 1, .nfixed = 1 },
                .flags = LIR_RETURNS_TWICE | LIR_CALL_SITE,
                .call_args = args, .ncall_args = 1
        };
        CHECK(lir_emit(L, &in));
        emit(L, LIR_BRNZ, LIR_NONE, (LirOpnd[]) { lir_r(d), lir_l(again) }, 2);
        in.dst = LIR_NONE;
        in.args[0] = lir_i((iptr)jump_seven);
        in.sig.ret = LIR_VOID;
        in.flags = LIR_NORETURN | LIR_CALL_SITE;
        CHECK(lir_emit(L, &in));
        CHECK(lir_bind(L, again));
        ret(L, lir_r(d));
        jmp_buf buf;
        CHECK(execute(NULL, L, (LirScalar[]) { { .ptr = &buf } }, 1).i == 7);
        lir_free(L);
}

static volatile sig_atomic_t Interrupt;
static u32 polls;
static void const *LastInfo;

static i32
handle_poll(Ty *ty, Value *top, void const *info)
{
        (void)ty;
        (void)top;
        ++polls;
        Interrupt = 0;
        LastInfo = info;
        return info != NULL;
}

static void
check_vm(void)
{
        static LirRuntime const runtime = {
                .interrupt = &Interrupt, .poll = handle_poll, .current_ty = current_ty
        };
        lir_set_runtime(&runtime);
        Lir *L = function(LIR_TYPE_I64, NULL, 0);
        LirLabel deopt = lir_label(L);
        emit(L, LIR_POLL, LIR_NONE,
             (LirOpnd[]) { lir_i(0), lir_i(0), lir_i(17), lir_l(deopt) }, 4);
        ret(L, lir_i(0));
        CHECK(lir_bind(L, deopt));
        ret(L, lir_i(1));
        Interrupt = 0;
        CHECK(execute(NULL, L, NULL, 0).i == 0);
        CHECK(polls == 0);
        Interrupt = 1;
        CHECK(execute(NULL, L, NULL, 0).i == 1);
        CHECK(polls == 1 && LastInfo == (void *)17);
        lir_free(L);
        L = function(LIR_TYPE_I64, NULL, 0);
        L->mode = LIR_MODE_ATTACHED;
        LirReg i = lir_reg(L, LIR_I64);
        LirLabel loop = lir_label(L);
        emit(L, LIR_LI, i, (LirOpnd[]) { lir_i(0) }, 1);
        CHECK(lir_bind(L, loop));
        emit(L, LIR_ADD, i, (LirOpnd[]) { lir_r(i), lir_i(1) }, 2);
        emit(L, LIR_BR, LIR_NONE,
             (LirOpnd[]) { lir_cc(LIR_LT), lir_r(i), lir_i(10), lir_l(loop) }, 4);
        ret(L, lir_r(i));
        Interrupt = 1;
        CHECK(execute(NULL, L, NULL, 0).i == 10);
        CHECK(polls == 2 && LastInfo == NULL);
        lir_free(L);
        L = function(LIR_TYPE_I64, NULL, 0);
        LirReg p = lir_vslot(L);
        LirReg d = lir_reg(L, LIR_I64);
        LirOpnd mem = lir_m(p, LIR_NONE, 1, offsetof(Value, z));
        emit(L, LIR_ST64, LIR_NONE, (LirOpnd[]) { mem, lir_i(42) }, 2);
        emit(L, LIR_LD_I64, d, &mem, 1);
        ret(L, lir_r(d));
        Value slots[1] = {0};
        Ty ty = { .stack = { .items = slots, .count = 1, .capacity = 1 } };
        CurrentTy = &ty;
        CHECK(execute(&ty, L, NULL, 0).i == 42);
        CHECK(slots[0].z == 42 && ty.stack.count == 1);
        lir_free(L);
        CurrentTy = &EmptyTy;
        lir_set_runtime(NULL);
}

int
main(void)
{
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
        printf("LIR interpreter: %u checks, %u failures\n", checks, failures);
        return failures != 0;
}
