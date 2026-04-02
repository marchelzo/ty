#include <math.h>
#include <stdlib.h>
#include <string.h>

#include "ty.h"
#include "value.h"
#include "vm.h"
#include "functions.h"

#ifdef __APPLE__
#define NewThread TY_NewThread_
#include <Accelerate/Accelerate.h>
#undef NewThread
#endif

enum {
        DTYPE_F64,
        DTYPE_F32,
        DTYPE_I64,
        DTYPE_I32,
        DTYPE_I16,
        DTYPE_I8,
        DTYPE_U8,
        DTYPE_BOOL,
        DTYPE_COUNT
};

#define DTYPE_IS_FLOAT(dt)    ((dt) <= DTYPE_F32)
#define DTYPE_IS_SIGNED(dt)   ((dt) >= DTYPE_I64 && (dt) <= DTYPE_I8)
#define DTYPE_IS_UNSIGNED(dt) ((dt) >= DTYPE_U8)
#define DTYPE_IS_INT(dt)      ((dt) >= DTYPE_I64)

#define MAX_NDIM 32

#define esz(dt) ((esz)(ty, (dt)))
static inline int
(esz)(Ty *ty, int dt)
{
        static const int sizes[] = { 8, 4, 8, 4, 2, 1, 1, 1 };
        if (UNLIKELY(dt < 0 || dt >= DTYPE_COUNT)) {
                zP("accelerate: invalid dtype: %d", dt);
        }

        return sizes[dt];
}

static inline double
getd(const void *p, i64 i, int dt)
{
        switch (dt) {
        case DTYPE_F64:  return ((const double *)p)[i];
        case DTYPE_F32:  return ((const float *)p)[i];
        case DTYPE_I64:  return (double)((const i64 *)p)[i];
        case DTYPE_I32:  return ((const i32 *)p)[i];
        case DTYPE_I16:  return ((const i16 *)p)[i];
        case DTYPE_I8:   return ((const i8 *)p)[i];
        case DTYPE_U8:   return ((const u8 *)p)[i];
        case DTYPE_BOOL: return ((const u8 *)p)[i];
        default:         return 0;
        }
}

static inline void
setd(void *p, i64 i, double v, int dt)
{
        switch (dt) {
        case DTYPE_F64:  ((double *)p)[i] = v;       break;
        case DTYPE_F32:  ((float *)p)[i] = (float)v; break;
        case DTYPE_I64:  ((i64 *)p)[i] = (i64)v;     break;
        case DTYPE_I32:  ((i32 *)p)[i] = (i32)v;     break;
        case DTYPE_I16:  ((i16 *)p)[i] = (i16)v;     break;
        case DTYPE_I8:   ((i8 *)p)[i] = (i8)v;       break;
        case DTYPE_U8:   ((u8 *)p)[i] = (u8)v;       break;
        case DTYPE_BOOL: ((u8 *)p)[i] = (v != 0);    break;
        }
}

static inline double
valtod(Value v)
{
        return (v.type == VALUE_REAL) ? v.real : (double)v.z;
}

#define DISPATCH(dt, ...) \
        switch (dt) { \
        case DTYPE_F64:  { typedef double T; __VA_ARGS__ } break; \
        case DTYPE_F32:  { typedef float  T; __VA_ARGS__ } break; \
        case DTYPE_I64:  { typedef i64    T; __VA_ARGS__ } break; \
        case DTYPE_I32:  { typedef i32    T; __VA_ARGS__ } break; \
        case DTYPE_I16:  { typedef i16    T; __VA_ARGS__ } break; \
        case DTYPE_I8:   { typedef i8     T; __VA_ARGS__ } break; \
        case DTYPE_U8:   { typedef u8     T; __VA_ARGS__ } break; \
        case DTYPE_BOOL: { typedef u8     T; __VA_ARGS__ } break; \
        }

#define DISPATCH_FLOAT(dt, ...) \
        switch (dt) { \
        case DTYPE_F64: { typedef double T; __VA_ARGS__ } break; \
        case DTYPE_F32: { typedef float  T; __VA_ARGS__ } break; \
        default: bP("expected float dtype, got %d", (int)(dt)); \
        }

#define DISPATCH_SIGNED(dt, ...) \
        switch (dt) { \
        case DTYPE_F64:  { typedef double T; __VA_ARGS__ } break; \
        case DTYPE_F32:  { typedef float  T; __VA_ARGS__ } break; \
        case DTYPE_I64:  { typedef i64    T; __VA_ARGS__ } break; \
        case DTYPE_I32:  { typedef i32    T; __VA_ARGS__ } break; \
        case DTYPE_I16:  { typedef i16    T; __VA_ARGS__ } break; \
        case DTYPE_I8:   { typedef i8     T; __VA_ARGS__ } break; \
        }

static const int PROMOTE[8][8] = {
        { 0, 0, 0, 0, 0, 0, 0, 0 },
        { 0, 1, 0, 0, 1, 1, 1, 1 },
        { 0, 0, 2, 2, 2, 2, 2, 2 },
        { 0, 0, 2, 3, 3, 3, 3, 3 },
        { 0, 1, 2, 3, 4, 4, 4, 4 },
        { 0, 1, 2, 3, 4, 5, 4, 5 },
        { 0, 1, 2, 3, 4, 4, 6, 6 },
        { 0, 1, 2, 3, 4, 5, 6, 7 },
};

#define CMP_BODY(LHS, RHS) \
        switch (op) { \
        case 0: r = (LHS) >  (RHS); break; \
        case 1: r = (LHS) <  (RHS); break; \
        case 2: r = (LHS) >= (RHS); break; \
        case 3: r = (LHS) <= (RHS); break; \
        case 4: r = (LHS) == (RHS); break; \
        default: r = (LHS) != (RHS); break; \
        }

BUILTIN_FUNCTION(accel_vadd)
{
        ASSERT_ARGC("vadd()", 5);

        void *a   = PTR_ARG(0);
        void *b   = PTR_ARG(1);
        void *out = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vaddD(a, 1, b, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vadd(a, 1, b, 1, out, 1, n);  return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict ap = a;
                const T *restrict bp = b;
                T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] + bp[i];
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vsub)
{
        ASSERT_ARGC("vsub()", 5);

        void *a   = PTR_ARG(0);
        void *b   = PTR_ARG(1);
        void *out = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vsubD(b, 1, a, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vsub(b, 1, a, 1, out, 1, n);  return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict ap = a;
                const T *restrict bp = b;
                T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] - bp[i];
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vmul)
{
        ASSERT_ARGC("vmul()", 5);

        void *a   = PTR_ARG(0);
        void *b   = PTR_ARG(1);
        void *out = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vmulD(a, 1, b, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vmul(a, 1, b, 1, out, 1, n);  return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict ap = a;
                const T *restrict bp = b;
                T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] * bp[i];
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vdiv)
{
        ASSERT_ARGC("vdiv()", 5);

        void *a   = PTR_ARG(0);
        void *b   = PTR_ARG(1);
        void *out = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vdivD(b, 1, a, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vdiv(b, 1, a, 1, out, 1, n);  return NIL; }
#endif
        if (DTYPE_IS_FLOAT(dt)) {
                DISPATCH_FLOAT(dt,
                        const T *restrict ap = a;
                        const T *restrict bp = b;
                        T *restrict cp = out;
                        for (i64 i = 0; i < n; ++i) {
                                cp[i] = ap[i] / bp[i];
                        }
                )
        } else {
                DISPATCH(dt,
                        const T *restrict ap = a;
                        const T *restrict bp = b;
                        T *restrict cp = out;
                        for (i64 i = 0; i < n; ++i) {
                                cp[i] = bp[i] != 0 ? ap[i] / bp[i] : 0;
                        }
                )
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_vsadd)
{
        ASSERT_ARGC("vsadd()", 5);

        void  *a   = PTR_ARG(0);
        double s   = FLOAT_ARG(1);
        void  *out = PTR_ARG(2);
        i64    n   = INT_ARG(3);
        i64    dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vsaddD(a, 1, &s, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { float sf = (float)s; vDSP_vsadd(a, 1, &sf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict ap = a; T *restrict cp = out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] + sv;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vsmul)
{
        ASSERT_ARGC("vsmul()", 5);

        void  *a   = PTR_ARG(0);
        double s   = FLOAT_ARG(1);
        void  *out = PTR_ARG(2);
        i64    n   = INT_ARG(3);
        i64    dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vsmulD(a, 1, &s, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { float sf = (float)s; vDSP_vsmul(a, 1, &sf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict ap = a; T *restrict cp = out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] * sv;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vsdiv)
{
        ASSERT_ARGC("vsdiv()", 5);

        void  *a   = PTR_ARG(0);
        double s   = FLOAT_ARG(1);
        void  *out = PTR_ARG(2);
        i64    n   = INT_ARG(3);
        i64    dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vsdivD(a, 1, &s, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { float sf = (float)s; vDSP_vsdiv(a, 1, &sf, out, 1, n); return NIL; }
#endif
        if (DTYPE_IS_INT(dt) && s == 0.0) {
                memset(out, 0, n * esz(dt));

                return NIL;
        }
        DISPATCH(dt,
                const T *restrict ap = a; T *restrict cp = out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] / sv;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_svdiv)
{
        ASSERT_ARGC("svdiv()", 5);

        double s   = FLOAT_ARG(0);
        void  *a   = PTR_ARG(1);
        void  *out = PTR_ARG(2);
        i64    n   = INT_ARG(3);
        i64    dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_svdivD(&s, a, 1, out, 1, n); return NIL; }
#endif
        if (DTYPE_IS_FLOAT(dt)) {
                DISPATCH_FLOAT(dt,
                        const T *restrict ap = a; T *restrict cp = out; T sv = (T)s;
                        for (i64 i = 0; i < n; ++i) {
                                cp[i] = sv / ap[i];
                        }
                )
        } else {
                DISPATCH(dt,
                        const T *restrict ap = a; T *restrict cp = out; T sv = (T)s;
                        for (i64 i = 0; i < n; ++i) {
                                cp[i] = ap[i] != 0 ? sv / ap[i] : 0;
                        }
                )
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_vneg)
{
        ASSERT_ARGC("vneg()", 4);

        void *a   = PTR_ARG(0);
        void *out = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);

        if (DTYPE_IS_UNSIGNED(dt)) {
                bP("unsigned dtype %d", (int)dt);
        }

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vnegD(a, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vneg(a, 1, out, 1, n);  return NIL; }
#endif
        DISPATCH_SIGNED(dt,
                const T *restrict ap = a; T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = -ap[i];
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vabs)
{
        ASSERT_ARGC("vabs()", 4);

        void *a   = PTR_ARG(0);
        void *out = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vabsD(a, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vabs(a, 1, out, 1, n);  return NIL; }
#endif
        if (DTYPE_IS_UNSIGNED(dt)) {
                memcpy(out, a, n * esz(dt));

                return NIL;
        }
        DISPATCH_SIGNED(dt,
                const T *restrict ap = a; T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = ap[i] < 0 ? -ap[i] : ap[i];
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vclip)
{
        ASSERT_ARGC("vclip()", 6);

        void  *a   = PTR_ARG(0);
        double lo  = FLOAT_ARG(1);
        double hi  = FLOAT_ARG(2);
        void  *out = PTR_ARG(3);
        i64    n   = INT_ARG(4);
        i64    dt  = INT_ARG(5);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vclipD(a, 1, &lo, &hi, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { float lf = (float)lo, hf = (float)hi; vDSP_vclip(a, 1, &lf, &hf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict ap = a; T *restrict cp = out;
                T tlo = (T)lo, thi = (T)hi;
                for (i64 i = 0; i < n; ++i) {
                        T v = ap[i];
                        cp[i] = v < tlo ? tlo : v > thi ? thi : v;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vfill)
{
        ASSERT_ARGC("vfill()", 4);

        double val = FLOAT_ARG(0);
        void  *out = PTR_ARG(1);
        i64    n   = INT_ARG(2);
        i64    dt  = INT_ARG(3);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vfillD(&val, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { float vf = (float)val; vDSP_vfill(&vf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                T *restrict cp = out; T tv = (T)val;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = tv;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vclr)
{
        ASSERT_ARGC("vclr()", 3);

        void *out = PTR_ARG(0);
        i64   n   = INT_ARG(1);
        i64   dt  = INT_ARG(2);

        memset(out, 0, n * esz(dt));

        return NIL;
}

BUILTIN_FUNCTION(accel_vramp)
{
        ASSERT_ARGC("vramp()", 5);

        double start = FLOAT_ARG(0);
        double step  = FLOAT_ARG(1);
        void  *out   = PTR_ARG(2);
        i64    n     = INT_ARG(3);
        i64    dt    = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vrampD(&start, &step, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { float sf = (float)start, stf = (float)step; vDSP_vramp(&sf, &stf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = (T)(start + i * step);
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vcopy)
{
        ASSERT_ARGC("vcopy()", 4);

        void *src = PTR_ARG(0);
        void *dst = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);

        memcpy(dst, src, n * esz(dt));

        return NIL;
}

BUILTIN_FUNCTION(accel_vcast)
{
        ASSERT_ARGC("vcast()", 5);

        void *src = PTR_ARG(0);
        void *dst = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64  sdt  = INT_ARG(3);
        i64  ddt  = INT_ARG(4);

        if (sdt == ddt) {
                memcpy(dst, src, n * esz(sdt));

                return NIL;
        }
        for (i64 i = 0; i < n; ++i) {
                setd(dst, i, getd(src, i, sdt), ddt);
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_vmath)
{
        ASSERT_ARGC("vmath()", 5);

        void *a   = PTR_ARG(0);
        void *out = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);
        i64   op  = INT_ARG(4);

        if (UNLIKELY(!DTYPE_IS_FLOAT(dt))) {
                bP("requires float dtype, got %d", (int)dt);
        }

        typedef double (*mathfn)(double);
        static const mathfn FNS[] = { exp, log, sqrt, sin, cos, tan, asin, acos, atan };

        if (UNLIKELY(op < 0 || op >= (i64)(sizeof FNS / sizeof FNS[0]))) {
                bP("invalid op %lld", (long long)op);
        }

#ifdef __APPLE__
        if (dt == DTYPE_F64) {
                int ni = (int)n;
                typedef void (*vvfn64)(double*, const double*, const int*);
                static const vvfn64 VV[] = { vvexp, vvlog, vvsqrt, vvsin, vvcos, vvtan, vvasin, vvacos, vvatan };
                VV[op](out, a, &ni);

                return NIL;
        }
        if (dt == DTYPE_F32) {
                int ni = (int)n;
                typedef void (*vvfn32)(float*, const float*, const int*);
                static const vvfn32 VV[] = { vvexpf, vvlogf, vvsqrtf, vvsinf, vvcosf, vvtanf, vvasinf, vvacosf, vvatanf };
                VV[op](out, a, &ni);

                return NIL;
        }
#endif
        DISPATCH_FLOAT(dt,
                const T *restrict ap = a; T *restrict cp = out;
                mathfn f = FNS[op];
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = (T)f((double)ap[i]);
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vpow)
{
        ASSERT_ARGC("vpow()", 5);

        void *bases = PTR_ARG(0);
        void *exps  = PTR_ARG(1);
        void *out   = PTR_ARG(2);
        i64   n     = INT_ARG(3);
        i64   dt    = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { int ni = (int)n; vvpow(out, exps, bases, &ni); return NIL; }
        if (dt == DTYPE_F32) { int ni = (int)n; vvpowf(out, exps, bases, &ni); return NIL; }
#endif
        DISPATCH_FLOAT(dt,
                const T *restrict bp = bases;
                const T *restrict ep = exps;
                T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = (T)pow((double)bp[i], (double)ep[i]);
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vspow)
{
        ASSERT_ARGC("vspow()", 5);

        void  *a   = PTR_ARG(0);
        double p   = FLOAT_ARG(1);
        void  *out = PTR_ARG(2);
        i64    n   = INT_ARG(3);
        i64    dt  = INT_ARG(4);

        if (p == 2.0) {
                DISPATCH_FLOAT(dt,
                        const T *restrict ap = a; T *restrict cp = out;
                        for (i64 i = 0; i < n; ++i) {
                                cp[i] = ap[i] * ap[i];
                        }
                )

                return NIL;
        }
        if (p == 0.5) {
#ifdef __APPLE__
                if (dt == DTYPE_F64) { int ni = (int)n; vvsqrt(out, a, &ni); return NIL; }
                if (dt == DTYPE_F32) { int ni = (int)n; vvsqrtf(out, a, &ni); return NIL; }
#endif
                DISPATCH_FLOAT(dt,
                        const T *restrict ap = a; T *restrict cp = out;
                        for (i64 i = 0; i < n; ++i) {
                                cp[i] = (T)sqrt((double)ap[i]);
                        }
                )

                return NIL;
        }

        DISPATCH_FLOAT(dt,
                const T *restrict ap = a; T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = (T)pow((double)ap[i], p);
                }
        )

        return NIL;
}

static double
signfn(double x)
{
        return x > 0 ? 1.0 : x < 0 ? -1.0 : 0.0;
}

BUILTIN_FUNCTION(accel_vroundfn)
{
        ASSERT_ARGC("vroundfn()", 5);

        void *a   = PTR_ARG(0);
        void *out = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);
        i64   op  = INT_ARG(4);

        typedef double (*rfn)(double);
        static const rfn FNS[] = { signfn, floor, ceil, round };

        if (UNLIKELY(op < 0 || op >= 4)) {
                bP("invalid op %lld", (long long)op);
        }

        DISPATCH_FLOAT(dt,
                const T *restrict ap = a; T *restrict cp = out;
                rfn f = FNS[op];
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = (T)f((double)ap[i]);
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_sve)
{
        ASSERT_ARGC("sve()", 3);

        void *a  = PTR_ARG(0);
        i64   n  = INT_ARG(1);
        i64   dt = INT_ARG(2);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { double r; vDSP_sveD(a, 1, &r, n); return REAL(r); }
        if (dt == DTYPE_F32) { float r;  vDSP_sve(a, 1, &r, n);  return REAL(r); }
#endif
        double s = 0.0, c = 0.0;
        for (i64 i = 0; i < n; ++i) {
                double y = getd(a, i, dt) - c;
                double t = s + y;
                c = (t - s) - y;
                s = t;
        }

        return REAL(s);
}

BUILTIN_FUNCTION(accel_maxv)
{
        ASSERT_ARGC("maxv()", 3);

        void *a  = PTR_ARG(0);
        i64   n  = INT_ARG(1);
        i64   dt = INT_ARG(2);

        if (UNLIKELY(n <= 0)) {
                return REAL(-INFINITY);
        }

#ifdef __APPLE__
        if (dt == DTYPE_F64) { double r; vDSP_maxvD(a, 1, &r, n); return REAL(r); }
        if (dt == DTYPE_F32) { float r;  vDSP_maxv(a, 1, &r, n);  return REAL(r); }
#endif
        double m = getd(a, 0, dt);
        for (i64 i = 1; i < n; ++i) {
                double v = getd(a, i, dt);
                if (v > m) {
                        m = v;
                }
        }

        return REAL(m);
}

BUILTIN_FUNCTION(accel_minv)
{
        ASSERT_ARGC("minv()", 3);

        void *a  = PTR_ARG(0);
        i64   n  = INT_ARG(1);
        i64   dt = INT_ARG(2);

        if (UNLIKELY(n <= 0)) {
                return REAL(INFINITY);
        }

#ifdef __APPLE__
        if (dt == DTYPE_F64) { double r; vDSP_minvD(a, 1, &r, n); return REAL(r); }
        if (dt == DTYPE_F32) { float r;  vDSP_minv(a, 1, &r, n);  return REAL(r); }
#endif
        double m = getd(a, 0, dt);
        for (i64 i = 1; i < n; ++i) {
                double v = getd(a, i, dt);
                if (v < m) {
                        m = v;
                }
        }

        return REAL(m);
}

BUILTIN_FUNCTION(accel_count_nz)
{
        ASSERT_ARGC("countNz()", 3);

        void *a  = PTR_ARG(0);
        i64   n  = INT_ARG(1);
        i64   dt = INT_ARG(2);

        i64 count = 0;
        DISPATCH(dt,
                const T *restrict ap = a;
                for (i64 i = 0; i < n; ++i) {
                        count += (ap[i] != 0);
                }
        )

        return INTEGER(count);
}

BUILTIN_FUNCTION(accel_vcmp_scalar)
{
        ASSERT_ARGC("vcmpScalar()", 6);

        void  *a   = PTR_ARG(0);
        double s   = FLOAT_ARG(1);
        u8    *out = PTR_ARG(2);
        i64    n   = INT_ARG(3);
        i64    op  = INT_ARG(4);
        i64    dt  = INT_ARG(5);

        DISPATCH(dt,
                const T *restrict ap = a; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) {
                        u8 r; CMP_BODY(ap[i], sv)
                        out[i] = r;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vcmp_array)
{
        ASSERT_ARGC("vcmpArray()", 6);

        void *a   = PTR_ARG(0);
        void *b   = PTR_ARG(1);
        u8   *out = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   op  = INT_ARG(4);
        i64   dt  = INT_ARG(5);

        DISPATCH(dt,
                const T *restrict ap = a; const T *restrict bp = b;
                for (i64 i = 0; i < n; ++i) {
                        u8 r; CMP_BODY(ap[i], bp[i])
                        out[i] = r;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_bool_index)
{
        ASSERT_ARGC("boolIndex()", 5);

        void *src  = PTR_ARG(0);
        u8   *mask = PTR_ARG(1);
        void *out  = PTR_ARG(2);
        i64   n    = INT_ARG(3);
        i64   dt   = INT_ARG(4);

        i64 j = 0;
        DISPATCH(dt,
                const T *restrict sp = src; T *restrict op = out;
                for (i64 i = 0; i < n; ++i) {
                        if (mask[i]) {
                                op[j++] = sp[i];
                        }
                }
        )

        return INTEGER(j);
}

BUILTIN_FUNCTION(accel_bool_assign)
{
        ASSERT_ARGC("boolAssign()", 5);

        void  *dst  = PTR_ARG(0);
        u8    *mask = PTR_ARG(1);
        double val  = FLOAT_ARG(2);
        i64    n    = INT_ARG(3);
        i64    dt   = INT_ARG(4);

        DISPATCH(dt,
                T *restrict dp = dst; T tv = (T)val;
                for (i64 i = 0; i < n; ++i) {
                        if (mask[i]) {
                                dp[i] = tv;
                        }
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vmul_mask)
{
        ASSERT_ARGC("vmulMask()", 5);

        void *a    = PTR_ARG(0);
        u8   *mask = PTR_ARG(1);
        void *out  = PTR_ARG(2);
        i64   n    = INT_ARG(3);
        i64   dt   = INT_ARG(4);

        DISPATCH(dt,
                const T *restrict ap = a; T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = mask[i] ? ap[i] : 0;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vselect)
{
        ASSERT_ARGC("vselect()", 6);

        u8   *cond = PTR_ARG(0);
        void *x    = PTR_ARG(1);
        void *y    = PTR_ARG(2);
        void *out  = PTR_ARG(3);
        i64   n    = INT_ARG(4);
        i64   dt   = INT_ARG(5);

        DISPATCH(dt,
                const T *restrict xp = x; const T *restrict yp = y; T *restrict op = out;
                for (i64 i = 0; i < n; ++i) {
                        op[i] = cond[i] ? xp[i] : yp[i];
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vcumsum)
{
        ASSERT_ARGC("vcumsum()", 4);

        void *a   = PTR_ARG(0);
        void *out = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);

        DISPATCH(dt,
                const T *restrict ap = a; T *restrict cp = out;
                T s = 0;
                for (i64 i = 0; i < n; ++i) {
                        s += ap[i];
                        cp[i] = s;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vrandn)
{
        ASSERT_ARGC("vrandn()", 4);

        void  *out   = PTR_ARG(0);
        i64    n     = INT_ARG(1);
        double scale = FLOAT_ARG(2);
        i64    dt    = INT_ARG(3);

        static const double TAU = 6.283185307179586;

        DISPATCH_FLOAT(dt,
                T *restrict cp = out;
                for (i64 i = 0; i + 1 < n; i += 2) {
                        double u1 = TyRandom(ty) + 1e-15;
                        double u2 = TyRandom(ty);
                        double r  = scale * sqrt(-2.0 * log(u1));
                        cp[i]     = (T)(r * cos(TAU * u2));
                        cp[i + 1] = (T)(r * sin(TAU * u2));
                }
                if (n & 1) {
                        double u1 = TyRandom(ty) + 1e-15;
                        double u2 = TyRandom(ty);
                        cp[n - 1] = (T)(scale * sqrt(-2.0 * log(u1)) * cos(TAU * u2));
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vrand)
{
        ASSERT_ARGC("vrand()", 3);

        void *out = PTR_ARG(0);
        i64   n   = INT_ARG(1);
        i64   dt  = INT_ARG(2);

        DISPATCH_FLOAT(dt,
                T *restrict cp = out;
                for (i64 i = 0; i < n; ++i) {
                        cp[i] = (T)TyRandom(ty);
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_mtrans)
{
        ASSERT_ARGC("mtrans()", 5);

        void *src = PTR_ARG(0);
        void *dst = PTR_ARG(1);
        i64   m   = INT_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_mtransD(src, 1, dst, 1, n, m); return NIL; }
        if (dt == DTYPE_F32) { vDSP_mtrans(src, 1, dst, 1, n, m);  return NIL; }
#endif
        DISPATCH(dt,
                const T *restrict sp = src; T *restrict dp = dst;
                for (i64 i = 0; i < m; ++i) {
                        for (i64 j = 0; j < n; ++j) {
                                dp[j * m + i] = sp[i * n + j];
                        }
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_transpose_nd)
{
        ASSERT_ARGC("transposeNd()", 5);

        void *src   = PTR_ARG(0);
        void *dst   = PTR_ARG(1);
        i64  *shape = PTR_ARG(2);
        i64   ndim  = INT_ARG(3);
        i64   esize = INT_ARG(4);

        if (UNLIKELY(ndim <= 0 || ndim > MAX_NDIM)) {
                bP("ndim %lld out of range [1, %d]", (long long)ndim, MAX_NDIM);
        }

        i64 src_strides[MAX_NDIM], out_strides[MAX_NDIM];
        i64 total = 1;
        for (i64 d = ndim - 1; d >= 0; d--) {
                src_strides[d] = total;
                total *= shape[d];
        }
        out_strides[ndim - 1] = 1;
        for (i64 d = ndim - 2; d >= 0; d--) {
                out_strides[d] = out_strides[d + 1] * shape[ndim - 2 - d];
        }

        char *restrict dp = dst;
        const char *restrict sp = src;

        for (i64 k = 0; k < total; k++) {
                i64 si = 0, rem = k;
                for (i64 d = 0; d < ndim; d++) {
                        i64 idx = rem / out_strides[d];
                        rem %= out_strides[d];
                        si += idx * src_strides[ndim - 1 - d];
                }
                memcpy(dp + k * esize, sp + si * esize, esize);
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_broadcast_binop)
{
        ASSERT_ARGC("broadcastBinop()", 10);

        void *a     = PTR_ARG(0);
        void *b     = PTR_ARG(1);
        void *out   = PTR_ARG(2);
        i64  *a_str = PTR_ARG(3);
        i64  *b_str = PTR_ARG(4);
        i64  *o_shp = PTR_ARG(5);
        i64   ndim  = INT_ARG(6);
        i64   total = INT_ARG(7);
        i64   op    = INT_ARG(8);
        i64   dt    = INT_ARG(9);

        if (UNLIKELY(ndim > MAX_NDIM)) {
                bP("ndim %lld exceeds limit %d", (long long)ndim, MAX_NDIM);
        }

        int a_contig = 1, b_contig = 1, b_scalar = 1;
        {
                i64 a_expected = 1, b_expected = 1;
                for (i64 d = ndim - 1; d >= 0; d--) {
                        if (a_str[d] != a_expected) { a_contig = 0; }
                        if (b_str[d] != b_expected) { b_contig = 0; }
                        if (b_str[d] != 0)          { b_scalar = 0; }
                        a_expected *= o_shp[d];
                        b_expected *= o_shp[d];
                }
        }

        if (a_contig && b_contig) {
                DISPATCH(dt,
                        const T *restrict ap = a;
                        const T *restrict bp = b;
                        T *restrict cp = out;
                        switch (op) {
                        case 0:
                                for (i64 k = 0; k < total; k++) { cp[k] = ap[k] + bp[k]; }
                                break;
                        case 1:
                                for (i64 k = 0; k < total; k++) { cp[k] = ap[k] - bp[k]; }
                                break;
                        case 2:
                                for (i64 k = 0; k < total; k++) { cp[k] = ap[k] * bp[k]; }
                                break;
                        case 3:
                                if (DTYPE_IS_FLOAT(dt)) {
                                        for (i64 k = 0; k < total; k++) { cp[k] = ap[k] / bp[k]; }
                                } else {
                                        for (i64 k = 0; k < total; k++) { cp[k] = bp[k] != 0 ? ap[k] / bp[k] : 0; }
                                }
                                break;
                        case 4:
                                for (i64 k = 0; k < total; k++) { cp[k] = (T)pow((double)ap[k], (double)bp[k]); }
                                break;
                        }
                )

                return NIL;
        }

        if (a_contig && b_scalar) {
                DISPATCH(dt,
                        const T *restrict ap = a;
                        T bv = *(const T *)b;
                        T *restrict cp = out;
                        switch (op) {
                        case 0:
                                for (i64 k = 0; k < total; k++) { cp[k] = ap[k] + bv; }
                                break;
                        case 1:
                                for (i64 k = 0; k < total; k++) { cp[k] = ap[k] - bv; }
                                break;
                        case 2:
                                for (i64 k = 0; k < total; k++) { cp[k] = ap[k] * bv; }
                                break;
                        case 3:
                                if (DTYPE_IS_INT(dt) && bv == 0) {
                                        memset(out, 0, total * esz(dt));
                                } else {
                                        for (i64 k = 0; k < total; k++) { cp[k] = ap[k] / bv; }
                                }
                                break;
                        case 4:
                                for (i64 k = 0; k < total; k++) { cp[k] = (T)pow((double)ap[k], (double)bv); }
                                break;
                        }
                )

                return NIL;
        }

        DISPATCH(dt,
                const T *restrict ap = a;
                const T *restrict bp = b;
                T *restrict cp = out;
                for (i64 k = 0; k < total; k++) {
                        i64 ai = 0, bi = 0, rem = k;
                        for (i64 d = ndim - 1; d >= 0; d--) {
                                i64 idx = rem % o_shp[d];
                                rem /= o_shp[d];
                                ai += idx * a_str[d];
                                bi += idx * b_str[d];
                        }
                        T va = ap[ai], vb = bp[bi];
                        switch (op) {
                        case 0: cp[k] = va + vb; break;
                        case 1: cp[k] = va - vb; break;
                        case 2: cp[k] = va * vb; break;
                        case 3: cp[k] = (DTYPE_IS_INT(dt) && vb == 0) ? 0 : va / vb; break;
                        case 4: cp[k] = (T)pow((double)va, (double)vb); break;
                        }
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_sum_axis0)
{
        ASSERT_ARGC("sumAxis0()", 5);

        void *src  = PTR_ARG(0);
        void *dst  = PTR_ARG(1);
        i64   rows = INT_ARG(2);
        i64   cols = INT_ARG(3);
        i64   dt   = INT_ARG(4);

        memset(dst, 0, cols * esz(dt));

#ifdef __APPLE__
        if (dt == DTYPE_F64) {
                double *sp = src, *dp = dst;
                for (i64 i = 0; i < rows; ++i) {
                        vDSP_vaddD(dp, 1, sp + i * cols, 1, dp, 1, cols);
                }

                return NIL;
        }
        if (dt == DTYPE_F32) {
                float *sp = src, *dp = dst;
                for (i64 i = 0; i < rows; ++i) {
                        vDSP_vadd(dp, 1, sp + i * cols, 1, dp, 1, cols);
                }

                return NIL;
        }
#endif
        DISPATCH(dt,
                const T *restrict sp = src; T *restrict dp = dst;
                for (i64 i = 0; i < rows; ++i) {
                        for (i64 j = 0; j < cols; ++j) {
                                dp[j] += sp[i * cols + j];
                        }
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_add_row)
{
        ASSERT_ARGC("addRow()", 5);

        void *data = PTR_ARG(0);
        void *row  = PTR_ARG(1);
        i64   rows = INT_ARG(2);
        i64   cols = INT_ARG(3);
        i64   dt   = INT_ARG(4);

#ifdef __APPLE__
        if (dt == DTYPE_F64) {
                double *dp = data, *rp = row;
                for (i64 i = 0; i < rows; ++i) {
                        vDSP_vaddD(dp + i * cols, 1, rp, 1, dp + i * cols, 1, cols);
                }

                return NIL;
        }
        if (dt == DTYPE_F32) {
                float *dp = data, *rp = row;
                for (i64 i = 0; i < rows; ++i) {
                        vDSP_vadd(dp + i * cols, 1, rp, 1, dp + i * cols, 1, cols);
                }

                return NIL;
        }
#endif
        DISPATCH(dt,
                T *restrict dp = data; const T *restrict rp = row;
                for (i64 i = 0; i < rows; ++i) {
                        for (i64 j = 0; j < cols; ++j) {
                                dp[i * cols + j] += rp[j];
                        }
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_vget)
{
        ASSERT_ARGC("vget()", 3);

        void *p  = PTR_ARG(0);
        i64   i  = INT_ARG(1);
        i64   dt = INT_ARG(2);

        switch (dt) {
        case DTYPE_F64:  return REAL(((double *)p)[i]);
        case DTYPE_F32:  return REAL(((float *)p)[i]);
        case DTYPE_I64:  return INTEGER(((i64 *)p)[i]);
        case DTYPE_I32:  return INTEGER(((i32 *)p)[i]);
        case DTYPE_I16:  return INTEGER(((i16 *)p)[i]);
        case DTYPE_I8:   return INTEGER(((i8 *)p)[i]);
        case DTYPE_U8:   return INTEGER(((u8 *)p)[i]);
        case DTYPE_BOOL: return INTEGER(((u8 *)p)[i]);
        default:         return NIL;
        }
}

BUILTIN_FUNCTION(accel_vset)
{
        ASSERT_ARGC("vset()", 4);

        void *p  = PTR_ARG(0);
        i64   i  = INT_ARG(1);
        Value v  = ARG(2);
        i64   dt = INT_ARG(3);

        setd(p, i, valtod(v), dt);

        return NIL;
}

BUILTIN_FUNCTION(accel_from_list)
{
        ASSERT_ARGC("fromList()", 3);

        Array *arr = ARRAY_ARG(0);
        void  *dst = PTR_ARG(1);
        i64    dt  = INT_ARG(2);

        for (usize i = 0; i < arr->count; ++i) {
                setd(dst, i, valtod(arr->items[i]), dt);
        }

        return INTEGER(arr->count);
}

BUILTIN_FUNCTION(accel_from_list2d)
{
        ASSERT_ARGC("fromList2d()", 3);

        Array *arr = ARRAY_ARG(0);
        void  *dst = PTR_ARG(1);
        i64    dt  = INT_ARG(2);

        i64 rows = arr->count;
        if (rows == 0) {
                return INTEGER(0);
        }

        if (UNLIKELY(arr->items[0].type != VALUE_ARRAY)) {
                bP("expected array of arrays");
        }

        i64 cols = arr->items[0].array->count;
        for (i64 i = 0; i < rows; ++i) {
                if (UNLIKELY(arr->items[i].type != VALUE_ARRAY)) {
                        bP("row %lld is not an array", (long long)i);
                }
                Array *row = arr->items[i].array;
                if (UNLIKELY((i64)row->count != cols)) {
                        bP("jagged rows (row 0 has %lld cols, row %lld has %lld)",
                           (long long)cols, (long long)i, (long long)row->count);
                }
                for (i64 j = 0; j < cols; ++j) {
                        setd(dst, i * cols + j, valtod(row->items[j]), dt);
                }
        }

        return INTEGER(cols);
}

BUILTIN_FUNCTION(accel_to_list)
{
        ASSERT_ARGC("toList()", 3);

        void *src = PTR_ARG(0);
        i64   n   = INT_ARG(1);
        i64   dt  = INT_ARG(2);

        Array *arr = vAn(n);
        if (DTYPE_IS_FLOAT(dt)) {
                for (i64 i = 0; i < n; ++i) {
                        arr->items[i] = REAL(getd(src, i, dt));
                }
        } else {
                for (i64 i = 0; i < n; ++i) {
                        arr->items[i] = INTEGER((i64)getd(src, i, dt));
                }
        }
        arr->count = n;

        return ARRAY(arr);
}

BUILTIN_FUNCTION(accel_from_bytes)
{
        ASSERT_ARGC("fromBytes()", 5);

        Value v = ARG(0);
        unsigned char *src;
        if (v.type == VALUE_PTR) {
                src = v.ptr;
        } else if (v.type == VALUE_BLOB) {
                src = v.blob->items;
        } else {
                bP("arg[0] must be Blob or Ptr");
        }

        i64   off = INT_ARG(1);
        void *dst = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

        const unsigned char *p = src + off;

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vfltu8D(p, 1, dst, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vfltu8(p, 1, dst, 1, n);  return NIL; }
#endif
        for (i64 i = 0; i < n; ++i) {
                setd(dst, i, (double)p[i], dt);
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_one_hot)
{
        ASSERT_ARGC("oneHot()", 5);

        void *labels = PTR_ARG(0);
        void *out    = PTR_ARG(1);
        i64   n      = INT_ARG(2);
        i64   k      = INT_ARG(3);
        i64   dt     = INT_ARG(4);

        memset(out, 0, n * k * esz(dt));
        for (i64 i = 0; i < n; ++i) {
                i64 c = (i64)getd(labels, i, dt);
                if (UNLIKELY(c < 0 || c >= k)) {
                        bP("label %lld out of range [0, %lld) at index %lld",
                           (long long)c, (long long)k, (long long)i);
                }
                setd(out, i * k + c, 1.0, dt);
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_argmax_axis1)
{
        ASSERT_ARGC("argmaxAxis1()", 5);

        void *data = PTR_ARG(0);
        i64  *out  = PTR_ARG(1);
        i64   m    = INT_ARG(2);
        i64   n    = INT_ARG(3);
        i64   dt   = INT_ARG(4);

        DISPATCH(dt,
                const T *restrict dp = data;
                for (i64 i = 0; i < m; ++i) {
                        const T *restrict row = dp + i * n;
                        i64 best = 0; T bv = row[0];
                        for (i64 j = 1; j < n; ++j) {
                                if (row[j] > bv) {
                                        bv = row[j];
                                        best = j;
                                }
                        }
                        out[i] = best;
                }
        )

        return NIL;
}

BUILTIN_FUNCTION(accel_softmax)
{
        ASSERT_ARGC("softmax()", 4);

        void *src = PTR_ARG(0);
        void *dst = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   k   = INT_ARG(3);

        double *restrict sp = src;
        double *restrict dp = dst;
        for (i64 i = 0; i < n; ++i) {
                const double *restrict row = sp + i * k;
                double *restrict orow = dp + i * k;

                double mx = row[0];
                for (i64 j = 1; j < k; ++j) {
                        if (row[j] > mx) {
                                mx = row[j];
                        }
                }

                double s = 0.0;
                for (i64 j = 0; j < k; ++j) {
                        double e = exp(row[j] - mx);
                        orow[j] = e;
                        s += e;
                }

                double inv = 1.0 / s;
                for (i64 j = 0; j < k; ++j) {
                        orow[j] *= inv;
                }
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_cross_entropy)
{
        ASSERT_ARGC("crossEntropy()", 3);

        double *restrict probs   = PTR_ARG(0);
        double *restrict targets = PTR_ARG(1);
        i64     total            = INT_ARG(2);

        double loss = 0.0;
        for (i64 i = 0; i < total; ++i) {
                if (targets[i] > 0.0) {
                        double p = probs[i];
                        loss -= targets[i] * log(p > 1e-15 ? p : 1e-15);
                }
        }

        return REAL(loss);
}

BUILTIN_FUNCTION(accel_accuracy)
{
        ASSERT_ARGC("accuracy()", 5);

        i64  *preds  = PTR_ARG(0);
        void *labels = PTR_ARG(1);
        i64   n      = INT_ARG(2);
        i64   ldt    = INT_ARG(3);
        imax  k      = INT_ARG(4);

        if (UNLIKELY(n <= 0)) {
                return REAL(0.0);
        }

        i64 correct = 0;
        for (i64 i = 0; i < n; ++i) {
                if (UNLIKELY(preds[i] < 0 || preds[i] >= k)) {
                        bP(
                                "prediction %"PRIiMAX" out of range "
                                "[0, %"PRIiMAX") at index %"PRIi64,
                                (imax)preds[i], k, i
                        );
                }
                correct += (preds[i] == (i64)getd(labels, i, ldt));
        }

        return REAL((double)correct / n);
}

BUILTIN_FUNCTION(accel_vtrace)
{
        ASSERT_ARGC("vtrace()", 4);

        void *data = PTR_ARG(0);
        i64   m    = INT_ARG(1);
        i64   n    = INT_ARG(2);
        i64   dt   = INT_ARG(3);

        i64 mn = m < n ? m : n;
        double s = 0.0;
        for (i64 i = 0; i < mn; ++i) {
                s += getd(data, i * n + i, dt);
        }

        return REAL(s);
}

BUILTIN_FUNCTION(accel_array_eq)
{
        ASSERT_ARGC("arrayEq()", 4);

        void *a  = PTR_ARG(0);
        void *b  = PTR_ARG(1);
        i64   n  = INT_ARG(2);
        i64   dt = INT_ARG(3);

        if (memcmp(a, b, n * esz(dt)) == 0) {
                return INTEGER(1);
        }

        if (DTYPE_IS_FLOAT(dt)) {
                DISPATCH_FLOAT(dt,
                        const T *restrict ap = a; const T *restrict bp = b;
                        for (i64 i = 0; i < n; ++i) {
                                if (ap[i] != bp[i]) {
                                        return INTEGER(0);
                                }
                        }
                )

                return INTEGER(1);
        }

        return INTEGER(0);
}

BUILTIN_FUNCTION(accel_promote)
{
        ASSERT_ARGC("promote()", 2);

        i64 a = INT_ARG(0);
        i64 b = INT_ARG(1);

        return INTEGER(PROMOTE[a & 7][b & 7]);
}
