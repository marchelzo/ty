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
};

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
        }

static inline int
esz(int dt)
{
        static const int sizes[] = { 8, 4, 8, 4, 2, 1, 1, 1 };
        return sizes[dt & 7];
}

static inline double
getd(void *p, i64 i, int dt)
{
        switch (dt) {
        case DTYPE_F64:  return ((double *)p)[i];
        case DTYPE_F32:  return ((float *)p)[i];
        case DTYPE_I64:  return (double)((i64 *)p)[i];
        case DTYPE_I32:  return ((i32 *)p)[i];
        case DTYPE_I16:  return ((i16 *)p)[i];
        case DTYPE_I8:   return ((i8 *)p)[i];
        case DTYPE_U8:   return ((u8 *)p)[i];
        case DTYPE_BOOL: return ((u8 *)p)[i];
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
                T *ap = (T*)a; T *bp = (T*)b; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] + bp[i];
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
                T *ap = (T*)a; T *bp = (T*)b; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] - bp[i];
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
                T *ap = (T*)a; T *bp = (T*)b; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] * bp[i];
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
#endif
        DISPATCH(dt,
                T *ap = (T*)a; T *bp = (T*)b; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] / bp[i];
        )
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
                T *ap = (T*)a; T *cp = (T*)out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] + sv;
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
                T *ap = (T*)a; T *cp = (T*)out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] * sv;
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
#endif
        DISPATCH(dt,
                T *ap = (T*)a; T *cp = (T*)out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] / sv;
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
        DISPATCH(dt,
                T *ap = (T*)a; T *cp = (T*)out; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) cp[i] = sv / ap[i];
        )
        return NIL;
}

BUILTIN_FUNCTION(accel_vneg)
{
        ASSERT_ARGC("vneg()", 4);
        void *a   = PTR_ARG(0);
        void *out = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   dt  = INT_ARG(3);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vnegD(a, 1, out, 1, n); return NIL; }
        if (dt == DTYPE_F32) { vDSP_vneg(a, 1, out, 1, n);  return NIL; }
#endif
        DISPATCH(dt,
                T *ap = (T*)a; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = -ap[i];
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
        DISPATCH(dt,
                T *ap = (T*)a; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = ap[i] < 0 ? -ap[i] : ap[i];
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
        if (dt == DTYPE_F32) { float lf = (float)lo; float hf = (float)hi; vDSP_vclip(a, 1, &lf, &hf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                T *ap = (T*)a; T *cp = (T*)out; T tlo = (T)lo; T thi = (T)hi;
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
                T *cp = (T*)out; T tv = (T)val;
                for (i64 i = 0; i < n; ++i) cp[i] = tv;
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
        if (dt == DTYPE_F32) { float sf = (float)start; float stf = (float)step; vDSP_vramp(&sf, &stf, out, 1, n); return NIL; }
#endif
        DISPATCH(dt,
                T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = (T)(start + i * step);
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

        for (i64 i = 0; i < n; ++i)
                setd(dst, i, getd(src, i, sdt), ddt);
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

        typedef double (*mathfn)(double);
        static const mathfn FNS[] = { exp, log, sqrt, sin, cos, tan, asin, acos, atan };

#ifdef __APPLE__
        if (dt == DTYPE_F64 && op < 9) {
                int ni = (int)n;
                typedef void (*vvfn64)(double*, const double*, const int*);
                static const vvfn64 VV[] = { vvexp, vvlog, vvsqrt, vvsin, vvcos, vvtan, vvasin, vvacos, vvatan };
                VV[op](out, a, &ni);
                return NIL;
        }
        if (dt == DTYPE_F32 && op < 9) {
                int ni = (int)n;
                typedef void (*vvfn32)(float*, const float*, const int*);
                static const vvfn32 VV[] = { vvexpf, vvlogf, vvsqrtf, vvsinf, vvcosf, vvtanf, vvasinf, vvacosf, vvatanf };
                VV[op](out, a, &ni);
                return NIL;
        }
#endif
        DISPATCH_FLOAT(dt,
                T *ap = (T*)a; T *cp = (T*)out;
                mathfn f = FNS[op];
                for (i64 i = 0; i < n; ++i) cp[i] = (T)f((double)ap[i]);
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
#endif
        DISPATCH_FLOAT(dt,
                T *bp = (T*)bases; T *ep = (T*)exps; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = (T)pow((double)bp[i], (double)ep[i]);
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

        DISPATCH_FLOAT(dt,
                T *ap = (T*)a; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = (T)pow((double)ap[i], p);
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

        DISPATCH_FLOAT(dt,
                T *ap = (T*)a; T *cp = (T*)out;
                rfn f = FNS[op];
                for (i64 i = 0; i < n; ++i) cp[i] = (T)f((double)ap[i]);
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
        double s = 0.0;
        for (i64 i = 0; i < n; ++i) s += getd(a, i, dt);
        return REAL(s);
}

BUILTIN_FUNCTION(accel_maxv)
{
        ASSERT_ARGC("maxv()", 3);
        void *a  = PTR_ARG(0);
        i64   n  = INT_ARG(1);
        i64   dt = INT_ARG(2);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { double r; vDSP_maxvD(a, 1, &r, n); return REAL(r); }
        if (dt == DTYPE_F32) { float r;  vDSP_maxv(a, 1, &r, n);  return REAL(r); }
#endif
        double m = getd(a, 0, dt);
        for (i64 i = 1; i < n; ++i) {
                double v = getd(a, i, dt);
                if (v > m) m = v;
        }
        return REAL(m);
}

BUILTIN_FUNCTION(accel_minv)
{
        ASSERT_ARGC("minv()", 3);
        void *a  = PTR_ARG(0);
        i64   n  = INT_ARG(1);
        i64   dt = INT_ARG(2);

#ifdef __APPLE__
        if (dt == DTYPE_F64) { double r; vDSP_minvD(a, 1, &r, n); return REAL(r); }
        if (dt == DTYPE_F32) { float r;  vDSP_minv(a, 1, &r, n);  return REAL(r); }
#endif
        double m = getd(a, 0, dt);
        for (i64 i = 1; i < n; ++i) {
                double v = getd(a, i, dt);
                if (v < m) m = v;
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
                T *ap = (T*)a;
                for (i64 i = 0; i < n; ++i) if (ap[i] != 0) ++count;
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
                T *ap = (T*)a; T sv = (T)s;
                for (i64 i = 0; i < n; ++i) {
                        u8 r;
                        switch (op) {
                        case 0: r = ap[i] >  sv; break;
                        case 1: r = ap[i] <  sv; break;
                        case 2: r = ap[i] >= sv; break;
                        case 3: r = ap[i] <= sv; break;
                        case 4: r = ap[i] == sv; break;
                        default: r = ap[i] != sv; break;
                        }
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
                T *ap = (T*)a; T *bp = (T*)b;
                for (i64 i = 0; i < n; ++i) {
                        u8 r;
                        switch (op) {
                        case 0: r = ap[i] >  bp[i]; break;
                        case 1: r = ap[i] <  bp[i]; break;
                        case 2: r = ap[i] >= bp[i]; break;
                        case 3: r = ap[i] <= bp[i]; break;
                        case 4: r = ap[i] == bp[i]; break;
                        default: r = ap[i] != bp[i]; break;
                        }
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
                T *sp = (T*)src; T *op = (T*)out;
                for (i64 i = 0; i < n; ++i) if (mask[i]) op[j++] = sp[i];
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
                T *dp = (T*)dst; T tv = (T)val;
                for (i64 i = 0; i < n; ++i) if (mask[i]) dp[i] = tv;
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
                T *ap = (T*)a; T *cp = (T*)out;
                T s = 0;
                for (i64 i = 0; i < n; ++i) { s += ap[i]; cp[i] = s; }
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
                T *cp = (T*)out;
                for (i64 i = 0; i + 1 < n; i += 2) {
                        double u1 = drand48() + 1e-15;
                        double u2 = drand48();
                        double r  = scale * sqrt(-2.0 * log(u1));
                        cp[i]     = (T)(r * cos(TAU * u2));
                        cp[i + 1] = (T)(r * sin(TAU * u2));
                }
                if (n % 2 == 1) {
                        double u1 = drand48() + 1e-15;
                        double u2 = drand48();
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
                T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = (T)drand48();
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
#endif
        DISPATCH(dt,
                T *sp = (T*)src; T *dp = (T*)dst;
                for (i64 i = 0; i < m; ++i)
                        for (i64 j = 0; j < n; ++j)
                                dp[j * m + i] = sp[i * n + j];
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

        i64 src_strides[32]; i64 out_strides[32]; i64 total = 1;
        for (i64 d = ndim - 1; d >= 0; d--) { src_strides[d] = total; total *= shape[d]; }
        out_strides[ndim - 1] = 1;
        for (i64 d = ndim - 2; d >= 0; d--) out_strides[d] = out_strides[d + 1] * shape[ndim - 2 - d];

        for (i64 k = 0; k < total; k++) {
                i64 si = 0; i64 rem = k;
                for (i64 d = 0; d < ndim; d++) {
                        i64 idx = rem / out_strides[d];
                        rem %= out_strides[d];
                        si += idx * src_strides[ndim - 1 - d];
                }
                memcpy((char *)dst + k * esize, (char *)src + si * esize, esize);
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

        DISPATCH(dt,
                T *ap = (T*)a; T *bp = (T*)b; T *cp = (T*)out;
                for (i64 k = 0; k < total; k++) {
                        i64 ai = 0; i64 bi = 0; i64 rem = k;
                        for (i64 d = ndim - 1; d >= 0; d--) {
                                i64 idx = rem % o_shp[d];
                                rem /= o_shp[d];
                                ai += idx * a_str[d];
                                bi += idx * b_str[d];
                        }
                        T va = ap[ai]; T vb = bp[bi];
                        switch (op) {
                        case 0: cp[k] = va + vb; break;
                        case 1: cp[k] = va - vb; break;
                        case 2: cp[k] = va * vb; break;
                        case 3: cp[k] = vb != 0 ? va / vb : 0; break;
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
        DISPATCH(dt,
                T *sp = (T*)src; T *dp = (T*)dst;
                for (i64 i = 0; i < rows; ++i)
                        for (i64 j = 0; j < cols; ++j)
                                dp[j] += sp[i * cols + j];
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

        double d = (v.type == VALUE_REAL) ? v.real : (double)v.z;
        setd(p, i, d, dt);
        return NIL;
}

BUILTIN_FUNCTION(accel_from_list)
{
        ASSERT_ARGC("fromList()", 3);
        Array *arr = ARRAY_ARG(0);
        void  *dst = PTR_ARG(1);
        i64    dt  = INT_ARG(2);

        for (usize i = 0; i < arr->count; ++i) {
                Value v = arr->items[i];
                double d = (v.type == VALUE_REAL) ? v.real : (double)v.z;
                setd(dst, i, d, dt);
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
        if (rows == 0) return INTEGER(0);

        i64 cols = arr->items[0].array->count;
        for (i64 i = 0; i < rows; ++i) {
                Array *row = arr->items[i].array;
                if ((i64)row->count != cols) zP("array: jagged rows");
                for (i64 j = 0; j < cols; ++j) {
                        Value v = row->items[j];
                        double d = (v.type == VALUE_REAL) ? v.real : (double)v.z;
                        setd(dst, i * cols + j, d, dt);
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
        for (i64 i = 0; i < n; ++i) {
                if (dt <= DTYPE_F32)
                        arr->items[i] = REAL(getd(src, i, dt));
                else
                        arr->items[i] = INTEGER((i64)getd(src, i, dt));
        }
        arr->count = n;
        return ARRAY(arr);
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
                T *xp = (T*)x; T *yp = (T*)y; T *op = (T*)out;
                for (i64 i = 0; i < n; ++i) op[i] = cond[i] ? xp[i] : yp[i];
        )
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
                T *dp = (T*)data;
                for (i64 i = 0; i < m; ++i) {
                        i64 best = 0; T bv = dp[i * n];
                        for (i64 j = 1; j < n; ++j)
                                if (dp[i * n + j] > bv) { bv = dp[i * n + j]; best = j; }
                        out[i] = best;
                }
        )
        return NIL;
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
        for (i64 i = 0; i < mn; ++i) s += getd(data, i * n + i, dt);
        return REAL(s);
}

BUILTIN_FUNCTION(accel_array_eq)
{
        ASSERT_ARGC("arrayEq()", 4);
        void *a  = PTR_ARG(0);
        void *b  = PTR_ARG(1);
        i64   n  = INT_ARG(2);
        i64   dt = INT_ARG(3);

        DISPATCH(dt,
                T *ap = (T*)a; T *bp = (T*)b;
                for (i64 i = 0; i < n; ++i)
                        if (ap[i] != bp[i]) return INTEGER(0);
        )
        return INTEGER(1);
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
                T *ap = (T*)a; T *cp = (T*)out;
                for (i64 i = 0; i < n; ++i) cp[i] = mask[i] ? ap[i] : 0;
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
                double *dp = data; double *rp = row;
                for (i64 i = 0; i < rows; ++i) vDSP_vaddD(dp + i * cols, 1, rp, 1, dp + i * cols, 1, cols);
                return NIL;
        }
        if (dt == DTYPE_F32) {
                float *dp = data; float *rp = row;
                for (i64 i = 0; i < rows; ++i) vDSP_vadd(dp + i * cols, 1, rp, 1, dp + i * cols, 1, cols);
                return NIL;
        }
#endif
        DISPATCH(dt,
                T *dp = (T*)data; T *rp = (T*)row;
                for (i64 i = 0; i < rows; ++i)
                        for (i64 j = 0; j < cols; ++j)
                                dp[i * cols + j] += rp[j];
        )
        return NIL;
}

BUILTIN_FUNCTION(accel_from_bytes)
{
        ASSERT_ARGC("fromBytes()", 5);
        Value v = ARG(0);
        unsigned char *src;
        if (v.type == VALUE_PTR)      src = v.ptr;
        else if (v.type == VALUE_BLOB) src = v.blob->items;
        else zP("fromBytes(): arg[0] must be Blob or Ptr");

        i64   off = INT_ARG(1);
        void *dst = PTR_ARG(2);
        i64   n   = INT_ARG(3);
        i64   dt  = INT_ARG(4);

        unsigned char const *p = src + off;

#ifdef __APPLE__
        if (dt == DTYPE_F64) { vDSP_vfltu8D(p, 1, dst, 1, n); return NIL; }
#endif
        for (i64 i = 0; i < n; ++i)
                setd(dst, i, (double)p[i], dt);
        return NIL;
}

BUILTIN_FUNCTION(accel_softmax)
{
        ASSERT_ARGC("softmax()", 4);
        void *src = PTR_ARG(0);
        void *dst = PTR_ARG(1);
        i64   n   = INT_ARG(2);
        i64   k   = INT_ARG(3);

        double *sp = src; double *dp = dst;
        for (i64 i = 0; i < n; ++i) {
                double mx = sp[i * k];
                for (i64 j = 1; j < k; ++j)
                        if (sp[i * k + j] > mx) mx = sp[i * k + j];
                double s = 0.0;
                for (i64 j = 0; j < k; ++j) {
                        double e = exp(sp[i * k + j] - mx);
                        dp[i * k + j] = e;
                        s += e;
                }
                double inv = 1.0 / s;
                for (i64 j = 0; j < k; ++j) dp[i * k + j] *= inv;
        }
        return NIL;
}

BUILTIN_FUNCTION(accel_cross_entropy)
{
        ASSERT_ARGC("crossEntropy()", 3);
        double *probs   = PTR_ARG(0);
        double *targets = PTR_ARG(1);
        i64     total   = INT_ARG(2);

        double loss = 0.0;
        for (i64 i = 0; i < total; ++i)
                if (targets[i] > 0.0) {
                        double p = probs[i];
                        loss -= targets[i] * log(p > 1e-15 ? p : 1e-15);
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
        i64   k      = INT_ARG(4);

        i64 correct = 0;
        for (i64 i = 0; i < n; ++i)
                if (preds[i] == (i64)getd(labels, i, ldt)) ++correct;
        return REAL((double)correct / n);
}

BUILTIN_FUNCTION(accel_promote)
{
        ASSERT_ARGC("promote()", 2);
        i64 a = INT_ARG(0);
        i64 b = INT_ARG(1);
        return INTEGER(PROMOTE[a & 7][b & 7]);
}
