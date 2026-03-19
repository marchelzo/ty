#include <math.h>
#include <string.h>

#include "ty.h"
#include "value.h"
#include "vm.h"
#include "functions.h"

BUILTIN_FUNCTION(accel_vmul)
{
        ASSERT_ARGC("vmul()", 4);

        double *a = PTR_ARG(0);
        double *b = PTR_ARG(1);
        double *c = PTR_ARG(2);
        i64     n = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                c[i] = a[i] * b[i];

        return NIL;
}

BUILTIN_FUNCTION(accel_vdiv)
{
        ASSERT_ARGC("vdiv()", 4);

        double *a = PTR_ARG(0);
        double *b = PTR_ARG(1);
        double *c = PTR_ARG(2);
        i64     n = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                c[i] = a[i] / b[i];

        return NIL;
}

BUILTIN_FUNCTION(accel_vsadd)
{
        ASSERT_ARGC("vsadd()", 4);

        double *a   = PTR_ARG(0);
        double  s   = FLOAT_ARG(1);
        double *out = PTR_ARG(2);
        i64     n   = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                out[i] = a[i] + s;

        return NIL;
}

BUILTIN_FUNCTION(accel_vsmul)
{
        ASSERT_ARGC("vsmul()", 4);

        double *a   = PTR_ARG(0);
        double  s   = FLOAT_ARG(1);
        double *out = PTR_ARG(2);
        i64     n   = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                out[i] = a[i] * s;

        return NIL;
}

BUILTIN_FUNCTION(accel_vsdiv)
{
        ASSERT_ARGC("vsdiv()", 4);

        double *a   = PTR_ARG(0);
        double  s   = FLOAT_ARG(1);
        double *out = PTR_ARG(2);
        i64     n   = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                out[i] = a[i] / s;

        return NIL;
}

BUILTIN_FUNCTION(accel_svdiv)
{
        ASSERT_ARGC("svdiv()", 4);

        double  s   = FLOAT_ARG(0);
        double *a   = PTR_ARG(1);
        double *out = PTR_ARG(2);
        i64     n   = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                out[i] = s / a[i];

        return NIL;
}

BUILTIN_FUNCTION(accel_vneg)
{
        ASSERT_ARGC("vneg()", 3);

        double *a   = PTR_ARG(0);
        double *out = PTR_ARG(1);
        i64     n   = INT_ARG(2);

        for (i64 i = 0; i < n; ++i)
                out[i] = -a[i];

        return NIL;
}

BUILTIN_FUNCTION(accel_vabs)
{
        ASSERT_ARGC("vabs()", 3);

        double *a   = PTR_ARG(0);
        double *out = PTR_ARG(1);
        i64     n   = INT_ARG(2);

        for (i64 i = 0; i < n; ++i)
                out[i] = fabs(a[i]);

        return NIL;
}

BUILTIN_FUNCTION(accel_vclip)
{
        ASSERT_ARGC("vclip()", 5);

        double *a   = PTR_ARG(0);
        double  lo  = FLOAT_ARG(1);
        double  hi  = FLOAT_ARG(2);
        double *out = PTR_ARG(3);
        i64     n   = INT_ARG(4);

        for (i64 i = 0; i < n; ++i) {
                double v = a[i];
                out[i] = v < lo ? lo : v > hi ? hi : v;
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_vfill)
{
        ASSERT_ARGC("vfill()", 3);

        double  val = FLOAT_ARG(0);
        double *out = PTR_ARG(1);
        i64     n   = INT_ARG(2);

        for (i64 i = 0; i < n; ++i)
                out[i] = val;

        return NIL;
}

BUILTIN_FUNCTION(accel_vclr)
{
        ASSERT_ARGC("vclr()", 2);

        double *out = PTR_ARG(0);
        i64     n   = INT_ARG(1);

        memset(out, 0, n * sizeof (double));

        return NIL;
}

BUILTIN_FUNCTION(accel_vramp)
{
        ASSERT_ARGC("vramp()", 4);

        double  start = FLOAT_ARG(0);
        double  step  = FLOAT_ARG(1);
        double *out   = PTR_ARG(2);
        i64     n     = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                out[i] = start + i * step;

        return NIL;
}

BUILTIN_FUNCTION(accel_mtrans)
{
        ASSERT_ARGC("mtrans()", 4);

        double *src = PTR_ARG(0);
        double *dst = PTR_ARG(1);
        i64     m   = INT_ARG(2);
        i64     n   = INT_ARG(3);

        for (i64 i = 0; i < m; ++i)
                for (i64 j = 0; j < n; ++j)
                        dst[j * m + i] = src[i * n + j];

        return NIL;
}

BUILTIN_FUNCTION(accel_sve)
{
        ASSERT_ARGC("sve()", 2);

        double *a = PTR_ARG(0);
        i64     n = INT_ARG(1);

        double s = 0.0;
        for (i64 i = 0; i < n; ++i)
                s += a[i];

        return REAL(s);
}

BUILTIN_FUNCTION(accel_maxv)
{
        ASSERT_ARGC("maxv()", 2);

        double *a = PTR_ARG(0);
        i64     n = INT_ARG(1);

        double m = a[0];
        for (i64 i = 1; i < n; ++i)
                if (a[i] > m) m = a[i];

        return REAL(m);
}

BUILTIN_FUNCTION(accel_minv)
{
        ASSERT_ARGC("minv()", 2);

        double *a = PTR_ARG(0);
        i64     n = INT_ARG(1);

        double m = a[0];
        for (i64 i = 1; i < n; ++i)
                if (a[i] < m) m = a[i];

        return REAL(m);
}

BUILTIN_FUNCTION(accel_vexp)
{
        ASSERT_ARGC("vexp()", 3);

        double *a   = PTR_ARG(0);
        double *out = PTR_ARG(1);
        i64     n   = INT_ARG(2);

        for (i64 i = 0; i < n; ++i)
                out[i] = exp(a[i]);

        return NIL;
}

BUILTIN_FUNCTION(accel_vlog)
{
        ASSERT_ARGC("vlog()", 3);

        double *a   = PTR_ARG(0);
        double *out = PTR_ARG(1);
        i64     n   = INT_ARG(2);

        for (i64 i = 0; i < n; ++i)
                out[i] = log(a[i]);

        return NIL;
}

BUILTIN_FUNCTION(accel_vsqrt)
{
        ASSERT_ARGC("vsqrt()", 3);

        double *a   = PTR_ARG(0);
        double *out = PTR_ARG(1);
        i64     n   = INT_ARG(2);

        for (i64 i = 0; i < n; ++i)
                out[i] = sqrt(a[i]);

        return NIL;
}

BUILTIN_FUNCTION(accel_vpow)
{
        ASSERT_ARGC("vpow()", 4);

        double *bases = PTR_ARG(0);
        double *exps  = PTR_ARG(1);
        double *out   = PTR_ARG(2);
        i64     n     = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                out[i] = pow(bases[i], exps[i]);

        return NIL;
}

BUILTIN_FUNCTION(accel_broadcast_binop)
{
        ASSERT_ARGC("broadcast_binop()", 9);

        double *a     = PTR_ARG(0);
        double *b     = PTR_ARG(1);
        double *out   = PTR_ARG(2);
        i64    *a_str = PTR_ARG(3);
        i64    *b_str = PTR_ARG(4);
        i64    *o_shp = PTR_ARG(5);
        i64     ndim  = INT_ARG(6);
        i64     total = INT_ARG(7);
        i64     op    = INT_ARG(8);

        for (i64 k = 0; k < total; k++) {
                i64 ai = 0, bi = 0, rem = k;
                for (i64 d = ndim - 1; d >= 0; d--) {
                        i64 idx = rem % o_shp[d];
                        rem /= o_shp[d];
                        ai += idx * a_str[d];
                        bi += idx * b_str[d];
                }
                double va = a[ai], vb = b[bi];
                switch (op) {
                case 0: out[k] = va + vb; break;
                case 1: out[k] = va - vb; break;
                case 2: out[k] = va * vb; break;
                case 3: out[k] = va / vb; break;
                case 4: out[k] = pow(va, vb); break;
                }
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_transpose_nd)
{
        ASSERT_ARGC("transpose_nd()", 4);

        double *src   = PTR_ARG(0);
        double *dst   = PTR_ARG(1);
        i64    *shape = PTR_ARG(2);
        i64     ndim  = INT_ARG(3);

        i64 src_strides[32], out_strides[32], total = 1;

        for (i64 d = ndim - 1; d >= 0; d--) {
                src_strides[d] = total;
                total *= shape[d];
        }

        out_strides[ndim - 1] = 1;
        for (i64 d = ndim - 2; d >= 0; d--)
                out_strides[d] = out_strides[d + 1] * shape[ndim - 2 - d];

        for (i64 k = 0; k < total; k++) {
                i64 si = 0, rem = k;
                for (i64 d = 0; d < ndim; d++) {
                        i64 idx = rem / out_strides[d];
                        rem %= out_strides[d];
                        si += idx * src_strides[ndim - 1 - d];
                }
                dst[k] = src[si];
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_vcmp_scalar)
{
        ASSERT_ARGC("vcmp_scalar()", 5);

        double *a   = PTR_ARG(0);
        double  s   = FLOAT_ARG(1);
        double *out = PTR_ARG(2);
        i64     n   = INT_ARG(3);
        i64     op  = INT_ARG(4);

        for (i64 i = 0; i < n; ++i) {
                int r;
                switch (op) {
                case 0: r = a[i] >  s; break;
                case 1: r = a[i] <  s; break;
                case 2: r = a[i] >= s; break;
                case 3: r = a[i] <= s; break;
                case 4: r = a[i] == s; break;
                default: r = a[i] != s; break;
                }
                out[i] = r ? 1.0 : 0.0;
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_vcmp_array)
{
        ASSERT_ARGC("vcmp_array()", 5);

        double *a   = PTR_ARG(0);
        double *b   = PTR_ARG(1);
        double *out = PTR_ARG(2);
        i64     n   = INT_ARG(3);
        i64     op  = INT_ARG(4);

        for (i64 i = 0; i < n; ++i) {
                int r;
                switch (op) {
                case 0: r = a[i] >  b[i]; break;
                case 1: r = a[i] <  b[i]; break;
                case 2: r = a[i] >= b[i]; break;
                case 3: r = a[i] <= b[i]; break;
                case 4: r = a[i] == b[i]; break;
                default: r = a[i] != b[i]; break;
                }
                out[i] = r ? 1.0 : 0.0;
        }

        return NIL;
}

BUILTIN_FUNCTION(accel_count_nz)
{
        ASSERT_ARGC("count_nz()", 2);

        double *a = PTR_ARG(0);
        i64     n = INT_ARG(1);

        i64 count = 0;
        for (i64 i = 0; i < n; ++i)
                if (a[i] != 0.0) ++count;

        return INTEGER(count);
}

BUILTIN_FUNCTION(accel_bool_index)
{
        ASSERT_ARGC("bool_index()", 4);

        double *src  = PTR_ARG(0);
        double *mask = PTR_ARG(1);
        double *out  = PTR_ARG(2);
        i64     n    = INT_ARG(3);

        i64 j = 0;
        for (i64 i = 0; i < n; ++i)
                if (mask[i] != 0.0)
                        out[j++] = src[i];

        return INTEGER(j);
}

BUILTIN_FUNCTION(accel_bool_assign)
{
        ASSERT_ARGC("bool_assign()", 4);

        double *dst  = PTR_ARG(0);
        double *mask = PTR_ARG(1);
        double  val  = FLOAT_ARG(2);
        i64     n    = INT_ARG(3);

        for (i64 i = 0; i < n; ++i)
                if (mask[i] != 0.0)
                        dst[i] = val;

        return NIL;
}

BUILTIN_FUNCTION(accel_from_bytes)
{
        ASSERT_ARGC("fromBytes()", 4);

        Value v = ARG(0);
        unsigned char *src;
        if (v.type == VALUE_PTR)
                src = v.ptr;
        else if (v.type == VALUE_BLOB)
                src = v.blob->items;
        else
                zP("fromBytes(): arg[0] must be Blob or Ptr");

        i64     off = INT_ARG(1);
        double *dst = PTR_ARG(2);
        i64     n   = INT_ARG(3);

        unsigned char const *p = src + off;
        for (i64 i = 0; i < n; ++i)
                dst[i] = (double)p[i];

        return NIL;
}

BUILTIN_FUNCTION(accel_softmax)
{
        ASSERT_ARGC("softmax()", 4);

        double *src = PTR_ARG(0);
        double *dst = PTR_ARG(1);
        i64     n   = INT_ARG(2);
        i64     k   = INT_ARG(3);

        for (i64 i = 0; i < n; ++i) {
                double mx = src[i * k];
                for (i64 j = 1; j < k; ++j)
                        if (src[i * k + j] > mx)
                                mx = src[i * k + j];
                double s = 0.0;
                for (i64 j = 0; j < k; ++j) {
                        double e = exp(src[i * k + j] - mx);
                        dst[i * k + j] = e;
                        s += e;
                }
                double inv = 1.0 / s;
                for (i64 j = 0; j < k; ++j)
                        dst[i * k + j] *= inv;
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
        for (i64 i = 0; i < total; ++i) {
                if (targets[i] > 0.0) {
                        double p = probs[i];
                        loss -= targets[i] * log(p > 1e-15 ? p : 1e-15);
                }
        }

        return REAL(loss);
}

BUILTIN_FUNCTION(accel_sum_axis0)
{
        ASSERT_ARGC("sumAxis0()", 4);

        double *src  = PTR_ARG(0);
        double *dst  = PTR_ARG(1);
        i64     rows = INT_ARG(2);
        i64     cols = INT_ARG(3);

        memset(dst, 0, cols * sizeof (double));

        for (i64 i = 0; i < rows; ++i)
                for (i64 j = 0; j < cols; ++j)
                        dst[j] += src[i * cols + j];

        return NIL;
}
