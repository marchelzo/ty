#include <string.h>
#include <limits.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "log.h"
#include "functions.h"
#include "operators.h"
#include "xd.h"
#include "vm.h"
#include "ty.h"

static Value
array_drop_mut(Ty *ty, Value *array, int argc, Value *kwargs);

static Value
array_drop(Ty *ty, Value *array, int argc, Value *kwargs);

static Value
array_min_by(Ty *ty, Value *array, int argc, Value *kwargs);

static Value
array_max_by(Ty *ty, Value *array, int argc, Value *kwargs);

static Value
array_reverse(Ty *ty, Value *array, int argc, Value *kwargs);

typedef struct {
        Value f;
        Ty *ty;
} SortContext;

static int
#if defined(__linux__)
compare_default(void const *v1, void const *v2, void *ty)
#else
compare_default(void *ty, void const *v1, void const *v2)
#endif
{
        return v_cmp(v1, v2);
}

static int
#if defined(__linux__)
compare_by(void const *v1, void const *v2, void *ctx_)
#else
compare_by(void *ctx_, void const *v1, void const *v2)
#endif
{
        SortContext *ctx = ctx_;
        Ty *ty = ctx->ty;

        Value k1 = vm_call1(ty, &ctx->f, (Value *)v1);
        gP(&k1);

        Value k2 = vm_call1(ty, &ctx->f, (Value *)v2);
        gP(&k2);

        int result = v_cmp(&k1, &k2);

        gX();
        gX();

        return result;
}

static int
#if defined(__linux__)
compare_by2(void const *v1, void const *v2, void *ctx_)
#else
compare_by2(void *ctx_, void const *v1, void const *v2)
#endif
{
        SortContext *ctx = ctx_;
        Ty *ty = ctx->ty;

        Value v = vm_eval_function(ty, &ctx->f, v1, v2, NULL);
        gP(&v);

        int result;

        if (v.type == VALUE_INTEGER) {
                result = v.z;
        } else {
                result = v_truthy(&v) ? 1 : -1;
        }

        gX();

        return result;
}

inline static void
shrink(Ty *ty, Value *v)
{
        Array *a = v->array;

        if (
                (vC(*a) > 8 * vN(*a))
             || (vC(*a) - vN(*a) > 1000)
        ) {
                vC(*a) = vN(*a);
                if (vN(*a) == 0) {
                        mF(vv(*a));
                        vv(*a) = NULL;
                } else {
                        mREu(vv(*a), vN(*a) * sizeof (Value));
                }
        }
}

static Value
array_push(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Array.push()", 0, INT_MAX);
        vvPn(*array->array, &ARG(0), argc);
        return NIL;
}

static Value
array_insert(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Array.insert()", 2, INT_MAX);

        imax i = INT_ARG(0);

        if (i < 0) {
                i += vN(*array->array) + 1;
        }

        if (i < 0 || i > vN(*array->array)) {
                bP("index out of range: %"PRIiMAX, i);
        }

        vvIn(*array->array, &ARG(1), argc - 1, i);

        return *array;
}

static Value
array_pop(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.pop()", 0, 1);

        Value v;

        if (argc == 0) {
                if (vN(*array->array) == 0) {
                        bP("empty array");
                }
                v = vXx(*array->array);
        } else {
                imax i = INT_ARG(0);
                if (i < 0) {
                        i += vN(*array->array);
                }
                if (i < 0 || i >= vN(*array->array)) {
                        bP("out of range: %"PRIiMAX, i);
                }
                v = v__(*array->array, i);
                vvXi(*array->array, i);
        }

        shrink(ty, array);

        return v;
}

static Value
array_swap(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.swap()", 2);

        imax i = INT_ARG(0);
        imax j = INT_ARG(1);

        if (i < 0) {
                i += vN(*array->array);
        }
        if (j < 0) {
                j += vN(*array->array);
        }

        if (
                (i < 0) || (i >= vN(*array->array))
             || (j < 0) || (j >= vN(*array->array))
        ) {
                bP("out of range: (%"PRIiMAX", %"PRIiMAX")", i, j);
        }

        Value tmp = v__(*array->array, i);
        *v_(*array->array, i) = v__(*array->array, j);
        *v_(*array->array, j) = tmp;

        return *array;
}

static Value
array_splice(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.splice()", 1, 2);

        imax i = INT_ARG(0);
        imax n;

        if (argc == 2) {
                n = INT_ARG(1);
        } else {
                n = vN(*array->array);
        }

        if (i < 0) {
                i += vN(*array->array);
        }
        if (i < 0) {
                bP("out of range: %"PRIiMAX, i);
        }

        if (n < 0) {
                n += vN(*array->array);
        }
        if (n < 0) {
                bP("bad count: %"PRIiMAX, n);
        }

        i = min(i, vN(*array->array));
        n = min(n, vN(*array->array) - i);

        Array *slice = vA();
        NOGC(slice);

        vvPn(*slice, vv(*array->array) + i, n);
        memmove(
                vv(*array->array) + i,
                vv(*array->array) + (i + n),
                (vN(*array->array) - (i + n)) * sizeof (Value)
        );
        vN(*array->array) -= n;

        shrink(ty, array);

        OKGC(slice);

        return ARRAY(slice);
}

inline static Value
index_safe(Array const *array, isize i)
{
        if (i < 0 || i >= vN(*array)) {
                return NIL;
        } else {
                return v__(*array, i);
        }
}

static Value
array_zip(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Array.zip()", 1, INT_MAX);

        usize n = vN(*array->array);
        Value f = KWARG("f", _ANY);
        bool longest = HAVE_FLAG("longest");

        for (int i = 0; i < argc; ++i) {
                Array *arg = ARRAY_ARG(i);
                n = longest
                  ? max(n, vN(*arg))
                  : min(n, vN(*arg));
        }

        while (vN(*array->array) < n) {
                vAp(array->array, NIL);
        }

        for (usize i = 0; i < n; ++i) {
                if (IsMissing(f)) {
                        Value tuple = vT(argc + 1);
                        tuple.items[0] = index_safe(array->array, i);
                        for (int j = 0; j < argc; ++j) {
                                tuple.items[j + 1] = index_safe(ARRAY_ARG(j), i);
                        }
                        *v_(*array->array, i) = tuple;
                } else {
                        Value v = index_safe(array->array, i);
                        vmP(&v);
                        for (int j = 0; j < argc; ++j) {
                                v = index_safe(ARG(-1).array, i);
                                vmP(&v);
                        }
                        *v_(*array->array, i) = vmC(&f, argc + 1);
                }
        }

        vN(*array->array) = n;
        shrink(ty, array);

        return *array;
}

static Value
array_window(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.window()", 1, 2);

        imax k = INT_ARG(0);
        if (k <= 0) {
                bP("bad window size: %"PRIiMAX, k);
        }

        isize n = max((imax)vN(*array->array) - k + 1, 0);

        if (argc == 2) {
                Value f = ARG(1);
                for (isize i = 0; i < n; ++i) {
                        for (isize j = i; j < i + k; ++j) {
                                vmP(v_(*array->array, j));
                        }
                        *v_(*array->array, i) = vmC(&f, k);
                }

        } else {
                for (isize i = 0; i < n; ++i) {
                        Array *win = vAn(k);
                        for (isize j = i; j < i + k; ++j) {
                                vPx(*win, v__(*array->array, j));
                        }
                        *v_(*array->array, i) = ARRAY(win);
                }
        }

        vN(*array->array) = n;
        shrink(ty, array);

        return *array;
}

inline static isize
iwrap(isize i, isize n)
{
        return (i < 0) ? (i + n) : i;
}

inline static bool
idx_ok(Array const *array, isize i)
{
        return (i >= 0) && (i < (isize)vN(*array));
}

static Value
slice3(Ty *ty, Array const *xs, Value const *_i, Value const *_j, Value const *_k)
{
        Array *slice = uAo0(sizeof (Array), GC_ARRAY);

        isize i = _i->z;
        isize k = (_k->type == VALUE_NIL) ? 1 : (_k->z + !_k->z);

        if (k < 0) {
                isize j = (_j->type == VALUE_NIL) ? 0 : _j->z;
                isize start = min(iwrap(i - 1, vN(*xs)), vN(*xs) - 1);
                isize stop = max(iwrap(j, vN(*xs)), 0);
                for (isize ix = start; ix >= stop; ix += k) {
                        if (idx_ok(xs, ix)) {
                                uvP(*slice, v__(*xs, ix));
                        }
                }
        } else {
                isize j = (_j->type == VALUE_NIL) ? vN(*xs) : _j->z;
                isize start = max(iwrap(i, vN(*xs)), 0);
                isize stop = min(iwrap(j, vN(*xs)), vN(*xs));
                for (isize ix = start; ix < stop; ix += k) {
                        if (idx_ok(xs, ix)) {
                                uvP(*slice, v__(*xs, ix));
                        }
                }
        }

        NOGC(slice);
        CheckUsed(ty);
        OKGC(slice);

        return ARRAY(slice);
}

static Value
array_slice(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.slice()", 1, 2, 3);

        if (argc == 3) {
                Value _i = ARGx(0, VALUE_INTEGER);
                Value _j = ARGx(1, VALUE_INTEGER, VALUE_NIL);
                Value _k = ARGx(2, VALUE_INTEGER, VALUE_NIL);
                return slice3(ty, array->array, &_i, &_j, &_k);
        }

        imax i = INT_ARG(0);
        imax n;

        if (argc == 2) {
                n = INT_ARG(1);
        } else {
                n = vN(*array->array);
        }

        if (i < 0) {
                i += vN(*array->array);
        }
        if (i < 0) {
                bP("out of range: %"PRIiMAX, i);
        }

        if (n < 0) {
                n += vN(*array->array);
        }
        if (n < 0) {
                bP("bad count: %"PRIiMAX, n);
        }

        i = min(i, vN(*array->array));
        n = min(n, vN(*array->array) - i);

        Array *slice = vAn(n);
        memmove(
                vv(*slice),
                vv(*array->array) + i,
                n * sizeof (Value)
        );
        vN(*slice) = n;

        return ARRAY(slice);
}

static Value
array_sort(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.sort()", 0, 1, 2);

        Array const *xs = array->array;
        isize i = 0;
        isize n = vN(*xs);

        switch (argc) {
        case 0:
                break;
        case 1:
                i = INT_ARG(0);
                break;
        case 2:
                i = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (i < 0) {
                i += vN(*xs);
        }

        if (n < 0 || i < 0 || i + n > vN(*xs)) {
                bP(
                        "index out of range: i=%zd, n=%zd, #xs=%zu",
                        i, n, vN(*xs)
                );
        }

        Value *by = NAMED("by");
        Value *cmp = NAMED("cmp");

        if (by != NULL && cmp != NULL) {
                bP("kwargs `by` and `cmp` both specified");
        }

        SortContext ctx = {
                .ty = ty
        };

        if (by != NULL) {
                if (!CALLABLE(*by)) {
                        bP("`by` not callable: %s", VSC(by));
                }
                ctx.f = *by;
                rqsort(vv(*array->array) + i, n, sizeof (Value), compare_by, &ctx);
        } else if (cmp != NULL) {
                if (!CALLABLE(*cmp)) {
                        bP("`cmp` not callable: %s", VSC(cmp));
                }
                ctx.f = *cmp;
                rqsort(vv(*array->array) + i, n, sizeof (Value), compare_by2, &ctx);
        } else {
                rqsort(vv(*array->array) + i, n, sizeof (Value), compare_default, ty);
        }

        Value *desc = NAMED("desc");

        if (desc != NULL && v_truthy(desc)) {
                array_reverse(ty, array, argc, NULL);
        }

        return *array;
}

static Value
array_next_permutation(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.nextPermutation()", 0);

        Array *xs = array->array;

        for (isize i = (isize)vN(*xs) - 1; i > 0; --i) {
                if (v_cmp(v_(*xs, i - 1), v_(*xs, i)) < 0) {
                        isize j = i;
                        for (isize k = i + 1; k < vN(*xs); ++k) {
                                if (
                                        (v_cmp(v_(*xs, k), v_(*xs, j)) < 0)
                                     && (v_cmp(v_(*xs, k), v_(*xs, i - 1)) > 0)
                                ) {
                                        j = k;
                                }
                        }

                        SWAP(Value, *v_(*xs, i - 1), *v_(*xs, j));

                        vmP(&INTEGER(i));
                        array_sort(ty, array, 1, kwargs);
                        vmX();

                        return *array;
                }
        }

        return NIL;
}

static Value
array_take_while_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.takeWhile!()", 1);

        Value f = ARG(0);

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        usize keep = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                if (value_apply_predicate(ty, &f, v_(*array->array, i))) {
                        keep += 1;
                } else {
                        break;
                }
        }

        vN(*array->array) = keep;
        shrink(ty, array);

        return *array;
}

static Value
array_take_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.takeWhile()", 1);

        Value f = ARG(0);

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        usize keep = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                if (value_apply_predicate(ty, &f, v_(*array->array, i))) {
                        keep += 1;
                } else {
                        break;
                }
        }

        Value result = ARRAY(vA());
        NOGC(result.array);
        value_array_reserve(ty, result.array, keep);
        OKGC(result.array);
        memmove(vv(*result.array), vv(*array->array), keep * sizeof (Value));
        vN(*result.array) = keep;

        return result;
}

static Value
array_drop_while_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.dropWhile!()", 1);

        Value f = ARG(0);

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        usize drop = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                if (value_apply_predicate(ty, &f, v_(*array->array, i))) {
                        drop += 1;
                } else {
                        break;
                }
        }

        memmove(
                vv(*array->array),
                vv(*array->array) + drop,
                (vN(*array->array) - drop) * sizeof (Value)
        );
        vN(*array->array) -= drop;
        shrink(ty, array);

        return *array;
}

static Value
array_drop_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.dropWhile()", 1);

        Value f = ARG(0);

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        usize drop = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                if (value_apply_predicate(ty, &f, v_(*array->array, i))) {
                        drop += 1;
                } else {
                        break;
                }
        }

        usize n = vN(*array->array) - drop;
        Value result = ARRAY(vA());
        NOGC(result.array);
        value_array_reserve(ty, result.array, n);
        OKGC(result.array);
        memmove(vv(*result.array), vv(*array->array) + drop, n * sizeof (Value));
        vN(*result.array) = n;

        return result;
}

static Value
array_uniq(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.uniq()", 0, 1);

        Value f = (argc > 0) ? ARG(0) : NONE;

        Value d = DICT(dict_new(ty));
        gP(&d);

        usize n = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                Value e = v__(*array->array, i);
                Value k = !IsNone(f)  ? vm_eval_function(ty, &f, &e, NULL) : e;
                Value *v = dict_put_key_if_not_exists(ty, d.dict, k);
                if (v->type == VALUE_NIL) {
                        *v = e;
                        *v_(*array->array, n++) = e;
                }
        }

        gX();
        vN(*array->array) = n;

        return *array;
}

static Value
array_take_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.take!()", 1);

        imax n = INT_ARG(0);
        vN(*array->array) = (n < 0) ? 0 : min(vN(*array->array), (usize)n);
        shrink(ty, array);

        return *array;
}

static Value
array_take(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.take()", 1);

        Value result = ARRAY(vA());
        imax n = INT_ARG(0);
        usize count = (n < 0) ? 0 : min((usize)n, vN(*array->array));

        NOGC(result.array);
        value_array_reserve(ty, result.array, count);
        OKGC(result.array);

        memmove(vv(*result.array), vv(*array->array), count * sizeof (Value));
        vN(*result.array) = count;

        return result;
}

static Value
array_drop_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.drop!()", 1);

        imax n = INT_ARG(0);
        usize d = (n < 0) ? 0 : min(vN(*array->array), (usize)n);

        memmove(
                vv(*array->array),
                vv(*array->array) + d,
                (vN(*array->array) - d) * sizeof (Value)
        );
        vN(*array->array) -= d;
        shrink(ty, array);

        return *array;
}

static Value
array_drop(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.drop()", 1);

        imax n = INT_ARG(0);

        usize d = (n < 0) ? 0 : min((usize)n, vN(*array->array));
        usize count = vN(*array->array) - d;

        Array *result = vAn(count);
        memcpy(vv(*result), vv(*array->array) + d, count * sizeof (Value));
        vN(*result) = count;

        return ARRAY(result);
}

static Value
array_sum(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.sum()", 0, 1);

        Value zero = (argc == 1) ? ARG(0) : NIL;

        if (vN(*array->array) == 0) {
                return zero;
        }

        isize i0;
        Value sum;

        if (argc == 1) {
                sum = zero;
                i0 = 0;
        } else {
                sum = v__(*array->array, 0);
                i0 = 1;
        }

        Value val;

        for (isize i = i0; i < vN(*array->array); ++i) {
                gP(&sum);
                val = v__(*array->array, i);
                sum = vm_2op(ty, OP_ADD, &sum, &val);
                gX();
        }

        return sum;
}

static Value
array_join(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.join()", 0, 1);

        if (vN(*array->array) == 0) {
                return STRING_EMPTY;
        }

        Value sep;
        if (argc == 0) {
                sep = STRING_EMPTY;
        } else {
                sep = ARGx(0, VALUE_STRING);
        }

        vmP(v_(*array->array, 0));
        Value sum = builtin_str(ty, 1, NULL);
        vmX();
        Value v = NIL;

        for (usize i = 1; i < vN(*array->array); ++i) {
                gP(&sum);
                gP(&v);
                vmP(v_(*array->array, i));
                v = builtin_str(ty, 1, NULL);
                vmX();
                gX();
                gP(&v);
                sum = vm_2op(ty, OP_ADD, &sum, &sep);
                gX();
                gX();
                gP(&v);
                gP(&sum);
                sum = vm_2op(ty, OP_ADD, &sum, &v);
                gX();
                gX();
        }

        return sum;
}

static Value
array_consume_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.consumeWhile()", 2);

        Value f = ARG(0);
        Value p = ARG(1);

        if (!CALLABLE(f)) {
                bP("source is not callable: %s", VSC(&f));
        }

        if (!CALLABLE(p)) {
                bP("predicate is not callable: %s", VSC(&p));
        }

        Value v = NIL;

        for (;;) {
                v = vm_eval_function(ty, &f, NULL);
                gP(&v);
                bool more = value_apply_predicate(ty, &p, &v);
                if (more) {
                        vAp(array->array, v);
                        gX();
                } else {
                        gX();
                        break;
                }
        }

        return *array;
}

static Value
array_groups_of(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.groups-of()", 1, 2);

        imax nsize = INT_ARG(0);

        if (nsize <= 0) {
                bP("group size must be positive");
        }

        usize size = nsize;
        bool keep_short = true;

        if (argc == 2) {
                keep_short = BOOL_ARG(1);
        }

        usize n = 0;
        usize i = 0;
        while (i + size <= vN(*array->array)) {
                Array *group = vA();
                NOGC(group);
                vvPn(*group, vv(*array->array) + i, size);
                OKGC(group);
                *v_(*array->array, n++) = ARRAY(group);
                i += size;
        }

        if (keep_short && i != vN(*array->array)) {
                Array *last = vA();
                NOGC(last);
                vvPn(*last, vv(*array->array) + i, vN(*array->array) - i);
                OKGC(last);
                *v_(*array->array, n++) = ARRAY(last);
        }

        vN(*array->array) = n;
        shrink(ty, array);

        return *array;
}

static Value
array_group_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.group-by()", 1);

        Value f = ARG(0);

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        Value v1, v2;
        v1 = v2 = NIL;

        usize len = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                Value group = ARRAY(vA());
                NOGC(group.array);
                Value e = v__(*array->array, i);
                v1 = vm_call1(ty, &f, &e);
                gP(&v1);
                vAp(group.array, e);
                while (i + 1 < vN(*array->array)) {
                        v2 = vm_call1(ty, &f, v_(*array->array, i + 1));
                        gP(&v2);
                        if (v_eq(&v1, &v2)) {
                                vAp(group.array, v__(*array->array, ++i));
                                gX();
                        } else {
                                gX();
                                break;
                        }
                }
                gX();
                OKGC(group.array);
                *v_(*array->array, len++) = group;
        }

        vN(*array->array) = len;
        shrink(ty, array);

        return *array;
}

static Value
array_group(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.group()", 0, 1);

        if (argc == 1) {
                return array_group_by(ty, array, argc, kwargs);
        }

        usize len = 0;
        for (usize i = 0; i < vN(*array->array); ++i) {
                Value group = ARRAY(vA());
                NOGC(group.array);
                vAp(group.array, v__(*array->array, i));
                while (
                        (i + 1 < vN(*array->array))
                     && v_eq(v_(*array->array, i), v_(*array->array, i + 1))
                ) {
                        vAp(group.array, v__(*array->array, ++i));
                }
                OKGC(group.array);
                *v_(*array->array, len++) = group;
        }

        vN(*array->array) = len;
        shrink(ty, array);

        return *array;
}

static Value
array_intersperse(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.intersperse()", 1);

        Value v = ARG(0);

        usize count = vN(*array->array);
        if (count < 2) {
                return *array;
        }

        usize n = count - 1;
        usize newcount = 2 * n + 1;
        value_array_reserve(ty, array->array, newcount);
        memcpy(
                vv(*array->array) + n + 1,
                vv(*array->array) + 1,
                n * sizeof (Value)
        );

        usize lo = 1;
        usize hi = n + 1;
        for (usize i = 0; i < n; ++i) {
                *v_(*array->array, lo++) = v;
                *v_(*array->array, lo++) = v__(*array->array, hi++);
        }

        vN(*array->array) = newcount;
        return *array;
}

static Value
array_min(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.min()", 0, 1);

        if (argc == 1) {
                return array_min_by(ty, array, argc, kwargs);
        }

        if (vN(*array->array) == 0) {
                return NIL;
        }

        Value min = v_0(*array->array);

        for (usize i = 1; i < vN(*array->array); ++i) {
                Value v = v__(*array->array, i);
                if (v_cmp(&v, &min) < 0) {
                        min = v;
                }
        }

        return min;
}

static Value
array_min_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.minBy()", 1);

        if (vN(*array->array) == 0) {
                return NIL;
        }

        Value f = ARG(0);
        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        Value min = v_0(*array->array);

        if (ARITY(f) > 1) {
                for (usize i = 1; i < vN(*array->array); ++i) {
                        Value v = v__(*array->array, i);
                        Value r = vm_eval_function(ty, &f, &v, &min, NULL);
                        gP(&r);
                        bool less = (r.type == VALUE_INTEGER)
                                  ? (r.z < 0)
                                  : v_truthy(&r);
                        if (less) {
                                min = v;
                        }
                        gX();
                }
        } else {
                Value k = vm_eval_function(ty, &f, &min, NULL);
                gP(&k);
                for (usize i = 1; i < vN(*array->array); ++i) {
                        Value v = v__(*array->array, i);
                        Value r = vm_eval_function(ty, &f, &v, NULL);
                        gP(&r);
                        if (v_cmp(&r, &k) < 0) {
                                min = v;
                                k = r;
                        }
                        gX();
                        gX();
                        gP(&k);
                }
                gX();
        }

        return min;
}

static Value
array_max(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.max()", 0, 1);

        if (argc == 1) {
                return array_max_by(ty, array, argc, kwargs);
        }

        if (vN(*array->array) == 0) {
                return NIL;
        }

        Value max = v_0(*array->array);

        for (usize i = 1; i < vN(*array->array); ++i) {
                Value v = v__(*array->array, i);
                if (v_cmp(&v, &max) > 0) {
                        max = v;
                }
        }

        return max;
}

static Value
array_max_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.maxBy()", 1);

        if (vN(*array->array) == 0) {
                return NIL;
        }

        Value f = ARG(0);
        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        Value max = v_0(*array->array);

        if (ARITY(f) > 1) {
                for (usize i = 1; i < vN(*array->array); ++i) {
                        Value v = v__(*array->array, i);
                        Value r = vm_eval_function(ty, &f, &v, &max, NULL);
                        gP(&r);
                        bool greater = (r.type == VALUE_INTEGER)
                                     ? r.z > 0
                                     : v_truthy(&r);
                        if (greater) {
                                max = v;
                        }
                        gX();
                }
        } else {
                Value k = vm_eval_function(ty, &f, &max, NULL);
                gP(&k);
                for (usize i = 1; i < vN(*array->array); ++i) {
                        Value v = v__(*array->array, i);
                        Value r = vm_eval_function(ty, &f, &v, NULL);
                        gP(&r);
                        if (v_cmp(&r, &k) > 0) {
                                max = v;
                                k = r;
                        }
                        gX();
                        gX();
                        gP(&k);
                }
                gX();
        }

        return max;
}

static Value
array_length(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.len()", 0);
        return INTEGER(vN(*array->array));
}

static Value
array_shuffle(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.shuffle!()", 0);

        for (usize i = vN(*array->array); i > 1; --i) {
                usize j = xoshiro256ss(ty) % i;
                SWAP(Value, *v_(*array->array, i - 1), *v_(*array->array, j));
        }

        return *array;
}

static Value
array_map(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.map()", 1);

        Value f = ARG(0);
        usize n = vN(*array->array);

        for (usize i = 0; i < n; ++i) {
                Value x = v__(*array->array, i);
                Value y = vm_call1(ty, &f, &x);
                *v_(*array->array, i) = y;
        }

        return *array;
}

static Value
array_enumerate(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.enumerate()", 0);

        usize n = vN(*array->array);

        for (usize i = 0; i < n; ++i) {
                Value entry = PAIR(
                        INTEGER(i),
                        v__(*array->array, i)
                );
                *v_(*array->array, i) =  entry;
        }

        return *array;
}

static Value
array_remove(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.remove()", 1);

        Value v = ARG(0);

        usize n = vN(*array->array);
        usize j = 0;
        for (usize i = 0; i < n; ++i) {
                if (!v_eq(&v, v_(*array->array, i))) {
                        *v_(*array->array, j++) = v__(*array->array, i);
                }
        }

        vN(*array->array) = j;
        shrink(ty, array);

        return *array;
}

static Value
array_filter(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.filter()", 1);

        Value pred = ARG(0);

        usize n0 = vN(*array->array);
        usize n = 0;
        for (usize i = 0; i < n0; ++i) {
                Value x = v__(*array->array, i);
                if (value_apply_predicate(ty, &pred, &x)) {
                        *v_(*array->array, n++) = x;
                }
        }

        vN(*array->array) = n;
        shrink(ty, array);

        return *array;
}

static Value
array_find(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.find()", 1);

        Value pred = ARG(0);
        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        usize n = vN(*array->array);
        for (usize i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                        return v__(*array->array, i);
                }
        }

        return NIL;
}

static Value
array_findr(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.findr()", 1);

        Value pred = ARG(0);
        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        isize n = vN(*array->array);
        for (isize i = n - 1; i >= 0; --i) {
                if (value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                        return v__(*array->array, i);
                }
        }

        return NIL;
}

static Value
array_bsearch(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.bsearch()", 1);

        Value v = ARG(0);

        isize i = 0,
             lo = 0,
             hi = vN(*array->array) - 1;

        while (lo <= hi) {
                isize m = (lo + hi) / 2;
                int c = v_cmp(&v, v_(*array->array, m));
                if (c < 0) {
                        hi = m - 1;
                        i = m;
                } else if (c > 0) {
                        lo = m + 1;
                        i = lo;
                } else {
                        return INTEGER(m);
                }
        }

        return INTEGER(i);
}

static Value
array_bsearch_strict(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.bsearch!()", 1);

        Value v = ARG(0);

        isize lo = 0,
              hi = vN(*array->array) - 1;

        while (lo <= hi) {
                isize m = (lo + hi) / 2;
                int c = v_cmp(&v, v_(*array->array, m));
                if (c < 0) {
                        hi = m - 1;
                } else if (c > 0) {
                        lo = m + 1;
                } else {
                        return INTEGER(m);
                }
        }

        return NIL;
}

static Value
array_search_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.searchBy()", 1);

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        usize n = vN(*array->array);
        for (usize i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                        return INTEGER(i);
                }
        }

        return NIL;
}

static Value
array_searchr_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.searchrBy()", 1);

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        isize n = vN(*array->array);
        for (isize i = n - 1; i >= 0; --i) {
                if (value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                        return INTEGER(i);
                }
        }

        return NIL;
}

static Value
array_set(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.set()", 0);

        Dict *d = dict_new(ty);
        NOGC(d);

        for (usize i = 0; i < vN(*array->array); ++i) {
                dict_put_key_if_not_exists(ty, d, v__(*array->array, i));
        }

        OKGC(d);

        return DICT(d);
}

static Value
array_partition(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.partition!()", 1);

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        Array const *xs = array->array;

        if (vN(*xs) == 0) {
                return *array;
        }

        usize y = 0;
        usize n = vN(*xs);

        while (y < n) {
                Value *v = v_(*xs, y);
                if (value_apply_predicate(ty, &pred, v)) {
                        y += 1;
                } else {
                        SWAP(Value, *v, *v_(*xs, --n));
                }
        }

        return ARRAY((Array *)xs);
}

static Value
array_split_at(Ty *ty, Value *array, int argc, Value *kargs)
{
        ASSERT_ARGC("Array.split()", 1);

        imax i = INT_ARG(0);

        if (i < 0) {
                i += vN(*array->array);
        }

        if (i < 0 || i > vN(*array->array)) {
                bP("index out of range: %"PRIiMAX, i);
        }

        Array *front = vA();
        NOGC(front);

        Array *back = vA();
        NOGC(back);

        vvPn(*front, vv(*array->array), i);
        vvPn(*back, vv(*array->array) + i, vN(*array->array) - i);

        Value pair = PAIR(ARRAY(front), ARRAY(back));

        OKGC(front);
        OKGC(back);

        return pair;
}

static Value
array_partition_no_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.partition()", 1);

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        usize n = vN(*array->array);

        Array *yes = vA();
        NOGC(yes);

        Array *no = vA();
        NOGC(no);

        for (usize i = 0; i < n; ++i) {
                Value *v = v_(*array->array, i);
                if (value_apply_predicate(ty, &pred, v)) {
                        vAp(yes, *v);
                } else {
                        vAp(no, *v);
                }
        }

        Value result = PAIR(ARRAY(yes), ARRAY(no));

        OKGC(yes);
        OKGC(no);

        return result;
}

static Value
array_contains(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.contains?()", 1);

        Value v = ARG(0);

        usize n = vN(*array->array);
        for (usize i = 0; i < n; ++i) {
                if (v_eq(&v, v_(*array->array, i))) {
                        return BOOLEAN(true);
                }
        }

        return BOOLEAN(false);
}

static Value
array_tuple(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.tuple()", 0);

        usize n = vN(*array->array);

        Value v = vT(n);
        memcpy(v.items, vv(*array->array), n * sizeof (Value));

        return v;
}

static Value
array_tally(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.tally()", 0, 1);

        Value d = DICT(dict_new(ty));
        gP(&d);

        if (argc == 0) {
                for (usize i = 0; i < vN(*array->array); ++i) {
                        Value *c = dict_get_value(ty, d.dict, v_(*array->array, i));
                        if (c == NULL) {
                                dict_put_value(ty, d.dict, v__(*array->array, i), INTEGER(1));
                        } else {
                                c->z += 1;
                        }
                }
        } else {
                Value f = ARG(0);
                if (!CALLABLE(f)) {
                        bP("not callable: %s", VSC(&f));
                }

                for (usize i = 0; i < vN(*array->array); ++i) {
                        Value v = vm_call1(ty, &f, v_(*array->array, i));
                        Value *c = dict_get_value(ty, d.dict, &v);
                        if (c == NULL) {
                                dict_put_value(ty, d.dict, v, INTEGER(1));
                        } else {
                                c->z += 1;
                        }
                }
        }

        gX();

        return d;
}

static Value
array_search(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.search()", 1);

        Value v = ARG(0);

        usize n = vN(*array->array);
        for (usize i = 0; i < n; ++i) {
                if (v_eq(&v, v_(*array->array, i))) {
                        return INTEGER(i);
                }
        }

        return NIL;
}

static Value
array_searchr(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.searchr()", 1);

        Value v = ARG(0);

        isize n = vN(*array->array);
        for (isize i = n - 1; i >= 0; --i) {
                if (v_eq(&v, v_(*array->array, i))) {
                        return INTEGER(i);
                }
        }

        return NIL;
}

static Value
array_flat(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.flat()", 0, 1);

        vec(Value *) stack  = {0};
        vec(imax)    dstack = {0};

        imax maxdepth;

        if (argc == 1) {
                maxdepth = INT_ARG(0);
        } else {
                maxdepth = INT_MAX;
        }

        SCRATCH_SAVE();

        Array *r = vA();
        NOGC(r);

        usize n = vN(*array->array);
        for (usize i = 0; i < n; ++i) {
                svP(stack, v_(*array->array, i));
                svP(dstack, 1);
                while (vN(stack) > 0) {
                        Value *v = vXx(stack);
                        imax d = vXx(dstack);
                        if (v->type != VALUE_ARRAY || d > maxdepth) {
                                vAp(r, *v);
                        } else {
                                for (isize i = (isize)vN(*v->array) - 1; i >= 0; --i) {
                                        svP(stack, v_(*v->array, i));
                                        svP(dstack, d + 1);
                                }
                        }
                }
        }

        OKGC(r);

        SCRATCH_RESTORE();

        return ARRAY(r);
}

static Value
array_each(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.each()", 1, 2);

        if (argc == 1) {
                Value f = ARG(0);

                if (!CALLABLE(f)) {
                        bP("not callable: %s", VSC(&f));
                }

                usize n = vN(*array->array);

                for (usize i = 0; i < n; ++i) {
                        vm_eval_function(
                                ty,
                                &f,
                                v_(*array->array, i),
                                &INTEGER(i),
                                NULL
                        );
                }

                return *array;
        } else {
                Value v = ARG(0);
                Value f = ARG(1);

                if (!CALLABLE(f)) {
                        bP("not callable: %s", VSC(&f));
                }

                usize n = vN(*array->array);

                for (usize i = 0; i < n; ++i) {
                        vm_eval_function(
                                ty,
                                &f,
                                &v,
                                v_(*array->array, i),
                                &INTEGER(i),
                                NULL
                        );
                }

                return v;
        }
}

static Value
array_all(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.all()", 0, 1);

        usize n = vN(*array->array);

        if (argc == 0) {
                for (usize i = 0; i < n; ++i) {
                        if (!v_truthy(v_(*array->array, i))) {
                                return BOOLEAN(false);
                        }
                }
        } else {
                Value pred = ARG(0);

                if (!CALLABLE(pred)) {
                        bP("not callable: %s", VSC(&pred));
                }

                for (usize i = 0; i < n; ++i) {
                        if (!value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                                return BOOLEAN(false);
                        }
                }
        }

        return BOOLEAN(true);
}

static Value
array_any(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.any?()", 0, 1);

        usize n = vN(*array->array);

        if (argc == 0) {
                for (usize i = 0; i < n; ++i) {
                        if (v_truthy(v_(*array->array, i))) {
                                return BOOLEAN(true);
                        }
                }
        } else if (argc == 1) {
                Value pred = ARG(0);

                if (!CALLABLE(pred)) {
                        bP("not callable: %s", VSC(&pred));
                }

                for (usize i = 0; i < n; ++i) {
                        if (value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                                return BOOLEAN(true);
                        }
                }
        }

        return BOOLEAN(false);
}

static Value
array_count(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.count()", 1);

        Value v = ARG(0);

        usize n = vN(*array->array);
        usize k = 0;
        for (usize i = 0; i < n; ++i) {
                if (v_eq(&v, v_(*array->array, i))) {
                        k += 1;
                }
        }

        return INTEGER(k);
}

static Value
array_count_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.countBy()", 1);

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                bP("not callable: %s", VSC(&pred));
        }

        usize n = vN(*array->array);
        usize k = 0;
        for (usize i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, v_(*array->array, i))) {
                        k += 1;
                }
        }

        return INTEGER(k);
}

static Value
array_fold_left(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.fold()", 1, 2);

        usize start;
        Value f, v;

        if (argc == 1) {
                start = 1;
                f = ARG(0);
                if (vN(*array->array) == 0) {
                        bP("empty array and no start value");
                }
                v = v_0(*array->array);
        } else {
                start = 0;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        usize n = vN(*array->array);
        for (usize i = start; i < n; ++i) {
                gP(&v);
                v = vm_eval_function(ty, &f, &v, v_(*array->array, i), NULL);
                gX();
        }

        return v;
}

static Value
array_fold_right(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.foldr()", 1, 2);

        isize start;
        Value f, v;

        if (argc == 1) {
                start = (isize)vN(*array->array) - 2;
                f = ARG(0);
                if (vN(*array->array) == 0) {
                        bP("empty array and no start value");
                }
                v = v__(*array->array, start + 1);
        } else {
                start = (isize)vN(*array->array) - 1;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        for (isize i = start; i >= 0; --i) {
                gP(&v);
                v = vm_eval_function(
                        ty,
                        &f,
                        v_(*array->array, i),
                        &v,
                        NULL
                );
                gX();
        }

        return v;
}

static Value
array_scan_left(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.scan()", 1, 2);

        if (vN(*array->array) == 0) {
                return *array;
        }

        Value f;

        if (argc == 1) {
                f = ARG(0);
        } else {
                vvI(*array->array, ARG(0), 0);
                f = ARG(1);
        }

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        usize n = vN(*array->array);
        Value v = v__(*array->array, 0);

        for (usize i = 1; i < n; ++i) {
                gP(&v);
                v = vm_eval_function(ty, &f, &v, v_(*array->array, i), NULL);
                *v_(*array->array, i) = v;
                gX();
        }

        return *array;
}

static Value
array_scan_right(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.scanr()", 1, 2);

        if (vN(*array->array) == 0) {
                return *array;
        }

        Value f;

        if (argc == 1) {
                f = ARG(0);
        } else {
                vvP(*array->array, ARG(0));
                f = ARG(1);
        }

        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        Value v = v_L(*array->array);

        for (isize i = (isize)vN(*array->array) - 2; i >= 0; --i) {
                gP(&v);
                v = vm_eval_function(ty, &f, v_(*array->array, i), &v, NULL);
                *v_(*array->array, i) = v;
                gX();
        }

        return *array;
}

static Value
array_reverse(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.reverse()", 0, 1, 2);

        isize lo;
        isize n;

        if (argc > 0) {
                lo = INT_ARG(0);
                if (lo < 0) {
                        lo += vN(*array->array);
                }
        } else {
                lo = 0;
        }

        if (lo < 0 || lo > vN(*array->array)) {
                bP("invalid start index %zd for array with size %zu", lo, vN(*array->array));
        }

        if (argc > 1) {
                n = INT_ARG(1);
        } else {
                n = vN(*array->array) - lo;
        }

        if (n == 0) {
                return *array;
        }

        isize hi = lo + n - 1;

        if (hi >= vN(*array->array)) {
                bP(
                        "invalid count %jd for start index %jd and array of size %zu",
                        (imax)n, (imax)lo, vN(*array->array)
                );
        }

        while (lo < hi) {
                SWAP(
                        Value,
                        *v_(*array->array, lo),
                        *v_(*array->array, hi)
                );
                lo += 1;
                hi -= 1;
        }

        return *array;
}

static Value
array_rotate(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.rotate()", 0, 1);

        isize d = (argc == 1) ? INT_ARG(0) : 1;
        isize n = vN(*array->array);

        if (n == 0) {
                return *array;
        }

        d %= n;
        if (d < 0) {
                d += n;
        }

        isize cycles = gcd(n, d);
        for (isize i = 0; i < cycles; ++i) {
                Value t = v__(*array->array, i);
                isize j = i;
                for (;;) {
                        isize k = j + d;
                        if (k >= n) {
                                k -= n;
                        }
                        if (k == i) {
                                break;
                        }
                        *v_(*array->array, j) = v__(*array->array, k);
                        j = k;
                }
                *v_(*array->array, j) = t;
        }

        return *array;
}

static Value
array_sort_on(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.sortOn()", 1);

        Value f = ARG(0);
        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        if (vN(*array->array) == 0) {
                return *array;
        }

        SortContext ctx = {
                .f = f,
                .ty = ty
        };

        rqsort(vv(*array->array), vN(*array->array), sizeof (Value), compare_by, &ctx);

        return *array;
}

static Value
array_sort_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.sortBy()", 1);

        Value f = ARG(0);
        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        if (vN(*array->array) == 0) {
                return *array;
        }

        SortContext ctx = {
                .f = f,
                .ty = ty
        };

        rqsort(vv(*array->array), vN(*array->array), sizeof (Value), compare_by2, &ctx);

        return *array;
}

static Value
array_clone(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.clone()", 0);
        return ARRAY(ArrayClone(ty, array->array));
}

static Value
array_ptr(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.ptr()", 0);
        return PTR(array->array);
}

#define DEFINE_NO_MUT(name)                                                      \
        static Value                                                             \
        array_ ## name ## _no_mut(Ty *ty, Value *array, int argc, Value *kwargs) \
        {                                                                        \
                Value clone = array_clone(ty, array, 0, NULL);                   \
                gP(&clone);                                                      \
                Value result = array_ ## name(ty, &clone, argc, kwargs);         \
                gX();                                                            \
                return result;                                                   \
        }

DEFINE_NO_MUT(enumerate);
DEFINE_NO_MUT(filter);
DEFINE_NO_MUT(remove);
DEFINE_NO_MUT(group);
DEFINE_NO_MUT(group_by);
DEFINE_NO_MUT(groups_of);
DEFINE_NO_MUT(intersperse);
DEFINE_NO_MUT(map);
DEFINE_NO_MUT(window);
DEFINE_NO_MUT(reverse);
DEFINE_NO_MUT(rotate);
DEFINE_NO_MUT(scan_left);
DEFINE_NO_MUT(scan_right);
DEFINE_NO_MUT(shuffle);
DEFINE_NO_MUT(sort);
DEFINE_NO_MUT(sort_by);
DEFINE_NO_MUT(sort_on);
DEFINE_NO_MUT(uniq);
DEFINE_NO_MUT(zip);
DEFINE_NO_MUT(next_permutation);

DEFINE_METHOD_TABLE(
        array,
        { .name = "all?",              .func = array_all                     },
        { .name = "any?",              .func = array_any                     },
        { .name = "bsearch",           .func = array_bsearch_strict          },
        { .name = "bsearch?",          .func = array_bsearch                 },
        { .name = "clone",             .func = array_clone                   },
        { .name = "consumeWhile",      .func = array_consume_while           },
        { .name = "contains?",         .func = array_contains                },
        { .name = "count",             .func = array_count                   },
        { .name = "countBy",           .func = array_count_by                },
        { .name = "drop",              .func = array_drop                    },
        { .name = "drop!",             .func = array_drop_mut                },
        { .name = "dropWhile",         .func = array_drop_while              },
        { .name = "dropWhile!",        .func = array_drop_while_mut          },
        { .name = "each",              .func = array_each                    },
        { .name = "enumerate",         .func = array_enumerate_no_mut        },
        { .name = "enumerate!",        .func = array_enumerate               },
        { .name = "filter",            .func = array_filter_no_mut           },
        { .name = "filter!",           .func = array_filter                  },
        { .name = "find",              .func = array_find                    },
        { .name = "findr",             .func = array_findr                   },
        { .name = "flat",              .func = array_flat                    },
        { .name = "fold",              .func = array_fold_left               },
        { .name = "foldr",             .func = array_fold_right              },
        { .name = "group",             .func = array_group_no_mut            },
        { .name = "group!",            .func = array_group                   },
        { .name = "groupBy",           .func = array_group_by_no_mut         },
        { .name = "groupBy!",          .func = array_group_by                },
        { .name = "groupsOf",          .func = array_groups_of_no_mut        },
        { .name = "groupsOf!",         .func = array_groups_of               },
        { .name = "insert",            .func = array_insert                  },
        { .name = "intersperse",       .func = array_intersperse_no_mut      },
        { .name = "intersperse!",      .func = array_intersperse             },
        { .name = "join",              .func = array_join                    },
        { .name = "len",               .func = array_length                  },
        { .name = "map",               .func = array_map_no_mut              },
        { .name = "map!",              .func = array_map                     },
        { .name = "max",               .func = array_max                     },
        { .name = "maxBy",             .func = array_max_by                  },
        { .name = "min",               .func = array_min                     },
        { .name = "minBy",             .func = array_min_by                  },
        { .name = "nextPermutation",   .func = array_next_permutation_no_mut },
        { .name = "nextPermutation!",  .func = array_next_permutation        },
        { .name = "partition",         .func = array_partition_no_mut        },
        { .name = "partition!",        .func = array_partition               },
        { .name = "pop",               .func = array_pop                     },
        { .name = "ptr",               .func = array_ptr                     },
        { .name = "push",              .func = array_push                    },
        { .name = "remove",            .func = array_remove_no_mut           },
        { .name = "remove!",           .func = array_remove                  },
        { .name = "reverse",           .func = array_reverse_no_mut          },
        { .name = "reverse!",          .func = array_reverse                 },
        { .name = "rotate",            .func = array_rotate_no_mut           },
        { .name = "rotate!",           .func = array_rotate                  },
        { .name = "scan",              .func = array_scan_left_no_mut        },
        { .name = "scan!",             .func = array_scan_left               },
        { .name = "scanr",             .func = array_scan_right_no_mut       },
        { .name = "scanr!",            .func = array_scan_right              },
        { .name = "search",            .func = array_search                  },
        { .name = "searchBy",          .func = array_search_by               },
        { .name = "searchr",           .func = array_searchr                 },
        { .name = "searchrBy",         .func = array_searchr_by              },
        { .name = "set",               .func = array_set                     },
        { .name = "shuffle",           .func = array_shuffle_no_mut          },
        { .name = "shuffle!",          .func = array_shuffle                 },
        { .name = "slice",             .func = array_slice                   },
        { .name = "slice!",            .func = array_splice                  },
        { .name = "sort",              .func = array_sort_no_mut             },
        { .name = "sort!",             .func = array_sort                    },
        { .name = "sortBy",            .func = array_sort_by_no_mut          },
        { .name = "sortBy!",           .func = array_sort_by                 },
        { .name = "sortOn",            .func = array_sort_on_no_mut          },
        { .name = "sortOn!",           .func = array_sort_on                 },
        { .name = "splice",            .func = array_splice                  },
        { .name = "split",             .func = array_split_at                },
        { .name = "sum",               .func = array_sum                     },
        { .name = "swap",              .func = array_swap                    },
        { .name = "take",              .func = array_take                    },
        { .name = "take!",             .func = array_take_mut                },
        { .name = "takeWhile",         .func = array_take_while              },
        { .name = "takeWhile!",        .func = array_take_while_mut          },
        { .name = "tally",             .func = array_tally                   },
        { .name = "tuple",             .func = array_tuple                   },
        { .name = "uniq",              .func = array_uniq_no_mut             },
        { .name = "uniq!",             .func = array_uniq                    },
        { .name = "window",            .func = array_window_no_mut           },
        { .name = "window!",           .func = array_window                  },
        { .name = "zip",               .func = array_zip_no_mut              },
        { .name = "zip!",              .func = array_zip                     },
);

DEFINE_METHOD_LOOKUP(array)
DEFINE_METHOD_TABLE_BUILDER(array)
DEFINE_METHOD_COMPLETER(array)
