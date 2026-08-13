#include <stdlib.h>
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
        return value_compare(ty, v1, v2);
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

        int result = value_compare(ty, &k1, &k2);

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

        if (V_TYPE(v) == VALUE_INTEGER)
                result = V_Z(v);
        else
                result = value_truthy(ty, &v) ? 1 : -1;

        gX();

        return result;
}

inline static void
shrink(Ty *ty, Value *v)
{
        Array *a = V_ARRAY(*(v));

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
        vvPn(*V_ARRAY(*array), &ARG(0), argc);
        return NIL;
}

static Value
array_insert(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Array.insert()", 2, INT_MAX);

        imax i = INT_ARG(0);

        if (i < 0) {
                i += vN(*V_ARRAY(*array)) + 1;
        }

        if (i < 0 || i > vN(*V_ARRAY(*array))) {
                bP("index out of range: %"PRIiMAX, i);
        }

        vvIn(*V_ARRAY(*array), &ARG(1), argc - 1, i);

        return *array;
}

static Value
array_pop(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.pop()", 0, 1);

        Value v;

        if (argc == 0) {
                if (vN(*V_ARRAY(*array)) == 0) {
                        bP("empty array");
                }
                v = V_ARRAY(*(array))->items[--V_ARRAY(*(array))->count];
        } else {
                imax i = INT_ARG(0);
                if (i < 0) {
                        i += vN(*V_ARRAY(*array));
                }
                if (i < 0 || i >= vN(*V_ARRAY(*array))) {
                        bP("out of range: %"PRIiMAX, i);
                }
                v = v__(*V_ARRAY(*array), i);
                vvXi(*V_ARRAY(*array), i);
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
                i += vN(*V_ARRAY(*array));
        }
        if (j < 0) {
                j += vN(*V_ARRAY(*array));
        }

        if (
                (i < 0) || (i >= vN(*V_ARRAY(*array)))
             || (j < 0) || (j >= vN(*V_ARRAY(*array)))
        ) {
                bP("out of range: (%"PRIiMAX"), %"PRIiMAX")", i, j);
        }

        Value tmp = v__(*V_ARRAY(*array), i);
        *v_(*V_ARRAY(*array), i) = v__(*V_ARRAY(*array), j);
        *v_(*V_ARRAY(*array), j) = tmp;

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
                n = vN(*V_ARRAY(*array));
        }


        if (i < 0) {
                i += vN(*V_ARRAY(*array));
        }
        if (i < 0) {
                bP("out of range: %"PRIiMAX, i);
        }

        if (n < 0) {
                n += vN(*V_ARRAY(*array));
        }
        if (n < 0) {
                bP("bad count: %"PRIiMAX, n);
        }

        i = min(i, vN(*V_ARRAY(*array)));
        n = min(n, vN(*V_ARRAY(*array)) - i);

        Array *slice = vA();
        NOGC(slice);

        vvPn(*slice, vv(*V_ARRAY(*array)) + i, n);
        memmove(
                vv(*V_ARRAY(*array)) + i,
                vv(*V_ARRAY(*array)) + (i + n),
                (vN(*V_ARRAY(*array)) - (i + n)) * sizeof (Value)
        );
        vN(*V_ARRAY(*array)) -= n;

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

        usize n = vN(*V_ARRAY(*array));
        Value f = KWARG("f", _ANY);
        bool longest = HAVE_FLAG("longest");

        for (int i = 0; i < argc; ++i) {
                if (ARG_T(i) != VALUE_ARRAY) {
                        bP("arg%d is non-Array: %s", i, VSC(&ARG(i)));
                }
                n = longest
                  ? max(n, vN(*V_ARRAY(ARG(i))))
                  : min(n, vN(*V_ARRAY(ARG(i))));
        }

        while (vN(*V_ARRAY(*array)) < n) {
                vAp(V_ARRAY(*array), NIL);
        }

        for (usize i = 0; i < n; ++i) {
                if (IsMissing(f)) {
                        Value tuple = vT(argc + 1);
                        V_ITEMS(tuple)[0] = index_safe(V_ARRAY(*(array)), i);
                        for (int j = 0; j < argc; ++j) {
                                V_ITEMS(tuple)[j + 1] = index_safe(V_ARRAY(ARG(j)), i);
                        }
                        *v_(*V_ARRAY(*array), i) = tuple;
                } else {
                        Value v = index_safe(V_ARRAY(*(array)), i);
                        vmP(&v);
                        for (int j = 0; j < argc; ++j) {
                                v = index_safe(V_ARRAY(ARG(-1)), i);
                                vmP(&v);

                        }
                        *v_(*V_ARRAY(*array), i) = vmC(&f, argc + 1);
                }
        }

        vN(*V_ARRAY(*array)) = n;
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

        int n = max((imax)vN(*V_ARRAY(*array)) - k + 1, 0);

        if (argc == 2) {
                Value f = ARG(1);
                for (int i = 0; i < n; ++i) {
                        for (int j = i; j < i + k; ++j) {
                                vmP(v_(*V_ARRAY(*array), j));
                        }
                        *v_(*V_ARRAY(*array), i) = vmC(&f, k);
                }

        } else {
                for (int i = 0; i < n; ++i) {
                        Array *win = vAn(k);
                        for (int j = i; j < i + k; ++j) {
                                vPx(*win, v__(*V_ARRAY(*array), j));
                        }
                        *v_(*V_ARRAY(*array), i) =  ARRAY(win);
                }
        }

        vN(*V_ARRAY(*array)) = n;
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

        isize i = V_Z(*(_i));
        isize k = (V_TYPE(*(_k)) == VALUE_NIL) ? 1 : (V_Z(*(_k)) + !V_Z(*(_k)));

        if (k < 0) {
                isize j = (V_TYPE(*(_j)) == VALUE_NIL) ? 0 : V_Z(*(_j));
                isize start = min(iwrap(i - 1, vN(*xs)), vN(*xs) - 1);
                isize stop = max(iwrap(j, vN(*xs)), 0);
                for (isize ix = start; ix >= stop; ix += k) {
                        if (idx_ok(xs, ix)) {
                                uvP(*slice, v__(*xs, ix));
                        }
                }
        } else {
                isize j = (V_TYPE(*(_j)) == VALUE_NIL) ? vN(*xs) : V_Z(*(_j));
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
                return slice3(ty, V_ARRAY(*(array)), &_i, &_j, &_k);
        }

        imax i = INT_ARG(0);
        imax n;

        if (argc == 2) {
                n = INT_ARG(1);
        } else {
                n = vN(*V_ARRAY(*array));
        }

        if (i < 0) {
                i += vN(*V_ARRAY(*array));
        }
        if (i < 0) {
                bP("out of range: %"PRIiMAX, i);
        }

        if (n < 0) {
                n += vN(*V_ARRAY(*array));
        }
        if (n < 0) {
                bP("bad count: %"PRIiMAX, n);
        }

        i = min(i, vN(*V_ARRAY(*array)));
        n = min(n, vN(*V_ARRAY(*array)) - i);

        Array *slice = vAn(n);
        memmove(
                vv(*slice),
                vv(*V_ARRAY(*array)) + i,
                n * sizeof (Value)
        );
        vN(*slice) = n;

        return ARRAY(slice);
}

static Value
array_sort(Ty *ty, Value *array, int argc, Value *kwargs)
{
        char const *_name__ = "Array.sort()";

        int i;
        int n;

        Array const *xs = V_ARRAY(*(array));

        CHECK_ARGC(0, 1, 2);

        switch (argc) {
        case 0:
                i = 0;
                n = vN(*xs);
                break;
        case 1:
                i = INT_ARG(0);
                n = vN(*xs);
                break;
        case 2:
                i = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (i < 0) {
                i += V_ARRAY(*(array))->count;
        }

        if (n < 0 || i < 0 || i + n > vN(*xs)) {
                zP("Array.sort(): index out of range: i=%d, n=%d, #xs%d", i, n, (int)vN(*xs));
        }

        Value *by = NAMED("by");
        Value *cmp = NAMED("cmp");

        if (by != NULL && cmp != NULL) {
                zP("Array.sort(): kwargs `by` and `cmp` both specified");
        }

        SortContext ctx = {
                .ty = ty
        };

        if (by != NULL) {
                if (!CALLABLE(*by)) {
                        zP("Array.sort(): `by` not callable: %s", VSC(by));
                }
                ctx.f = *by;
                rqsort(V_ARRAY(*array)->items + i, n, sizeof (Value), compare_by, &ctx);
        } else if (cmp != NULL) {
                if (!CALLABLE(*cmp)) {
                        zP("Array.sort(): `cmp` not callable: %s", VSC(cmp));
                }
                ctx.f = *cmp;
                rqsort(V_ARRAY(*array)->items + i, n, sizeof (Value), compare_by2, &ctx);
        } else {
                rqsort(V_ARRAY(*array)->items + i, n, sizeof (Value), compare_default, ty);
        }

        Value *desc = NAMED("desc");

        if (desc != NULL && value_truthy(ty, desc)) {
                array_reverse(ty, array, argc, NULL);
        }

        return *array;
}

static Value
array_next_permutation(Ty *ty, Value *array, int argc, Value *kwargs)
{
#define CMP(i, j) value_compare(ty, &V_ARRAY(*array)->items[i], &V_ARRAY(*array)->items[j])
        if (argc != 0)
                zP("array.nextPermutation() expects no arguments but got %d", argc);

        for (int i = V_ARRAY(*(array))->count - 1; i > 0; --i) {
                if (CMP(i - 1, i) < 0) {
                        int j = i;
                        for (int k = i + 1; k < V_ARRAY(*(array))->count; ++k)
                                if (CMP(k, j) < 0 && CMP(k, i - 1) > 0)
                                        j = k;

                        Value t = V_ARRAY(*(array))->items[i - 1];
                        V_ARRAY(*(array))->items[i - 1] = V_ARRAY(*(array))->items[j];
                        V_ARRAY(*(array))->items[j] = t;

                        Value index = INTEGER(i);
                        vmP(&index);
                        array_sort(ty, array, 1, kwargs);
                        vmX();

                        return *array;
                }
        }

        return NIL;
#undef CMP
}

static Value
array_take_while_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.takeWhile!() expects 1 argument but got %d", argc);

        Value f = ARG(0);

        if (!CALLABLE(f))
                zP("non-callable predicate passed to array.takeWhile!()");

        int keep = 0;
        for (int i = 0; i < V_ARRAY(*(array))->count; ++i) {
                if (value_apply_predicate(ty, &f, &V_ARRAY(*(array))->items[i])) {
                        ++keep;
                } else {
                        break;
                }
        }

        V_ARRAY(*(array))->count = keep;
        shrink(ty, array);

        return *array;
}

static Value
array_take_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.takeWhile!()", 1);

        Value f = ARG(0);

        if (!CALLABLE(f)) {
                zP("non-callable predicate passed to array.takeWhile!()");
        }

        int keep = 0;
        for (int i = 0; i < vN(*V_ARRAY(*array)); ++i) {
                if (value_apply_predicate(ty, &f, v_(*V_ARRAY(*array), i))) {
                        keep += 1;
                } else {
                        break;
                }
        }

        Value result = ARRAY(vA());
        NOGC(V_ARRAY(result));
        value_array_reserve(ty, V_ARRAY(result), keep);
        OKGC(V_ARRAY(result));
        memmove(V_ARRAY(result)->items, V_ARRAY(*array)->items, keep * sizeof (Value));
        V_ARRAY(result)->count = keep;

        return result;
}

static Value
array_drop_while_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.dropWhile!() expects 1 argument but got %d", argc);

        Value f = ARG(0);

        if (!CALLABLE(f))
                zP("non-callable predicate passed to array.dropWhile!()");

        int drop = 0;
        for (int i = 0; i < V_ARRAY(*(array))->count; ++i)
                if (value_apply_predicate(ty, &f, &V_ARRAY(*(array))->items[i]))
                        ++drop;
                else
                        break;

        memmove(V_ARRAY(*array)->items, V_ARRAY(*array)->items + drop, (V_ARRAY(*array)->count - drop) * sizeof (Value));
        V_ARRAY(*(array))->count -= drop;
        shrink(ty, array);

        return *array;
}

static Value
array_drop_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.dropWhile() expects 1 argument but got %d", argc);

        Value f = ARG(0);

        if (!CALLABLE(f))
                zP("non-callable predicate passed to array.dropWhile()");

        int drop = 0;
        for (int i = 0; i < V_ARRAY(*(array))->count; ++i)
                if (value_apply_predicate(ty, &f, &V_ARRAY(*(array))->items[i]))
                        ++drop;
                else
                        break;

        int n = V_ARRAY(*(array))->count - drop;
        Value result = ARRAY(vA());
        NOGC(V_ARRAY(result));
        value_array_reserve(ty, V_ARRAY(result), n);
        OKGC(V_ARRAY(result));
        memmove(V_ARRAY(result)->items, V_ARRAY(*array)->items + drop, n * sizeof (Value));
        V_ARRAY(result)->count = n;

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
        for (usize i = 0; i < vN(*V_ARRAY(*array)); ++i) {
                Value e = v__(*V_ARRAY(*array), i);
                Value k = !IsNone(f)  ? vm_eval_function(ty, &f, &e, NULL) : e;
                Value *v = dict_put_key_if_not_exists(ty, V_DICT(d), k);
                if (V_TYPE(*(v)) == VALUE_NIL) {
                        *v = e;
                        *v_(*V_ARRAY(*array), n++) = e;
                }
        }

        gX();
        vN(*V_ARRAY(*array)) = n;

        return *array;
}

static Value
array_take_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.take!() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (V_TYPE(n) != VALUE_INTEGER)
                zP("non-integer passed to array.take!()");

        V_ARRAY(*(array))->count = (V_Z(n) < 0) ? 0 : min(V_ARRAY(*(array))->count, V_Z(n));
        shrink(ty, array);

        return *array;
}

static Value
array_take(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.take() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (V_TYPE(n) != VALUE_INTEGER)
                zP("non-integer passed to array.take!()");

        Value result = ARRAY(vA());

        int count = (V_Z(n) < 0) ? 0 : min(V_Z(n), V_ARRAY(*(array))->count);

        NOGC(V_ARRAY(result));
        value_array_reserve(ty, V_ARRAY(result), count);
        OKGC(V_ARRAY(result));

        memmove(V_ARRAY(result)->items, V_ARRAY(*array)->items, count * sizeof (Value));
        V_ARRAY(result)->count = count;

        return result;
}

static Value
array_drop_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.drop!() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (V_TYPE(n) != VALUE_INTEGER)
                zP("non-integer passed to array.drop!()");

        int d = min(V_ARRAY(*(array))->count, max(V_Z(n), 0));

        memmove(V_ARRAY(*array)->items, V_ARRAY(*array)->items + d, (V_ARRAY(*array)->count - d) * sizeof (Value));
        V_ARRAY(*(array))->count -= d;
        shrink(ty, array);

        return *array;
}

static Value
array_drop(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.drop()", 1);

        imax n = INT_ARG(0);

        int d = min(max(n, 0), V_ARRAY(*(array))->count);
        int count = V_ARRAY(*(array))->count - d;

        Array *result = vAn(count);
        memcpy(vv(*result), vv(*V_ARRAY(*array)) + d, count * sizeof (Value));
        vN(*result) = count;

        return ARRAY(result);
}

static Value
array_sum(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.sum()", 0, 1);

        Value zero = (argc == 1) ? ARG(0) : NIL;

        if (vN(*V_ARRAY(*array)) == 0) {
                return zero;
        }

        isize i0;
        Value sum;

        if (argc == 1) {
                sum = zero;
                i0 = 0;
        } else {
                sum = v__(*V_ARRAY(*array), 0);
                i0 = 1;
        }

        Value val;

        for (isize i = i0; i < vN(*V_ARRAY(*array)); ++i) {
                gP(&sum);
                val = v__(*V_ARRAY(*array), i);
                sum = vm_2op(ty, OP_ADD, &sum, &val);
                gX();
        }

        return sum;
}

static Value
array_join(Ty *ty, Value *array, int argc, Value *kwargs)
{
        char const *_name__ = "Array.join()";

        CHECK_ARGC(0, 1);

        if (vN(*V_ARRAY(*array)) == 0) {
                return STRING_EMPTY;
        }

        Value sep;
        if (argc == 0) {
                sep = STRING_EMPTY;
        } else {
                sep = ARGx(0, VALUE_STRING);
        }

        vmP(v_(*V_ARRAY(*array), 0));
        Value sum = builtin_str(ty, 1, NULL);
        vmX();
        Value v = NIL;

        gP(&sep);
        for (int i = 1; i < V_ARRAY(*(array))->count; ++i) {
                gP(&sum);
                gP(&v);
                vmP(v_(*V_ARRAY(*array), i));
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
        gX();

        return sum;
}

static Value
array_consume_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 2)
                zP("array.consumeWhile() expects 2 arguments but got %d", argc);

        Value f = ARG(0);
        Value p = ARG(1);

        if (!CALLABLE(f)) {
                zP("Array.consumeWhile(): source is not callable: %s", VSC(&f));
        }

        if (!CALLABLE(p)) {
                zP("Array.consumeWhile(): non-callable passed as predicate: %s", VSC(&p));
        }

        Value v = NIL;

        for (;;) {
                v = vm_eval_function(ty, &f, NULL);
                gP(&v);
                bool more = value_apply_predicate(ty, &p, &v);
                if (more) {
                        vAp(V_ARRAY(*array), v);
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

        Value size = ARG(0);
        if (V_TYPE(size) != VALUE_INTEGER)
                zP("the argument to array.groupsOf() must be an integer");

        if (V_Z(size) <= 0)
                zP("the argument to array.groupsOf() must be positive");

        bool keep_short = true;

        if (argc == 2) {
                if (V_TYPE(ARG(1)) != VALUE_BOOLEAN) {
                        zP("the second argument to array.groupsOf() must be a boolean");
                }
                keep_short = V_BOOL(ARG(1));
        }

        int n = 0;
        int i = 0;
        while (i + V_Z(size) <= V_ARRAY(*(array))->count) {
                Array *group = vA();
                NOGC(group);
                vvPn(*group, V_ARRAY(*array)->items + i, V_Z(size));
                OKGC(group);
                *v_(*V_ARRAY(*array), n++) = ARRAY(group);
                i += V_Z(size);
        }

        if (keep_short && i != V_ARRAY(*(array))->count) {
                Array *last = vA();
                NOGC(last);
                vvPn(*last, V_ARRAY(*array)->items + i, V_ARRAY(*array)->count - i);
                OKGC(last);
                V_ARRAY(*(array))->items[n++] = ARRAY(last);
        }

        V_ARRAY(*(array))->count = n;
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

        int len = 0;
        for (int i = 0; i < V_ARRAY(*(array))->count; ++i) {
                Value group = ARRAY(vA());
                NOGC(V_ARRAY(group));
                Value e = V_ARRAY(*(array))->items[i];
                v1 = vm_call1(ty, &f, &e);
                gP(&v1);
                vAp(V_ARRAY(group), e);
                while (i + 1 < V_ARRAY(*(array))->count) {
                        v2 = vm_call1(ty, &f, &V_ARRAY(*(array))->items[i + 1]);
                        gP(&v2);
                        if (value_test_equality(ty, &v1, &v2)) {
                                vAp(V_ARRAY(group), V_ARRAY(*array)->items[++i]);
                                gX();
                        } else {
                                gX();
                                break;
                        }
                }
                gX();
                OKGC(V_ARRAY(group));
                V_ARRAY(*(array))->items[len++] = group;
        }

        V_ARRAY(*(array))->count = len;
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

        int len = 0;
        for (int i = 0; i < V_ARRAY(*(array))->count; ++i) {
                Value group = ARRAY(vA());
                NOGC(V_ARRAY(group));
                vAp(V_ARRAY(group), V_ARRAY(*array)->items[i]);
                while (
                        (i + 1 < V_ARRAY(*(array))->count)
                     && v_eq(&V_ARRAY(*array)->items[i], &V_ARRAY(*array)->items[i + 1])
                ) {
                        vAp(V_ARRAY(group), V_ARRAY(*array)->items[++i]);
                }
                OKGC(V_ARRAY(group));
                V_ARRAY(*(array))->items[len++] = group;
        }

        V_ARRAY(*(array))->count = len;
        shrink(ty, array);

        return *array;
}

static Value
array_intersperse(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the intersperse method on arrays expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = V_ARRAY(*(array))->count - 1;
        if (n < 1)
                return *array;

        int newcount = 2 * n + 1;
        value_array_reserve(ty, V_ARRAY(*(array)), newcount);
        memcpy(V_ARRAY(*array)->items + n + 1, V_ARRAY(*array)->items + 1, n * sizeof (Value));

        int lo = 1;
        int hi = n + 1;
        for (int i = 0; i < n; ++i) {
                V_ARRAY(*(array))->items[lo++] = v;
                V_ARRAY(*(array))->items[lo++] = V_ARRAY(*(array))->items[hi++];
        }

        V_ARRAY(*(array))->count = newcount;
        return *array;
}

static Value
array_min(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc == 1)
                return array_min_by(ty, array, argc, kwargs);

        if (argc != 0)
                zP("the min method on arrays expects no arguments but got %d", argc);

        if (V_ARRAY(*(array))->count == 0)
                return NIL;

        Value min, v;
        min = V_ARRAY(*(array))->items[0];

        for (int i = 1; i < V_ARRAY(*(array))->count; ++i) {
                v = V_ARRAY(*(array))->items[i];
                if (value_compare(ty, &v, &min) < 0)
                        min = v;
        }

        return min;
}

static Value
array_min_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the minBy method on arrays expects 1 argument but got %d", argc);

        if (V_ARRAY(*(array))->count == 0)
                return NIL;

        Value f = ARG(0);
        if (!CALLABLE(f))
                zP("non-function passed to the minBy method on array");

        Value min, v, k, r;
        min = V_ARRAY(*(array))->items[0];

        r = k = NIL;

        if (V_TYPE(f) == VALUE_FUNCTION && V_INFO(f)[2] > 1) {
                for (int i = 1; i < V_ARRAY(*(array))->count; ++i) {
                        v = V_ARRAY(*(array))->items[i];
                        r = vm_eval_function(ty, &f, &v, &min, NULL);
                        gP(&r);
                        if (
                                (V_TYPE(r) != VALUE_INTEGER && !value_truthy(ty, &r))
                             || (V_Z(r) < 0)
                        ) {
                                min = v;
                        }
                        gX();
                }
        } else {
                k = vm_eval_function(ty, &f, &min, NULL);
                gP(&k);
                for (int i = 1; i < V_ARRAY(*(array))->count; ++i) {
                        v = V_ARRAY(*(array))->items[i];
                        r = vm_eval_function(ty, &f, &v, NULL);
                        gP(&r);
                        if (value_compare(ty, &r, &k) < 0) {
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
        char const *_name__ = "Array.max()";

        if (argc == 1) {
                return array_max_by(ty, array, argc, kwargs);
        }

        CHECK_ARGC(0);

        if (vN(*V_ARRAY(*array)) == 0) {
                return NIL;
        }

        Value max, v;
        max = v__(*V_ARRAY(*array), 0);

        for (int i = 1; i < vN(*V_ARRAY(*array)); ++i) {
                v = v__(*V_ARRAY(*array), i);
                if (value_compare(ty, &v, &max) > 0) {
                        max = v;
                }
        }

        return max;
}

static Value
array_max_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.max-by()", 1);

        if (vN(*V_ARRAY(*array)) == 0) {
                return NIL;
        }

        Value f = ARG(0);
        if (!CALLABLE(f)) {
                bP("not callable: %s", VSC(&f));
        }

        Value max, v, k, r;
        max = V_ARRAY(*(array))->items[0];

        k = r = NIL;

        if (V_TYPE(f) == VALUE_FUNCTION && V_INFO(f)[2] > 1) {
                for (int i = 1; i < V_ARRAY(*(array))->count; ++i) {
                        v = V_ARRAY(*(array))->items[i];
                        r = vm_eval_function(ty, &f, &v, &max, NULL);
                        gP(&r);
                        if (
                                (V_TYPE(r) != VALUE_INTEGER && value_truthy(ty, &r))
                             || (V_Z(r) > 0)
                        ) {
                                max = v;
                        }
                        gX();

                }
        } else {
                k = vm_eval_function(ty, &f, &max, NULL);
                        gP(&k);
                for (int i = 1; i < V_ARRAY(*(array))->count; ++i) {
                        v = V_ARRAY(*(array))->items[i];
                        r = vm_eval_function(ty, &f, &v, NULL);
                        gP(&r);
                        if (value_compare(ty, &r, &k) > 0) {
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
        return INTEGER(vN(*V_ARRAY(*array)));
}

static Value
array_shuffle(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("the shuffle! method on arrays expects no arguments but got %d", argc);

        Value t;
        int n = V_ARRAY(*(array))->count;
        for (int i = n - 1; i > 0; --i) {
                int j = rand() % (i + 1);
                t = V_ARRAY(*(array))->items[i];
                V_ARRAY(*(array))->items[i] = V_ARRAY(*(array))->items[j];
                V_ARRAY(*(array))->items[j] = t;
        }

        return *array;
}

static Value
array_map(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.map()", 1);

        Value f = ARG(0);
        usize n = vN(*V_ARRAY(*array));

        for (usize i = 0; i < n; ++i) {
                Value x = v__(*V_ARRAY(*array), i);
                Value y = vm_call1(ty, &f, &x);
                *v_(*V_ARRAY(*array), i) = y;
        }

        return *array;
}

static Value
array_enumerate(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.enumerate()", 0);

        usize n = vN(*V_ARRAY(*array));

        for (int i = 0; i < n; ++i) {
                Value entry = PAIR(
                        INTEGER(i),
                        v__(*V_ARRAY(*array), i)
                );
                *v_(*V_ARRAY(*array), i) =  entry;
        }

        return *array;
}

static Value
array_remove(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.remove()", 1);

        Value v = ARG(0);

        isize n = vN(*V_ARRAY(*array));
        isize j = 0;
        for (int i = 0; i < n; ++i) {
                if (!v_eq(&v, &V_ARRAY(*array)->items[i])) {
                        *v_(*V_ARRAY(*array), j++) = v__(*V_ARRAY(*array), i);
                }
        }

        vN(*V_ARRAY(*array)) = j;
        shrink(ty, array);

        return *array;
}

static Value
array_filter(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.filter()", 1);

        Value pred = ARG(0);

        usize n0 = vN(*V_ARRAY(*array));
        usize n = 0;
        for (usize i = 0; i < n0; ++i) {
                Value x = v__(*V_ARRAY(*array), i);
                if (value_apply_predicate(ty, &pred, &x)) {
                        *v_(*V_ARRAY(*array), n++) = x;
                }
        }

        vN(*V_ARRAY(*array)) = n;
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

        isize n = vN(*V_ARRAY(*array));
        for (int i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i])) {
                        return V_ARRAY(*(array))->items[i];
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

        isize n = vN(*V_ARRAY(*array));
        for (int i = n - 1; i >= 0; --i) {
                if (value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i])) {
                        return V_ARRAY(*(array))->items[i];
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
             hi = vN(*V_ARRAY(*array)) - 1;

        while (lo <= hi) {
                isize m = (lo + hi) / 2;
                int c = value_compare(ty, &v, &V_ARRAY(*(array))->items[m]);
                if      (c < 0) { hi = m - 1; i = m;  }
                else if (c > 0) { lo = m + 1; i = lo; }
                else            { return INTEGER(m);  }
        }

        return INTEGER(i);
}

static Value
array_bsearch_strict(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.bsearch!()", 1);

        Value v = ARG(0);

        isize lo = 0,
              hi = vN(*V_ARRAY(*array)) - 1;

        while (lo <= hi) {
                isize m = (lo + hi) / 2;
                int c = value_compare(ty, &v, &V_ARRAY(*(array))->items[m]);
                if      (c < 0) hi = m - 1;
                else if (c > 0) lo = m + 1;
                else            return INTEGER(m);
        }

        return NIL;
}

static Value
array_search_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the searchBy method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the searchBy method on array");

        int n = V_ARRAY(*(array))->count;
        for (int i = 0; i < n; ++i)
                if (value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i]))
                        return INTEGER(i);

        return NIL;
}

static Value
array_searchr_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the searchrBy method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the searchBy method on array");

        int n = V_ARRAY(*(array))->count;
        for (int i = n - 1; i >= 0; --i)
                if (value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i]))
                        return INTEGER(i);

        return NIL;
}

static Value
array_set(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("array.set() expects 0 arguments but got %d", argc);

        Dict *d = dict_new(ty);
        NOGC(d);

        for (int i = 0; i < V_ARRAY(*(array))->count; ++i) {
                dict_put_key_if_not_exists(ty, d, V_ARRAY(*(array))->items[i]);
        }

        OKGC(d);

        return DICT(d);
}

static Value
array_partition(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("Array.partition!(): expected 1 argument but got %d", argc);
        }

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                zP("Array.partition!(): expected callable arg0 but got: %s", VSC(&pred));
        }

        Array const *xs = V_ARRAY(*(array));

        if (vN(*xs) == 0) {
                return *array;
        }

        int y = 0;
        int n = vN(*xs);

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
        if (argc != 1) {
                zP("array.split()  expects 1 argument but got %d", argc);
        }

        if (V_TYPE(ARG(0)) != VALUE_INTEGER) {
                zP(
                        "array.split() expected integer but got %s%s%s%s",
                        TERM(96),
                        TERM(1),
                        SHOW(&ARG(0)),
                        TERM(0)
                );
        }

        int i = V_Z(ARG(0));

        if (i < 0)
                i += V_ARRAY(*(array))->count;

        if (i < 0 || i > V_ARRAY(*(array))->count) {
                zP("array.split(): index %s%d%s out of range", TERM(96), i, TERM(0));
        }

        Array *front = vA();
        NOGC(front);

        Array *back = vA();
        NOGC(back);

        vvPn(*front, vv(*V_ARRAY(*array)), i);
        vvPn(*back, vv(*V_ARRAY(*array)) + i, vN(*V_ARRAY(*array)) - i);

        Value pair = PAIR(ARRAY(front), ARRAY(back));

        OKGC(front);
        OKGC(back);

        return pair;
}

static Value
array_partition_no_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("Array.partition(): expected 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred)) {
                zP("Array.partition(): expected callable but got: %s", VSC(&pred));
        }

        int n = V_ARRAY(*(array))->count;

        Array *yes = vA();
        NOGC(yes);

        Array *no = vA();
        NOGC(no);

        for (int i = 0; i < n; ++i) {
                Value *v = v_(*V_ARRAY(*array), i);
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
        if (argc != 1)
                zP("array.contains?() expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = V_ARRAY(*(array))->count;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(ty, &v, &V_ARRAY(*(array))->items[i]))
                        return BOOLEAN(true);

        return BOOLEAN(false);
}

static Value
array_tuple(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("array.tuple() expects 0 arguments but got %d", argc);
        }

        int n = V_ARRAY(*(array))->count;

        Value v = vT(n);
        memcpy(V_ITEMS(v), V_ARRAY(*array)->items, n * sizeof (Value));

        return v;
}

static Value
array_tally(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0 && argc != 1)
                zP("array.tally() expects 0 or 1 argument(s) but got %d", argc);

        Value d = DICT(dict_new(ty));
        gP(&d);

        if (argc == 0) {
                for (int i = 0; i < V_ARRAY(*(array))->count; ++i) {
                        Value *c = dict_get_value(ty, V_DICT(d), &V_ARRAY(*(array))->items[i]);
                        if (c == NULL) {
                                dict_put_value(ty, V_DICT(d), V_ARRAY(*(array))->items[i], INTEGER(1));
                        } else {
                                *c = INTEGER(V_Z(*c) + 1);
                        }
                }
        } else {
                Value f = ARG(0);
                if (!CALLABLE(f))
                        zP("non-callable passed to array.tally()");

                for (int i = 0; i < V_ARRAY(*(array))->count; ++i) {
                        Value v = vm_call1(ty, &f, &V_ARRAY(*(array))->items[i]);
                        Value *c = dict_get_value(ty, V_DICT(d), &v);
                        if (c == NULL) {
                                dict_put_value(ty, V_DICT(d), v, INTEGER(1));
                        } else {
                                *c = INTEGER(V_Z(*c) + 1);
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

        usize n = vN(*V_ARRAY(*array));
        for (usize i = 0; i < n; ++i) {
                if (v_eq(&v, v_(*V_ARRAY(*array), i))) {
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

        usize n = vN(*V_ARRAY(*array));
        for (usize i = n - 1; i >= 0; --i) {
                if (v_eq(&v, v_(*V_ARRAY(*array), i))) {
                        return INTEGER(i);
                }
        }

        return NIL;
}

static Value
array_flat(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.flat()", 0, 1);

        vec(Value *) stack = {0};
        vec(usize)  dstack = {0};

        usize maxdepth;

        if (argc == 1) {
                maxdepth = INT_ARG(0);
        } else {
                maxdepth = INT_MAX;
        }

        SCRATCH_SAVE();

        Array *r = vA();
        NOGC(r);

        usize n = vN(*V_ARRAY(*array));
        for (usize i = 0; i < n; ++i) {
                svP(stack, v_(*V_ARRAY(*array), i));
                svP(dstack, 1);
                while (vN(stack) > 0) {
                        Value *v = vXx(stack);
                        usize d = vXx(dstack);
                        if (V_TYPE(*(v)) != VALUE_ARRAY || d > maxdepth) {
                                vAp(r, *v);
                        } else {
                                for (isize i = vN(*V_ARRAY(*v)) - 1; i >= 0; --i) {
                                        svP(stack, &V_ARRAY(*v)->items[i]);
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

                if (V_TYPE(f) != VALUE_FUNCTION && V_TYPE(f) != VALUE_BUILTIN_FUNCTION && V_TYPE(f) != VALUE_METHOD && V_TYPE(f) != VALUE_BUILTIN_METHOD)
                        zP("non-function passed to the each method on array");

                int n = V_ARRAY(*(array))->count;

                for (int i = 0; i < n; ++i) {
                        Value index = INTEGER(i);
                        vm_eval_function(ty, &f, &V_ARRAY(*array)->items[i], &index, NULL);
                }

                return *array;
        } else {
                Value v = ARG(0);
                Value f = ARG(1);

                if (V_TYPE(f) != VALUE_FUNCTION && V_TYPE(f) != VALUE_BUILTIN_FUNCTION && V_TYPE(f) != VALUE_METHOD && V_TYPE(f) != VALUE_BUILTIN_METHOD)
                        zP("non-function passed to the each method on array");

                int n = V_ARRAY(*(array))->count;

                for (int i = 0; i < n; ++i) {
                        Value index = INTEGER(i);
                        vm_eval_function(ty, &f, &v, &V_ARRAY(*array)->items[i], &index, NULL);
                }

                return v;
        }

}

static Value
array_all(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.all()", 0, 1);

        usize n = vN(*V_ARRAY(*array));

        if (argc == 0) {
                for (int i = 0; i < n; ++i) {
                        if (!value_truthy(ty, &V_ARRAY(*(array))->items[i]))
                                return BOOLEAN(false);
                }
        } else {
                Value pred = ARG(0);

                if (!CALLABLE(pred))
                        zP("non-predicate passed to the all? method on array");

                for (int i = 0; i < n; ++i) {
                        if (!value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i]))
                                return BOOLEAN(false);
                }
        }

        return BOOLEAN(true);
}

static Value
array_any(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int n = V_ARRAY(*(array))->count;

        if (argc == 0) {
                for (int i = 0; i < n; ++i)
                        if (value_truthy(ty, &V_ARRAY(*(array))->items[i]))
                                return BOOLEAN(true);
        } else if (argc == 1) {
                Value pred = ARG(0);

                if (!CALLABLE(pred))
                        zP("non-predicate passed to the any? method on array");

                for (int i = 0; i < n; ++i)
                        if (value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i]))
                                return BOOLEAN(true);
        } else {
                zP("the any? method on arrays expects 0 or 1 argument(s) but got %d", argc);
        }

        return BOOLEAN(false);
}

static Value
array_count(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the count method on arrays expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = V_ARRAY(*(array))->count;
        int k = 0;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(ty, &v, &V_ARRAY(*(array))->items[i]))
                        k += 1;

        return INTEGER(k);
}

static Value
array_count_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the count method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the count method on array");

        int n = V_ARRAY(*(array))->count;
        int k = 0;
        for (int i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, &V_ARRAY(*(array))->items[i])) {
                        k += 1;
                }
        }

        return INTEGER(k);
}

static Value
array_fold_left(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("the foldLeft method on arrays expects 1 or 2 arguments but got %d", argc);

        int start;
        Value f, v;

        if (argc == 1) {
                start = 1;
                f = ARG(0);
                if (V_ARRAY(*(array))->count == 0) {
                        zP("foldLeft called on empty array with 1 argument");
                }
                v = V_ARRAY(*(array))->items[0];
        } else {
                start = 0;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f))
                zP("non-function passed to the foldLeft method on array");

        int n = V_ARRAY(*(array))->count;
        for (int i = start; i < n; ++i) {
                gP(&v);
                v = vm_eval_function(ty, &f, &v, &V_ARRAY(*(array))->items[i], NULL);
                gX();
        }

        return v;
}

/* TODO: fix this */
static Value
array_fold_right(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2) {
                zP("Array.foldRight(): expected 1 or 2 arguments but got %d", argc);
        }

        int start;
        Value f, v;

        if (argc == 1) {
                start = V_ARRAY(*(array))->count - 2;
                f = ARG(0);
                if (V_ARRAY(*(array))->count == 0) {
                        zP("Array.foldRight(): empty array and no start value");
                }
                v = V_ARRAY(*(array))->items[start + 1];
        } else {
                start = V_ARRAY(*(array))->count - 1;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f)) {
                zP("Array.foldRight(): expected callable but got: %s", VSC(&f));
        }

        for (int i = start; i >= 0; --i) {
                gP(&v);
                v = vm_eval_function(
                        ty,
                        &f,
                        &V_ARRAY(*(array))->items[i],
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

        if (vN(*V_ARRAY(*array)) == 0) {
                return *array;
        }

        Value f;

        if (argc == 1) {
                f = ARG(0);
        } else {
                vvI(*V_ARRAY(*array), ARG(0), 0);
                f = ARG(1);
        }

        if (!CALLABLE(f)) {
                zP("Array.scan(): expected callable but got: %s", VSC(&f));
        }

        usize n = vN(*V_ARRAY(*array));
        Value v = v__(*V_ARRAY(*array), 0);

        for (usize i = 1; i < n; ++i) {
                gP(&v);
                v = vm_eval_function(ty, &f, &v, v_(*V_ARRAY(*array), i), NULL);
                *v_(*V_ARRAY(*array), i) = v;
                gX();
        }

        return *array;
}

static Value
array_scan_right(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.scanr()", 1, 2);

        if (vN(*V_ARRAY(*array)) == 0) {
                return *array;
        }

        Value f;

        if (argc == 1) {
                f = ARG(0);
        } else {
                vvP(*V_ARRAY(*array), ARG(0));
                f = ARG(1);
        }

        if (!CALLABLE(f)) {
                zP("Array.scanr(): expected callable but got: %s", VSC(&f));
        }

        Value v = v_L(*V_ARRAY(*array));

        for (isize i = vN(*V_ARRAY(*array)) - 2; i >= 0; --i) {
                gP(&v);
                v = vm_eval_function(ty, &f, v_(*V_ARRAY(*array), i), &v, NULL);
                *v_(*V_ARRAY(*array), i) = v;
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
                        lo += vN(*V_ARRAY(*array));
                }
        } else {
                lo = 0;
        }

        if (lo < 0 || lo > vN(*V_ARRAY(*array))) {
                bP("invalid start index %zd for array with size %zu", lo, vN(*V_ARRAY(*array)));
        }

        if (argc > 1) {
                n = INT_ARG(1);
        } else {
                n = vN(*V_ARRAY(*array)) - lo;
        }

        if (n == 0) {
                return *array;
        }

        isize hi = lo + n - 1;

        if (hi >= vN(*V_ARRAY(*array))) {
                bP(
                        "invalid count %jd for start index %jd and array of size %zu",
                        n, lo, vN(*V_ARRAY(*array))
                );
        }

        while (lo < hi) {
                SWAP(
                        Value,
                        *v_(*V_ARRAY(*array), lo),
                        *v_(*V_ARRAY(*array), hi)
                );
                lo += 1;
                hi -= 1;
        }

        return *array;
}

static Value
array_rotate(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int d = 1;
        int n = V_ARRAY(*(array))->count;

        if (argc == 1) {
                Value amount = ARG(0);
                if (V_TYPE(amount) != VALUE_INTEGER)
                        zP("the argument to array.rotate() must be an integer");
                d = V_Z(amount);
        } else if (argc != 0) {
                zP("the rotate method on arrays expects 0 or 1 arguments but got %d", argc);
        }

        if (n == 0)
                return *array;

        d %= n;
        if (d < 0)
                d += n;

        int N = gcd(n, d);
        int i, j, k;
        for (i = 0; i < N; ++i) {
                Value t = V_ARRAY(*(array))->items[i];
                j = i;
                for (;;) {
                        k = j + d;
                        if (k >= n)
                                k = k - n;
                        if (k == i)
                                break;
                        V_ARRAY(*(array))->items[j] = V_ARRAY(*(array))->items[k];
                        j = k;

                }
                V_ARRAY(*(array))->items[j] = t;
        }

        return *array;
}

static Value
array_sort_on(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("Array.sortOn() expects 1 argument but got %d", argc);

        Value f = ARG(0);
        if (!CALLABLE(f))
                zP("non-function passed to the Array.sortOn()");

        if (V_ARRAY(*(array))->count == 0)
                return *array;

        SortContext ctx = {
                .f = f,
                .ty = ty
        };

        rqsort(V_ARRAY(*array)->items, V_ARRAY(*array)->count, sizeof (Value), compare_by, &ctx);

        return *array;
}

static Value
array_sort_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("Array.sortBy() expects 1 argument but got %d", argc);

        Value f = ARG(0);
        if (!CALLABLE(f))
                zP("non-function passed to the Array.sortBy()");

        if (V_ARRAY(*(array))->count == 0)
                return *array;

        SortContext ctx = {
                .f = f,
                .ty = ty
        };

        rqsort(V_ARRAY(*array)->items, V_ARRAY(*array)->count, sizeof (Value), compare_by2, &ctx);

        return *array;
}

static Value
array_clone(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.clone()", 0);
        return ARRAY(ArrayClone(ty, V_ARRAY(*array)));
}

static Value
array_ptr(Ty *ty, Value *array, int argc, Value *kwargs)
{
        ASSERT_ARGC("Array.ptr()", 0);
        return PTR(V_ARRAY(*array));
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
        { .name = "has?",              .func = array_contains                },
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
