#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "log.h"
#include "functions.h"
#include "operators.h"
#include "util.h"
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
#if defined(__APPLE__)
compare_default(void *ty, void const *v1, void const *v2)
#elif defined(__linux__)
compare_default(void const *v1, void const *v2, void *ty)
#endif
{
        return value_compare(ty, v1, v2);
}

#if defined(__APPLE__)
#define rqsort(base, nel, width, cmp, ctx) qsort_r(base, nel, width, ctx, cmp);
#elif defined(__linux__)
#define rqsort(base, nel, width, cmp, ctx) qsort_r(base, nel, width, cmp, ctx);
#else
#endif

static int
#if defined(__APPLE__)
compare_by(void *ctx_, void const *v1, void const *v2)
#elif defined(__linux__)
compare_by(void const *v1, void const *v2, void *ctx_)
#endif
{
        SortContext *ctx = ctx_;
        Ty *ty = ctx->ty;

        Value k1 = value_apply_callable(ty, &ctx->f, (Value *)v1);
        gP(&k1);

        Value k2 = value_apply_callable(ty, &ctx->f, (Value *)v2);
        gP(&k2);

        int result = value_compare(ty, &k1, &k2);

        gX();
        gX();

        return result;
}

static int
#if defined(__APPLE__)
compare_by2(void *ctx_, void const *v1, void const *v2)
#elif defined(__linux__)
compare_by2(void const *v1, void const *v2, void *ctx_)
#endif
{
        SortContext *ctx = ctx_;
        Ty *ty = ctx->ty;

        Value v = vm_eval_function(ty, &ctx->f, v1, v2, NULL);
        gP(&v);

        int result;

        if (v.type == VALUE_INTEGER)
                result = v.integer;
        else
                result = value_truthy(ty, &v) ? 1 : -1;

        gX();

        return result;
}

inline static void
shrink(Ty *ty, Value *array)
{
        if (array->array->capacity > 8 * array->array->count || (array->array->capacity - array->array->count) > 1000) {
                array->array->capacity = array->array->count;
                if (array->array->count == 0)
                        mF(array->array->items), array->array->items = NULL;
                else
                        mREu(array->array->items, array->array->count * sizeof (Value));
        }
}

static Value
array_push(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the push method on arrays expects 1 argument but got %d", argc);

        vAp(array->array, ARG(0));

        return NIL;
}

static Value
array_insert(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 2)
                zP("the insert method on arrays expects 2 arguments but got %d", argc);

        Value i = ARG(0);
        Value v = ARG(1);

        if (i.type != VALUE_INTEGER)
                zP("non-integer passed as the index to the insert method on array");

        int index = i.integer;

        if (index < 0)
                index += array->array->count + 1;
        if (index < 0 || index > array->array->count)
                zP("array index passed to insert is out of range: %d", index);

        vAp(array->array, NIL);

        memmove(array->array->items + index + 1, array->array->items + index, (array->array->count - index - 1) * sizeof (Value));
        array->array->items[index] = v;

        return *array;
}

static Value
array_pop(Ty *ty, Value *array, int argc, Value *kwargs)
{
        Value result;

        if (argc == 0) {
                if (array->array->count == 0)
                        zP("attempt to pop from an empty array");
                result = array->array->items[--array->array->count];
        } else if (argc == 1) {
                Value arg = ARG(0);
                if (arg.type != VALUE_INTEGER)
                        zP("the argument to pop must be an integer");
                if (arg.integer < 0)
                        arg.integer += array->array->count;
                if (arg.integer < 0 || arg.integer >= array->array->count)
                        zP("array index passed to pop is out of range");
                result = array->array->items[arg.integer];
                vvXi(*array->array, arg.integer);
        } else {
                zP("the pop method on arrays expects 0 or 1 argument(s) but got %d", argc);
        }

        shrink(ty, array);

        return result;
}

static Value
array_swap(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 2)
                zP("array.swap() expects 2 arguments but got %d", argc);

        Value i = ARG(0);
        Value j = ARG(1);

        if (i.type != VALUE_INTEGER || j.type != VALUE_INTEGER)
                zP("the arguments to array.swap() must be integers");

        if (i.integer < 0)
                i.integer += array->array->count;

        if (j.integer < 0)
                j.integer += array->array->count;

        if (i.integer < 0 || i.integer >= array->array->count
         || j.integer < 0 || j.integer >= array->array->count) {
                zP("invalid indices passed to array.swap(): (%d, %d)", (int) i.integer, (int) j.integer);
           }

        Value tmp = array->array->items[i.integer];
        array->array->items[i.integer] = array->array->items[j.integer];
        array->array->items[j.integer] = tmp;

        return *array;
}

static Value
array_slice_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("array.slice!() expects 1 or 2 arguments but got %d", argc);

        Value start = ARG(0);

        if (start.type != VALUE_INTEGER)
                zP("non-integer passed as first argument to array.slice!()");

        int s = start.integer;
        int n;

        if (argc == 2) {
                Value count = ARG(1);
                if (count.type != VALUE_INTEGER)
                        zP("non-integer passed as second argument to array.slice!()");
                n = count.integer;
        } else {
                n = array->array->count;
        }


        if (s < 0)
                s += array->array->count;
        if (s < 0)
                zP("start index passed to array.slice!() is out of range");

        if (n < 0)
                n += array->array->count;
        if (n < 0)
                zP("negative count passed to array.slice!()");

        s = min(s, array->array->count);
        n = min(n, array->array->count - s);

        struct array *slice = vA();
        NOGC(slice);

        vvPn(*slice, array->array->items + s, n);
        memmove(array->array->items + s, array->array->items + s + n, (array->array->count - (s + n)) * sizeof (Value));

        array->array->count -= n;
        shrink(ty, array);

        OKGC(slice);

        return ARRAY(slice);
}

static Value
array_zip(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc == 0 || (argc == 1 && ARG(0).type != VALUE_ARRAY)) {
                zP("array.zip() expects at least one array argument");
        }

        int ac = argc;

        Value f = NIL;
        if (ARG(ac - 1).type != VALUE_ARRAY && CALLABLE(ARG(ac - 1))) {
                f = ARG(ac - 1);
                ac -= 1;
        }

        int n = array->array->count;
        for (int i = 0; i < ac; ++i) {
                if (ARG(i).type != VALUE_ARRAY) {
                        zP("non-array passed to array.zip()");
                }
                n = min(n, ARG(i).array->count);
        }

        for (int i = 0; i < n; ++i) {
                if (f.type == VALUE_NIL) {
                        Value t = vT(ac + 1);
                        t.items[0] = array->array->items[i];
                        for (int j = 0; j < ac; ++j) {
                                t.items[j + 1] = ARG(j).array->items[i];
                        }
                        array->array->items[i] = t;
                } else {
                        vmP(&array->array->items[i]);
                        for (int j = 0; j < ac; ++j) {
                                vmP(&ARG(-1).array->items[i]);
                        }
                        array->array->items[i] = vmC(&f, argc);
                }
        }

        array->array->count = n;
        shrink(ty, array);

        return *array;
}

static Value
array_window(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("array.window() expects 1 or 2 arguments but got %d", argc);

        Value k = ARG(0);
        if (k.type != VALUE_INTEGER)
                zP("the first argument to array.window() must be an integer");

        if (k.integer <= 0)
                zP("the first argument to array.window() must be positive");

        int n = max((intmax_t)array->array->count - k.integer + 1, 0);

        if (argc == 2) {
                Value f = ARG(1);
                if (!CALLABLE(f))
                        zP("the second argument to array.window() must be callable");

                for (int i = 0; i < n; ++i) {
                        for (int j = i; j < i + k.integer; ++j)
                                vmP(&array->array->items[j]);
                        array->array->items[i] = vmC(&f, k.integer);
                }

        } else {
                for (int i = 0; i < n; ++i) {
                        struct array *w = vA();
                        NOGC(w);
                        for (int j = i; j < i + k.integer; ++j)
                                vAp(w, array->array->items[j]);
                        OKGC(w);
                        array->array->items[i] = ARRAY(w);
                }
        }

        array->array->count = n;
        shrink(ty, array);

        return *array;
}

static Value
array_slice(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("array.slice() expects 1 or 2 arguments but got %d", argc);

        Value start = ARG(0);
        if (start.type != VALUE_INTEGER)
                zP("non-integer passed as first argument to array.slice()");

        int s = start.integer;
        int n;

        if (argc == 2) {
                Value count = ARG(1);
                if (count.type != VALUE_INTEGER)
                        zP("non-integer passed as second argument to array.slice()");
                n = count.integer;
        } else {
                n = array->array->count;
        }

        if (s < 0)
                s += array->array->count;
        if (s < 0)
                zP("start index passed to array.slice() is out of range");

        if (n < 0)
                n += array->array->count;
        if (n < 0)
                zP("negative count passed to array.slice()");

        s = min(s, array->array->count);
        n = min(n, array->array->count - s);

        Value result = ARRAY(vA());
        NOGC(result.array);
        value_array_reserve(ty, result.array, n);
        OKGC(result.array);
        memmove(result.array->items, array->array->items + s, n * sizeof (Value));
        result.array->count = n;

        return result;
}

static Value
array_sort(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int i;
        int n;

        switch (argc) {
        case 0:
                i = 0;
                n = array->array->count;
                break;
        case 2:
                if (ARG(1).type != VALUE_INTEGER)
                        zP("the second argument to array.sort() must be an integer");
                n = ARG(1).integer;
        case 1:
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the first argument to array.sort() must be an integer");
                i = ARG(0).integer;
                break;
        default:
                zP("array.sort() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (i < 0)
                i += array->array->count;

        if (argc == 1)
                n = array->array->count - i;

        if (n < 0 || i < 0 || i + n > array->array->count)
                zP("invalid index passed to array.sort()");

        Value *by = NAMED("by");
        Value *cmp = NAMED("cmp");

        if (by != NULL && cmp != NULL) {
                zP("ambiguous call to Array.sort(): by and cmp both specified");
        }

        SortContext ctx = {
                .ty = ty
        };

        if (by != NULL) {
                if (!CALLABLE(*by)) {
                        zP("Array.sort(): `by` is not callable");
                }
                ctx.f = *by;
                rqsort(array->array->items + i, n, sizeof (Value), compare_by, &ctx);
        } else if (cmp != NULL) {
                if (!CALLABLE(*cmp)) {
                        zP("Array.sort(): `cmp` is not callable");
                }
                ctx.f = *cmp;
                rqsort(array->array->items + i, n, sizeof (Value), compare_by2, &ctx);
        } else {
                rqsort(array->array->items + i, n, sizeof (Value), compare_default, ty);
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
#define CMP(i, j) value_compare(ty, &array->array->items[i], &array->array->items[j])
        if (argc != 0)
                zP("array.nextPermutation() expects no arguments but got %d", argc);

        for (int i = array->array->count - 1; i > 0; --i) {
                if (CMP(i - 1, i) < 0) {
                        int j = i;
                        for (int k = i + 1; k < array->array->count; ++k)
                                if (CMP(k, j) < 0 && CMP(k, i - 1) > 0)
                                        j = k;

                        Value t = array->array->items[i - 1];
                        array->array->items[i - 1] = array->array->items[j];
                        array->array->items[j] = t;

                        vmP(&INTEGER(i));
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
        for (int i = 0; i < array->array->count; ++i) {
                if (value_apply_predicate(ty, &f, &array->array->items[i]))
                        ++keep;
                else
                        break;
        }

        array->array->count = keep;
        shrink(ty, array);

        return *array;
}

static Value
array_take_while(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.takeWhile!() expects 1 argument but got %d", argc);

        Value f = ARG(0);

        if (!CALLABLE(f))
                zP("non-callable predicate passed to array.takeWhile!()");

        int keep = 0;
        for (int i = 0; i < array->array->count; ++i)
                if (value_apply_predicate(ty, &f, &array->array->items[i]))
                        ++keep;
                else
                        break;

        Value result = ARRAY(vA());
        NOGC(result.array);
        value_array_reserve(ty, result.array, keep);
        OKGC(result.array);
        memmove(result.array->items, array->array->items, keep * sizeof (Value));
        result.array->count = keep;

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
        for (int i = 0; i < array->array->count; ++i)
                if (value_apply_predicate(ty, &f, &array->array->items[i]))
                        ++drop;
                else
                        break;

        memmove(array->array->items, array->array->items + drop, (array->array->count - drop) * sizeof (Value));
        array->array->count -= drop;
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
        for (int i = 0; i < array->array->count; ++i)
                if (value_apply_predicate(ty, &f, &array->array->items[i]))
                        ++drop;
                else
                        break;

        int n = array->array->count - drop;
        Value result = ARRAY(vA());
        NOGC(result.array);
        value_array_reserve(ty, result.array, n);
        OKGC(result.array);
        memmove(result.array->items, array->array->items + drop, n * sizeof (Value));
        result.array->count = n;

        return result;
}

static Value
array_uniq(Ty *ty, Value *array, int argc, Value *kwargs)
{
        Value *f = NULL;

        if (argc == 1)
                f = &ARG(0);
        else if (argc != 0)
                zP("array.uniq() expects 0 or 1 arguments but got %d", argc);

        if (f != NULL && !CALLABLE(*f))
                zP("the argument to array.uniq() must be callable");

        Value d = DICT(dict_new(ty));
        gP(&d);

        int n = 0;
        for (int i = 0; i < array->array->count; ++i) {
                Value e = array->array->items[i];
                Value k = (f == NULL) ? e : vm_eval_function(ty, f, &e, NULL);
                Value *v = dict_put_key_if_not_exists(ty, d.dict, k);
                if (v->type == VALUE_NIL) {
                        *v = e;
                        array->array->items[n++] = e;
                }
        }

        gX();
        array->array->count = n;

        return *array;
}

static Value
array_take_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.take!() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (n.type != VALUE_INTEGER)
                zP("non-integer passed to array.take!()");

        array->array->count = min(array->array->count, n.integer);
        shrink(ty, array);

        return *array;
}

static Value
array_take(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.take() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (n.type != VALUE_INTEGER)
                zP("non-integer passed to array.take!()");

        Value result = ARRAY(vA());

        int count = min(n.integer, array->array->count);

        NOGC(result.array);
        value_array_reserve(ty, result.array, count);
        OKGC(result.array);

        memmove(result.array->items, array->array->items, count * sizeof (Value));
        result.array->count = count;

        return result;
}

static Value
array_drop_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.drop!() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (n.type != VALUE_INTEGER)
                zP("non-integer passed to array.drop!()");

        int d = min(array->array->count, max(n.integer, 0));

        memmove(array->array->items, array->array->items + d, (array->array->count - d) * sizeof (Value));
        array->array->count -= d;
        shrink(ty, array);

        return *array;
}

static Value
array_drop(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.drop() expects 1 argument but got %d", argc);

        Value n = ARG(0);

        if (n.type != VALUE_INTEGER)
                zP("non-integer passed to array.drop()");

        Value result = ARRAY(vA());

        int d = min(max(n.integer, 0), array->array->count);
        int count = array->array->count - d;

        NOGC(result.array);
        value_array_reserve(ty, result.array, count);
        OKGC(result.array);

        memcpy(result.array->items, array->array->items + d, count * sizeof (Value));
        result.array->count = count;

        return result;
}

static Value
array_sum(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("the sum method on arrays expects no arguments but got %d", argc);

        if (array->array->count == 0)
                return NIL;

        Value sum, v;
        sum = array->array->items[0];

        gP(&sum);

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                sum = vm_2op(ty, OP_ADD, &sum, &v);
        }

        gX();

        return sum;
}

static Value
array_join(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.join() expects 1 argument but got %d", argc);

        if (array->array->count == 0)
                return NIL;

        Value sep = ARG(0);
        if (sep.type != VALUE_STRING)
                zP("the argument to array.join() must be a string");

        vmP(&array->array->items[0]);
        Value sum = builtin_str(ty, 1, NULL);
        vmX();
        Value v = NIL;

        gP(&sum);
        gP(&v);

        for (int i = 1; i < array->array->count; ++i) {
                vmP(&array->array->items[i]);
                v = builtin_str(ty, 1, NULL);
                vmX();
                sum = vm_2op(ty, OP_ADD, &sum, &sep);
                sum = vm_2op(ty, OP_ADD, &sum, &v);
        }

        gX();
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

        if (!CALLABLE(f))
                zP("invalid source passed to array.consumeWhile()");

        if (!CALLABLE(p))
                zP("invalid predicate passed to array.consumeWhile()");

        Value v = NIL;
        gP(&v);

        for (;;) {
                v = vm_eval_function(ty, &f, NULL);
                if (value_apply_predicate(ty, &p, &v))
                        vAp(array->array, v);
                else
                        break;
        }

        gX();

        return *array;
}

static Value
array_groups_of(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("array.groupsOf() expects 1 or 2 arguments but got %d", argc);

        Value size = ARG(0);
        if (size.type != VALUE_INTEGER)
                zP("the argument to array.groupsOf() must be an integer");

        if (size.integer <= 0)
                zP("the argument to array.groupsOf() must be positive");

        bool keep_short = true;

        if (argc == 2) {
                if (ARG(1).type != VALUE_BOOLEAN) {
                        zP("the second argument to array.groupsOf() must be a boolean");
                }
                keep_short = ARG(1).boolean;
        }

        int n = 0;
        int i = 0;
        while (i + size.integer < array->array->count) {
                struct array *group = vA();
                NOGC(group);
                vvPn(*group, array->array->items + i, size.integer);
                OKGC(group);
                array->array->items[n++] = ARRAY(group);
                i += size.integer;
        }

        if (keep_short && i != array->array->count) {
                struct array *last = vA();
                NOGC(last);
                vvPn(*last, array->array->items + i, array->array->count - i);
                OKGC(last);
                array->array->items[n++] = ARRAY(last);
        }

        array->array->count = n;
        shrink(ty, array);

        return *array;
}

static Value
array_group_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.groupBy() expects 1 argument but got %d", argc);

        Value f = ARG(0);

        if (!CALLABLE(f))
                zP("the argument to array.groupBy() must be callable");

        Value v1, v2;
        v1 = v2 = NIL;

        gP(&v1);
        gP(&v2);

        int len = 0;
        for (int i = 0; i < array->array->count; ++i) {
                Value group = ARRAY(vA());
                NOGC(group.array);
                Value e = array->array->items[i];
                v1 = value_apply_callable(ty, &f, &e);
                vAp(group.array, e);
                while (i + 1 < array->array->count) {
                        v2 = value_apply_callable(ty, &f, &array->array->items[i + 1]);
                        if (value_test_equality(ty, &v1, &v2))
                                vAp(group.array, array->array->items[++i]);
                        else
                                break;
                }
                OKGC(group.array);
                array->array->items[len++] = group;
        }

        gX();
        gX();

        array->array->count = len;
        shrink(ty, array);

        return *array;
}

static Value
array_group(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc == 1)
                return array_group_by(ty, array, argc, kwargs);

        if (argc != 0)
                zP("array.group() expects 0 or 1 arguments but got %d", argc);

        int len = 0;
        for (int i = 0; i < array->array->count; ++i) {
                Value group = ARRAY(vA());
                NOGC(group.array);
                vAp(group.array, array->array->items[i]);
                while (i + 1 < array->array->count && value_test_equality(ty, &array->array->items[i], &array->array->items[i + 1]))
                        vAp(group.array, array->array->items[++i]);
                OKGC(group.array);
                array->array->items[len++] = group;
        }

        array->array->count = len;
        shrink(ty, array);

        return *array;
}

static Value
array_intersperse(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the intersperse method on arrays expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = array->array->count - 1;
        if (n < 1)
                return *array;

        int newcount = 2 * n + 1;
        value_array_reserve(ty, array->array, newcount);
        memcpy(array->array->items + n + 1, array->array->items + 1, n * sizeof (Value));

        int lo = 1;
        int hi = n + 1;
        for (int i = 0; i < n; ++i) {
                array->array->items[lo++] = v;
                array->array->items[lo++] = array->array->items[hi++];
        }

        array->array->count = newcount;
        return *array;
}

static Value
array_min(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc == 1)
                return array_min_by(ty, array, argc, kwargs);

        if (argc != 0)
                zP("the min method on arrays expects no arguments but got %d", argc);

        if (array->array->count == 0)
                return NIL;

        Value min, v;
        min = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
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

        if (array->array->count == 0)
                return NIL;

        Value f = ARG(0);
        if (!CALLABLE(f))
                zP("non-function passed to the minBy method on array");

        Value min, v, k, r;
        min = array->array->items[0];

        gP(&k);
        gP(&r);

        r = k = NIL;

        if (f.type == VALUE_FUNCTION && f.info[2] > 1) {
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function(ty, &f, &v, &min, NULL);
                        if ((r.type != VALUE_INTEGER && !value_truthy(ty, &r)) || r.integer < 0)
                                min = v;

                }
        } else {
                k = vm_eval_function(ty, &f, &min, NULL);
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function(ty, &f, &v, NULL);
                        if (value_compare(ty, &r, &k) < 0) {
                                min = v;
                                k = r;
                        }
                }
        }

        gX();
        gX();

        return min;
}

static Value
array_max(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc == 1)
                return array_max_by(ty, array, argc, kwargs);

        if (argc != 0)
                zP("the max method on arrays expects no arguments but got %d", argc);

        if (array->array->count == 0)
                return NIL;

        Value max, v;
        max = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                if (value_compare(ty, &v, &max) > 0)
                        max = v;
        }

        return max;
}

static Value
array_max_by(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the maxBy method on arrays expects 1 argument but got %d", argc);

        if (array->array->count == 0)
                return NIL;

        Value f = ARG(0);
        if (!CALLABLE(f))
                zP("non-function passed to the maxBy method on array");

        Value max, v, k, r;
        max = array->array->items[0];

        gP(&k);
        gP(&r);

        k = r = NIL;

        if (f.type == VALUE_FUNCTION && f.info[2] > 1) {
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function(ty, &f, &v, &max, NULL);
                        if ((r.type != VALUE_INTEGER && value_truthy(ty, &r)) || r.integer > 0)
                                max = v;

                }
        } else {
                k = vm_eval_function(ty, &f, &max, NULL);
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function(ty, &f, &v, NULL);
                        if (value_compare(ty, &r, &k) > 0) {
                                max = v;
                                k = r;
                        }
                }
        }

        gX();
        gX();

        return max;
}

static Value
array_length(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("array.len() expects no arguments but got %d", argc);

        return INTEGER(array->array->count);
}

static Value
array_shuffle(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("the shuffle! method on arrays expects no arguments but got %d", argc);

        Value t;
        int n = array->array->count;
        for (int i = n - 1; i > 0; --i) {
                int j = rand() % (i + 1);
                t = array->array->items[i];
                array->array->items[i] = array->array->items[j];
                array->array->items[j] = t;
        }

        return *array;
}

static Value
array_map(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the map method on arrays expects 1 argument but got %d", argc);

        Value f = ARG(0);

        if (!CALLABLE(f))
                zP("non-function passed to the map method on array");

        int n = array->array->count;
        for (int i = 0; i < n; ++i) {
                array->array->items[i] = value_apply_callable(ty, &f, &array->array->items[i]);
        }

        return *array;
}

static Value
array_enumerate(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("the enumerate method on arrays expects no arguments but got %d", argc);

        int n = array->array->count;

        for (int i = 0; i < n; ++i) {
                Value entry = vT(2);
                entry.items[0] = INTEGER(i);
                entry.items[1] = array->array->items[i];
                array->array->items[i] =  entry;
        }

        return *array;
}

static Value
array_remove(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the remove method on arrays expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = array->array->count;
        int j = 0;
        for (int i = 0; i < n; ++i)
                if (!value_test_equality(ty, &v, &array->array->items[i]))
                        array->array->items[j++] = array->array->items[i];

        array->array->count = j;
        shrink(ty, array);

        return *array;
}

static Value
array_filter(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the filter method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the filter method on array");

        int n = array->array->count;
        int j = 0;
        for (int i = 0; i < n; ++i)
                if (value_apply_predicate(ty, &pred, &array->array->items[i]))
                        array->array->items[j++] = array->array->items[i];

        array->array->count = j;
        shrink(ty, array);

        return *array;
}

static Value
array_find(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the find method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the find method on array");

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                if (value_apply_predicate(ty, &pred, &array->array->items[i]))
                        return array->array->items[i];

        return NIL;
}

static Value
array_findr(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the findr method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the findr method on array");

        int n = array->array->count;
        for (int i = n - 1; i >= 0; --i)
                if (value_apply_predicate(ty, &pred, &array->array->items[i]))
                        return array->array->items[i];

        return NIL;
}

static Value
array_bsearch(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the bsearch? method on array expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int i = 0,
            lo = 0,
            hi = array->array->count - 1;

        while (lo <= hi) {
                int m = (lo + hi) / 2;
                int c = value_compare(ty, &v, &array->array->items[m]);
                if      (c < 0) { hi = m - 1; i = m;  }
                else if (c > 0) { lo = m + 1; i = lo; }
                else            { return INTEGER(m);  }
        }

        return INTEGER(i);
}

static Value
array_bsearch_strict(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the bsearch method on array expects 1 argument but got %d", argc);

        Value v = ARG(0);

        // FIXME: is it ok to subtract 1 here when count is 0? implementation-defined?
        int lo = 0,
            hi = array->array->count - 1;

        while (lo <= hi) {
                int m = (lo + hi) / 2;
                int c = value_compare(ty, &v, &array->array->items[m]);
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

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                if (value_apply_predicate(ty, &pred, &array->array->items[i]))
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

        int n = array->array->count;
        for (int i = n - 1; i >= 0; --i)
                if (value_apply_predicate(ty, &pred, &array->array->items[i]))
                        return INTEGER(i);

        return NIL;
}

static Value
array_set(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("array.set() expects 0 arguments but got %d", argc);

        struct dict *d = dict_new(ty);
        NOGC(d);

        for (int i = 0; i < array->array->count; ++i) {
                dict_put_key_if_not_exists(ty, d, array->array->items[i]);
        }

        OKGC(d);
        return DICT(d);
}

static Value
array_partition(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the partition method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the partition method on array");

        int n = array->array->count;
        int j = 0;
        struct array *yes = vA();
        struct array *no = vA();

        NOGC(yes);
        NOGC(no);

        for (int i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, &array->array->items[i])) {
                        array->array->items[j++] = array->array->items[i];
                } else {
                        vAp(no, array->array->items[i]);
                }
        }

        array->array->count = j;
        shrink(ty, array);

        yes->items = array->array->items;
        yes->count = array->array->count;
        yes->capacity = array->array->capacity;

        vec_init(*array->array);

        vAp(array->array, ARRAY(yes));
        vAp(array->array, ARRAY(no));

        OKGC(yes);
        OKGC(no);

        return *array;
}

static Value
array_split_at(Ty *ty, Value *array, int argc, Value *kargs)
{
        if (argc != 1) {
                zP("array.split()  expects 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER) {
                zP(
                        "array.split() expected integer but got %s%s%s%s",
                        TERM(96),
                        TERM(1),
                        value_show(ty, &ARG(0)),
                        TERM(0)
                );
        }

        int i = ARG(0).integer;

        if (i < 0)
                i += array->array->count;

        if (i < 0 || i > array->array->count) {
                zP("array.split(): index %s%d%s out of range", TERM(96), i, TERM(0));
        }

        struct array *front = vA();
        NOGC(front);

        struct array *back = vA();
        NOGC(back);

        vvPn(*front, array->array->items, i);
        vvPn(*back, array->array->items + i, array->array->count - i);

        Value pair = vT(2);
        pair.items[0] = ARRAY(front);
        pair.items[1] = ARRAY(back);

        OKGC(front);
        OKGC(back);

        return pair;
}

static Value
array_partition_no_mut(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("the partition method on arrays expects 1 argument but got %d", argc);

        Value pred = ARG(0);

        if (!CALLABLE(pred))
                zP("non-predicate passed to the partition method on array");

        int n = array->array->count;
        struct array *yes = vA();
        struct array *no = vA();

        NOGC(yes);
        NOGC(no);

        for (int i = 0; i < n; ++i) {
                if (value_apply_predicate(ty, &pred, &array->array->items[i])) {
                        vAp(yes, array->array->items[i]);
                } else {
                        vAp(no, array->array->items[i]);
                }
        }

        struct array *result = vA();
        NOGC(result);

        vAp(result, ARRAY(yes));
        vAp(result, ARRAY(no));


        OKGC(yes);
        OKGC(no);
        OKGC(result);

        return ARRAY(result);
}

static Value
array_contains(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.contains?() expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(ty, &v, &array->array->items[i]))
                        return BOOLEAN(true);

        return BOOLEAN(false);
}

static Value
array_tuple(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("array.tuple() expects 0 arguments but got %d", argc);
        }

        int n = array->array->count;

        Value v = vT(n);
        memcpy(v.items, array->array->items, n * sizeof (Value));

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
                for (int i = 0; i < array->array->count; ++i) {
                        Value *c = dict_get_value(ty, d.dict, &array->array->items[i]);
                        if (c == NULL) {
                                dict_put_value(ty, d.dict, array->array->items[i], INTEGER(1));
                        } else {
                                c->integer += 1;
                        }
                }
        } else {
                Value f = ARG(0);
                if (!CALLABLE(f))
                        zP("non-callable passed to array.tally()");

                for (int i = 0; i < array->array->count; ++i) {
                        Value v = value_apply_callable(ty, &f, &array->array->items[i]);
                        Value *c = dict_get_value(ty, d.dict, &v);
                        if (c == NULL) {
                                dict_put_value(ty, d.dict, v, INTEGER(1));
                        } else {
                                c->integer += 1;
                        }
                }
        }

        gX();

        return d;
}

static Value
array_search(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.search() expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(ty, &v, &array->array->items[i]))
                        return INTEGER(i);

        return NIL;
}

static Value
array_searchr(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("array.searchr() expects 1 argument but got %d", argc);

        Value v = ARG(0);

        int n = array->array->count;
        for (int i = n - 1; i >= 0; --i)
                if (value_test_equality(ty, &v, &array->array->items[i]))
                        return INTEGER(i);

        return NIL;
}

static Value
array_flat(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0 && argc != 1) {
                zP("array.flat() expects 0 or 1 arguments but got %d", argc);
        }

        struct array *r = vA();

        vec(Value *) stack = {0};
        vec(int) dstack = {0};

        int maxdepth;

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("the argument to array.flat() must be an integer");
                }
                maxdepth = ARG(0).integer;
        } else {
                maxdepth = INT_MAX;
        }

        NOGC(r);

        for (int i = 0; i < array->array->count; ++i) {
                vvP(stack, &array->array->items[i]);
                vvP(dstack, 1);
                while (stack.count > 0) {
                        Value *v = *vvX(stack);
                        int d = *vvX(dstack);
                        if (v->type != VALUE_ARRAY || d > maxdepth) {
                                vAp(r, *v);
                        } else {
                                for (int i = v->array->count - 1; i >= 0; --i) {
                                        vvP(stack, &v->array->items[i]);
                                        vvP(dstack, d + 1);
                                }
                        }
                }
        }

        vvF(stack);
        OKGC(r);

        return ARRAY(r);

}

static Value
array_each(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("the each method on arrays expects 1 or 2 arguments but got %d", argc);

        if (argc == 1) {
                Value f = ARG(0);

                if (f.type != VALUE_FUNCTION && f.type != VALUE_BUILTIN_FUNCTION && f.type != VALUE_METHOD && f.type != VALUE_BUILTIN_METHOD)
                        zP("non-function passed to the each method on array");

                int n = array->array->count;

                for (int i = 0; i < n; ++i)
                        vm_eval_function(ty, &f, &array->array->items[i], &INTEGER(i), NULL);

                return *array;
        } else {
                Value v = ARG(0);
                Value f = ARG(1);

                if (f.type != VALUE_FUNCTION && f.type != VALUE_BUILTIN_FUNCTION && f.type != VALUE_METHOD && f.type != VALUE_BUILTIN_METHOD)
                        zP("non-function passed to the each method on array");

                int n = array->array->count;

                for (int i = 0; i < n; ++i) {
                        vm_eval_function(ty, &f, &v, &array->array->items[i], &INTEGER(i), NULL);
                }

                return v;
        }

}

static Value
array_all(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int n = array->array->count;

        if (argc == 0) {
                for (int i = 0; i < n; ++i) {
                        if (!value_truthy(ty, &array->array->items[i]))
                                return BOOLEAN(false);
                }
        } else if (argc == 1) {
                Value pred = ARG(0);

                if (!CALLABLE(pred))
                        zP("non-predicate passed to the all? method on array");

                for (int i = 0; i < n; ++i) {
                        if (!value_apply_predicate(ty, &pred, &array->array->items[i]))
                                return BOOLEAN(false);
                }
        } else {
                zP("the all? method on arrays expects 0 or 1 argument(s) but got %d", argc);
        }

        return BOOLEAN(true);
}

static Value
array_any(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int n = array->array->count;

        if (argc == 0) {
                for (int i = 0; i < n; ++i)
                        if (value_truthy(ty, &array->array->items[i]))
                                return BOOLEAN(true);
        } else if (argc == 1) {
                Value pred = ARG(0);

                if (!CALLABLE(pred))
                        zP("non-predicate passed to the any? method on array");

                for (int i = 0; i < n; ++i)
                        if (value_apply_predicate(ty, &pred, &array->array->items[i]))
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

        int n = array->array->count;
        int k = 0;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(ty, &v, &array->array->items[i]))
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

        int n = array->array->count;
        int k = 0;
        for (int i = 0; i < n; ++i)
                if (value_apply_predicate(ty, &pred, &array->array->items[i]))
                        k += 1;

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
                if (array->array->count == 0)
                        zP("foldLeft called on empty array with 1 argument");
                v = array->array->items[0];
        } else {
                start = 0;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f))
                zP("non-function passed to the foldLeft method on array");

        gP(&v);

        int n = array->array->count;
        for (int i = start; i < n; ++i)
                v = vm_eval_function(ty, &f, &v, &array->array->items[i], NULL);

        gX();

        return v;
}

/* TODO: fix this */
static Value
array_fold_right(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("the foldRight method on arrays expects 1 or 2 arguments but got %d", argc);

        int start;
        Value f, v;

        if (argc == 1) {
                start = array->array->count - 2;
                f = ARG(0);
                if (array->array->count == 0)
                        zP("foldRight called on empty array with 1 argument");
                v = array->array->items[start + 1];
        } else {
                start = array->array->count - 1;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f))
                zP("non-function passed to the foldRight method on array");

        gP(&v);

        for (int i = start; i >= 0; --i)
                v = vm_eval_function(ty, &f, &array->array->items[i], &v, NULL);

        gX();

        return v;
}

static Value
array_scan_left(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("the scanLeft method on arrays expects 1 or 2 arguments but got %d", argc);

        int start;
        Value f, v;

        if (argc == 1) {
                start = 1;
                f = ARG(0);
                if (array->array->count == 0)
                        zP("scanLeft called on empty array with 1 argument");
                v = array->array->items[0];
        } else {
                start = 0;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f))
                zP("non-function passed to the scanLeft method on array");

        int n = array->array->count;
        for (int i = start; i < n; ++i) {
                v = vm_eval_function(ty, &f, &v, &array->array->items[i], NULL);
                array->array->items[i] = v;
        }

        return *array;
}

static Value
array_scan_right(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("the scanRight method on arrays expects 1 or 2 arguments but got %d", argc);

        int start;
        Value f, v;

        if (argc == 1) {
                start = array->array->count - 2;
                f = ARG(0);
                if (array->array->count == 0)
                        zP("scanRight called on empty array with 1 argument");
                v = array->array->items[start + 1];
        } else {
                start = array->array->count - 1;
                f = ARG(1);
                v = ARG(0);
        }

        if (!CALLABLE(f))
                zP("non-function passed to the scanRight method on array");

        for (int i = start; i >= 0; --i) {
                v = vm_eval_function(ty, &f, &array->array->items[i], &v, NULL);
                array->array->items[i] = v;
        }

        return *array;
}

static Value
array_reverse(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int lo;
        int n;

        if (argc > 0 && ARG(0).type != VALUE_INTEGER) {
                zP("array.reverse(): expected integer as first argument but got: %s", value_show(ty, &ARG(0)));
        }

        if (argc > 1 && ARG(1).type != VALUE_INTEGER) {
                zP("array.reverse(): expected integer as second argument but got: %s", value_show(ty, &ARG(1)));
        }

        if (argc > 0) {
                lo = ARG(0).integer;
                if (lo < 0) { lo += array->array->count; }
        } else {
                lo = 0;
        }

        if (lo < 0 || lo > array->array->count) {
                zP("array.reverse(): invalid start index %d for array with size %zu", lo, array->array->count);
        }

        if (argc > 1) {
                n = ARG(1).integer;
        } else {
                n = array->array->count - lo;
        }

        if (n == 0) {
                return *array;
        }

        int hi = lo + n - 1;

        if (hi > array->array->count) {
                zP(
                        "array.reverse(): invalid count %d for start index %d and array with size %zu",
                        n, lo, array->array->count
                );
        }

        Value t;

        while (lo < hi) {
                t = array->array->items[lo];
                array->array->items[lo] = array->array->items[hi];
                array->array->items[hi] = t;

                ++lo;
                --hi;
        }

        return *array;
}

static Value
array_rotate(Ty *ty, Value *array, int argc, Value *kwargs)
{
        int d = 1;
        int n = array->array->count;

        if (argc == 1) {
                Value amount = ARG(0);
                if (amount.type != VALUE_INTEGER)
                        zP("the argument to array.rotate() must be an integer");
                d = amount.integer;
        } else if (argc != 0) {
                zP("the rotate method on arrays expects 0 or 1 arguments but got %d", argc);
        }

        d %= n;
        if (d < 0)
                d += n;

        int N = gcd(n, d);
        int i, j, k;
        for (i = 0; i < N; ++i) {
                Value t = array->array->items[i];
                j = i;
                for (;;) {
                        k = j + d;
                        if (k >= n)
                                k = k - n;
                        if (k == i)
                                break;
                        array->array->items[j] = array->array->items[k];
                        j = k;

                }
                array->array->items[j] = t;
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

        if (array->array->count == 0)
                return *array;

        SortContext ctx = {
                .f = f,
                .ty = ty
        };

        rqsort(array->array->items, array->array->count, sizeof (Value), compare_by, &ctx);

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

        if (array->array->count == 0)
                return *array;

        SortContext ctx = {
                .f = f,
                .ty = ty
        };

        rqsort(array->array->items, array->array->count, sizeof (Value), compare_by2, &ctx);

        return *array;
}

static Value
array_clone(Ty *ty, Value *array, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("the clone method on arrays expects no arguments but got %d", argc);

        Value v = *array;
        v.array = value_array_clone(ty, v.array);

        return v;
}

#define DEFINE_NO_MUT(name) \
        static Value \
        array_ ## name ## _no_mut(Ty *ty, Value *array, int argc, Value *kwargs) \
        { \
                Value clone = array_clone(ty, array, 0, NULL); \
                gP(&clone); \
                Value result = array_ ## name(ty, &clone, argc, kwargs); \
                gX(); \
                return result; \
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
        { .name = "slice!",            .func = array_slice_mut               },
        { .name = "sort",              .func = array_sort_no_mut             },
        { .name = "sort!",             .func = array_sort                    },
        { .name = "sortBy",            .func = array_sort_by_no_mut          },
        { .name = "sortBy!",           .func = array_sort_by                 },
        { .name = "sortOn",            .func = array_sort_on_no_mut          },
        { .name = "sortOn!",           .func = array_sort_on                 },
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
