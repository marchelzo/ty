#include <stdlib.h>
#include <string.h>

#include "value.h"
#include "log.h"
#include "functions.h"
#include "operators.h"
#include "util.h"
#include "vm.h"

static value_vector no_args = { .count = 0 };

static struct value *comparison_fn;

static int
compare_by(void const *v1, void const *v2)
{
        struct value k1 = value_apply_callable(comparison_fn, (struct value *)v1);
        struct value k2 = value_apply_callable(comparison_fn, (struct value *)v2);
        return value_compare(&k1, &k2);
}

static int
compare_by2(void const *v1, void const *v2)
{
        struct value v = vm_eval_function2(comparison_fn, (struct value *)v1, (struct value *)v2);

        if (v.type == VALUE_INTEGER) {
                return v.integer;
        } else {
                return value_truthy(&v) ? 1 : -1;
        }
}

static struct value
array_slice_mut(struct value *array, value_vector *args)
{
        if (args->count != 2) {
                vm_panic("array.slice!() expects 2 arguments but got %zu", args->count);
        }
        
        struct value start = args->items[0];
        struct value count = args->items[1];

        if (start.type != VALUE_INTEGER) {
                vm_panic("non-integer passed as first argument to array.slice!()");
        }

        if (count.type != VALUE_INTEGER) {
                vm_panic("non-integer passed as second argument to array.slice!()");
        }

        int s = start.integer;
        int n = count.integer;

        if (s < 0) {
                s += array->array->count;
        }
        if (s < 0) {
                vm_panic("start index passed to array.slice!() is out of range");
        }

        s = min(s, array->array->count);
        n = min(n, array->array->count - s);

        memmove(array->array->items, array->array->items + s, n * sizeof (struct value));
        array->array->count = n;

        return *array;
}

static struct value
array_zip(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.zip() expects 1 argument but got %zu", args->count);

        struct value other = args->items[0];
        if (other.type != VALUE_ARRAY)
                vm_panic("the argument to array.zip() must be an array");

        int n = min(array->array->count, other.array->count);

        for (int i = 0; i < n; ++i) {
                struct value_array *a = value_array_new();
                vec_push(*a, array->array->items[i]);
                vec_push(*a, other.array->items[i]);
                array->array->items[i] = ARRAY(a);
        }

        /*
         * TODO: implement something like this in vec.h
         */
        array->array->count = n;
        resize(array->array->items, n * sizeof *array->array->items);

        return *array;
}

static struct value
array_slice(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("array.slice() expects 2 arguments but got %zu", args->count);
        
        struct value start = args->items[0];
        struct value count = args->items[1];

        if (start.type != VALUE_INTEGER)
                vm_panic("non-integer passed as first argument to array.slice()");

        if (count.type != VALUE_INTEGER)
                vm_panic("non-integer passed as second argument to array.slice()");

        int s = start.integer;
        int n = count.integer;

        if (s < 0)
                s += array->array->count;
        if (s < 0)
                vm_panic("start index passed to array.slice() is out of range");

        s = min(s, array->array->count);
        n = min(n, array->array->count - s);

        struct value result = ARRAY(value_array_new());
        value_array_reserve(result.array, n);
        memmove(result.array->items, array->array->items + s, n * sizeof (struct value));
        result.array->count = n;

        return result;
}

static struct value
array_sort(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the sort method on arrays expects no arguments but got %zu", args->count);

        qsort(array->array->items, array->array->count, sizeof (struct value), value_compare);

        return *array;
}

static struct value
array_take_while_mut(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.takeWhile!() expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];

        if (!CALLABLE(f))
                vm_panic("non-callable predicate passed to array.takeWhile!()");

        int keep = 0;
        for (int i = 0; i < array->array->count; ++i) {
                if (value_apply_predicate(&f, &array->array->items[i]))
                        ++keep;
                else
                        break;
        }

        array->array->count = keep;

        return *array;
}

static struct value
array_take_while(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.takeWhile!() expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];

        if (!CALLABLE(f)) {
                vm_panic("non-callable predicate passed to array.takeWhile!()");
        }

        int keep = 0;
        for (int i = 0; i < array->array->count; ++i) {
                if (value_apply_predicate(&f, &array->array->items[i])) {
                        ++keep;
                } else {
                        break;
                }
        }

        struct value result = ARRAY(value_array_new());
        value_array_reserve(result.array, keep);
        memmove(result.array->items, array->array->items, keep * sizeof (struct value));
        result.array->count = keep;

        return result;
}

static struct value
array_drop_while_mut(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.dropWhile!() expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];

        if (!CALLABLE(f)) {
                vm_panic("non-callable predicate passed to array.dropWhile!()");
        }

        int drop = 0;
        for (int i = 0; i < array->array->count; ++i) {
                if (value_apply_predicate(&f, &array->array->items[i])) {
                        ++drop;
                } else {
                        break;
                }
        }

        memmove(array->array->items, array->array->items + drop, (array->array->count - drop) * sizeof (struct value));
        array->array->count -= drop;

        return *array;
}

static struct value
array_drop_while(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.dropWhile() expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];

        if (!CALLABLE(f)) {
                vm_panic("non-callable predicate passed to array.dropWhile()");
        }

        int drop = 0;
        for (int i = 0; i < array->array->count; ++i) {
                if (value_apply_predicate(&f, &array->array->items[i])) {
                        ++drop;
                } else {
                        break;
                }
        }

        int n = array->array->count - drop;
        struct value result = ARRAY(value_array_new());
        value_array_reserve(result.array, n);
        memmove(result.array->items, array->array->items + drop, n * sizeof (struct value));
        result.array->count = n;

        return result;
}

static struct value
array_take_mut(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.take!() expects 1 argument but got %zu", args->count);
        }

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER) {
                vm_panic("non-integer passed to array.take!()");
        }

        array->array->count = min(array->array->count, n.integer);

        return *array;
}

static struct value
array_take(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.take() expects 1 argument but got %zu", args->count);
        }

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER) {
                vm_panic("non-integer passed to array.take!()");
        }

        struct value result = ARRAY(value_array_new());

        int count = min(n.integer, array->array->count);

        value_array_reserve(result.array, count);
        memmove(result.array->items, array->array->items, count * sizeof (struct value));
        result.array->count = count;

        return result;
}

static struct value
array_drop_mut(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.drop!() expects 1 argument but got %zu", args->count);
        }

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER) {
                vm_panic("non-integer passed to array.drop!()");
        }

        int d = min(array->array->count, n.integer);

        memmove(array->array->items, array->array->items + d, (array->array->count - d) * sizeof (struct value));
        array->array->count -= d;

        return *array;
}

static struct value
array_drop(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.drop() expects 1 argument but got %zu", args->count);
        }

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER) {
                vm_panic("non-integer passed to array.drop!()");
        }

        struct value result = ARRAY(value_array_new());

        int d = min(n.integer, array->array->count);
        int count = array->array->count - d;

        value_array_reserve(result.array, count);
        memmove(result.array->items, array->array->items + d, count * sizeof (struct value));
        result.array->count = count;

        return result;
}

static struct value
array_sum(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the sum method on arrays expects no arguments but got %zu", args->count);
        }

        if (array->array->count == 0) {
                return NIL;
        }

        struct value sum, v;
        sum = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                sum = binary_operator_addition(&sum, &v);
        }

        return sum;
}

static struct value
array_consume_while(struct value *array, value_vector *args)
{
        if (args->count != 2) {
                vm_panic("array.consumeWhile() expects 2 arguments but got %zu", args->count);
        }

        struct value f = args->items[0];
        struct value p = args->items[1];

        if (!CALLABLE(f)) {
                vm_panic("invalid source passed to array.consumeWhile()");
        }

        if (!CALLABLE(p)) {
                vm_panic("invalid predicate passed to array.consumeWhile()");
        }

        for (;;) {
                struct value v = vm_eval_function(&f, NULL);
                if (value_apply_predicate(&p, &v)) {
                        value_array_push(array->array, v);
                } else {
                        break;
                }
        }

        return *array;
}

static struct value
array_group_by(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("array.groupBy() expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];
        
        if (!CALLABLE(f)) {
                vm_panic("the argument to array.groupBy() must be callable");
        }

        struct value result = ARRAY(value_array_new());

        for (int i = 0; i < array->array->count; ++i) {
                struct value group = ARRAY(value_array_new());
                struct value e = array->array->items[i];
                struct value v = value_apply_callable(&f, &e);
                value_array_push(group.array, e);
                while (i + 1 < array->array->count) {
                        struct value v2 = value_apply_callable(&f, &array->array->items[i + 1]);
                        if (value_test_equality(&v, &v2)) {
                                value_array_push(group.array, array->array->items[++i]);
                        } else {
                                break;
                        }
                }
                value_array_push(result.array, group);
        }

        return result;
}

static struct value
array_group(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("array.group() expects 0 arguments but got %zu", args->count);
        }

        struct value result = ARRAY(value_array_new());

        for (int i = 0; i < array->array->count; ++i) {
                struct value group = ARRAY(value_array_new());
                value_array_push(group.array, array->array->items[i]);
                while (i + 1 < array->array->count && value_test_equality(&array->array->items[i], &array->array->items[i + 1])) {
                        value_array_push(group.array, array->array->items[++i]);
                }
                value_array_push(result.array, group);
        }

        return result;
}

static struct value
array_intersperse(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the intersperse method on arrays expects 1 argument but got %zu", args->count);
        }

        struct value v = args->items[0];

        int n = array->array->count - 1;
        if (n < 1) {
                return *array;
        }

        int newcount = 2 * n + 1;
        value_array_reserve(array->array, newcount);
        memcpy(array->array->items + n + 1, array->array->items + 1, n * sizeof (struct value));

        int lo = 1;
        int hi = n + 1;
        for (int i = 0; i < n; ++i) {
                array->array->items[lo++] = v;
                array->array->items[lo++] = array->array->items[hi++];
        }

        array->array->count = newcount;
        return *array;
}

static struct value
array_min(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the min method on arrays expects no arguments but got %zu", args->count);
        }

        if (array->array->count == 0) {
                vm_panic("min called on empty array");
        }

        struct value min, v;
        min = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                if (value_compare(&v, &min) < 0) {
                        min = v;
                }
        }

        return min;
}

static struct value
array_min_by(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the minBy method on arrays expects 1 argument but got %zu", args->count);
        }

        if (array->array->count == 0) {
                vm_panic("minBy called on empty array");
        }

        struct value f = args->items[0];
        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the minBy method on array");
        }

        struct value min, v, k, r;
        min = array->array->items[0];

        if (f.type == VALUE_FUNCTION && f.param_symbols.count > 1) {
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function2(&f, &v, &min);
                        if ((r.type != VALUE_INTEGER && !value_truthy(&r)) || r.integer < 0) {
                                min = v;
                        }

                }
        } else {
                k = vm_eval_function(&f, &min);
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function(&f, &v);
                        if (value_compare(&r, &k) < 0) {
                                min = v;
                                k = r;
                        }
                }
        }

        return min;
}

static struct value
array_max(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the max method on arrays expects no arguments but got %zu", args->count);
        }

        if (array->array->count == 0) {
                vm_panic("max called on empty array");
        }

        struct value max, v;
        max = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                if (value_compare(&v, &max) > 0) {
                        max = v;
                }
        }

        return max;
}

static struct value
array_max_by(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the maxBy method on arrays expects 1 argument but got %zu", args->count);
        }

        if (array->array->count == 0) {
                vm_panic("maxBy called on empty array");
        }

        struct value f = args->items[0];
        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the maxBy method on array");
        }

        struct value max, v, k, r;
        max = array->array->items[0];

        if (f.type == VALUE_FUNCTION && f.param_symbols.count > 1) {
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function2(&f, &v, &max);
                        if ((r.type != VALUE_INTEGER && value_truthy(&r)) || r.integer > 0) {
                                max = v;
                        }

                }
        } else {
                k = vm_eval_function(&f, &max);
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function(&f, &v);
                        if (value_compare(&r, &k) > 0) {
                                max = v;
                                k = r;
                        }
                }
        }

        return max;
}

static struct value
array_length(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("array.len() expects no arguments but got %zu", args->count);
        }

        return (struct value) { .type = VALUE_INTEGER, .integer = array->array->count };
}

static struct value
array_shuffle(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the shuffle! method on arrays expects no arguments but got %zu", args->count);
        }

        struct value t;
        int n = array->array->count;
        for (int i = n - 1; i > 1; --i) {
                int j = rand() % i;
                t = array->array->items[i];
                array->array->items[i] = array->array->items[j];
                array->array->items[j] = t;
        }

        return *array;
}

static struct value
array_map(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the map method on arrays expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];

        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the map method on array");
        }

        int n = array->array->count;
        for (int i = 0; i < n; ++i) {
                array->array->items[i] = value_apply_callable(&f, &array->array->items[i]);
        }

        return *array;
}

static struct value
array_enumerate(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the enumerate method on arrays expects no arguments but got %zu", args->count);
        }

        int n = array->array->count;
        for (int i = 0; i < n; ++i) {
                struct value entry = ARRAY(value_array_new());
                value_array_push(entry.array, INTEGER(i));
                value_array_push(entry.array, array->array->items[i]);
                array->array->items[i] =  entry;
        }

        return *array;
}

static struct value
array_filter(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the filter method on arrays expects 1 argument but got %zu", args->count);
        }

        struct value pred = args->items[0];

        if (!CALLABLE(pred)) {
                vm_panic("non-predicate passed to the filter method on array");
        }

        int n = array->array->count;
        int j = 0;
        for (int i = 0; i < n; ++i) {
                if (value_apply_predicate(&pred, &array->array->items[i])) {
                        array->array->items[j++] = array->array->items[i];
                }
        }

        array->array->count = j;

        return *array;
}

static struct value
array_contains(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.contains?() expects 1 argument but got %zu", args->count);

        struct value v = args->items[0];

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(&v, &array->array->items[i]))
                        return BOOLEAN(true);

        return BOOLEAN(false);
}

static struct value
array_each(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the each method on arrays expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];

        if (f.type != VALUE_FUNCTION && f.type != VALUE_BUILTIN_FUNCTION) {
                vm_panic("non-function passed to the each method on array");
        }

        int n = array->array->count;

        for (int i = 0; i < n; ++i) {
                vm_eval_function(&f, &array->array->items[i]);
        }

        return *array;
}

static struct value
array_fold_left(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("the foldLeft method on arrays expects 1 or 2 arguments but got %zu", args->count);
        }

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = 1;
                f = args->items[0];
                if (array->array->count == 0) {
                        vm_panic("foldLeft called on array with 1 argument");
                }
                v = array->array->items[0];
        } else {
                start = 0;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the foldLeft method on array");
        }

        int n = array->array->count;
        for (int i = start; i < n; ++i) {
                v = vm_eval_function2(&f, &v, &array->array->items[i]);
        }

        return v;
}

static struct value
array_fold_right(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("the foldRight method on arrays expects 1 or 2 arguments but got %zu", args->count);
        }

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = array->array->count - 2;
                f = args->items[0];
                if (array->array->count == 0) {
                        vm_panic("foldRight called on array with 1 argument");
                }
                v = array->array->items[start + 1];
        } else {
                start = array->array->count - 1;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the foldRight method on array");
        }

        int n = array->array->count;
        for (int i = start; i < n; ++i) {
                v = vm_eval_function2(&f, &array->array->items[i], &v);
        }

        return v;
}

static struct value
array_scan_left(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("the scanLeft method on arrays expects 1 or 2 arguments but got %zu", args->count);
        }

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = 1;
                f = args->items[0];
                if (array->array->count == 0) {
                        vm_panic("scanLeft called on empty array with 1 argument");
                }
                v = array->array->items[0];
        } else {
                start = 0;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the scanLeft method on array");
        }

        int n = array->array->count;
        for (int i = start; i < n; ++i) {
                v = vm_eval_function2(&f, &v, &array->array->items[i]);
                array->array->items[i] = v;
        }

        return *array;
}

static struct value
array_scan_right(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2) {
                vm_panic("the scanRight method on arrays expects 1 or 2 arguments but got %zu", args->count);
        }

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = array->array->count - 2;
                f = args->items[0];
                if (array->array->count == 0) {
                        vm_panic("scanRight called on empty array with 1 argument");
                }
                v = array->array->items[start + 1];
        } else {
                start = array->array->count - 1;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the scanRight method on array");
        }

        for (int i = start; i >= 0; --i) {
                v = vm_eval_function2(&f, &array->array->items[i], &v);
                array->array->items[i] = v;
        }

        return *array;
}

static struct value
array_reverse(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the reverse method on arrays expects no arguments but got %zu", args->count);
        }

        int lo = 0;
        int hi = array->array->count - 1;

        struct value t;
        while (lo < hi) {
                t = array->array->items[lo];
                array->array->items[lo] = array->array->items[hi];
                array->array->items[hi] = t;

                ++lo;
                --hi;
        }

        return *array;
}

static struct value
array_clone(struct value *array, value_vector *args)
{
        if (args->count != 0) {
                vm_panic("the clone method on arrays expects no arguments but got %zu", args->count);
        }

        struct value v = *array;
        v.array = value_array_clone(v.array);

        return v;
}

static struct value
array_reversed(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_reverse(&clone, args);
}

static struct value
array_sorted(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_sort(&clone, args);
}

static struct value
array_shuffled(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_shuffle(&clone, args);
}

static struct value
array_enumerated(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_enumerate(&clone, args);
}

static struct value
array_zipped(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_zip(&clone, args);
}

static struct value
array_mapped(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_map(&clone, args);
}

static struct value
array_filtered(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_filter(&clone, args);
}

static struct value
array_scanned_left(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_scan_left(&clone, args);
}

static struct value
array_scanned_right(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_scan_right(&clone, args);
}

static struct value
array_interspersed(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_intersperse(&clone, args);
}

static struct value
array_sort_by(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the sortBy method on arrays expects 1 argument but got %zu", args->count);
        }

        struct value f = args->items[0];

        if (!CALLABLE(f)) {
                vm_panic("non-function passed to the sortBy method on array");
        }

        comparison_fn = &f;

        if (f.type == VALUE_FUNCTION && f.param_symbols.count > 1) {
                qsort(array->array->items, array->array->count, sizeof (struct value), compare_by2);
        } else {
                qsort(array->array->items, array->array->count, sizeof (struct value), compare_by);
        }

        return *array;
}

static struct value
array_sorted_by(struct value *array, value_vector *args)
{
        struct value clone = array_clone(array, &no_args);
        return array_sort_by(&clone, args);
}

static struct value
array_push(struct value *array, value_vector *args)
{
        if (args->count != 1) {
                vm_panic("the push method on arrays expects 1 argument but got %zu", args->count);
        }

        value_array_push(array->array, args->items[0]);

        return NIL;
}

static struct value
array_insert(struct value *array, value_vector *args)
{
        if (args->count != 2) {
                vm_panic("the insert method on arrays expects 2 arguments but got %zu", args->count);
        }

        struct value i = args->items[0];
        struct value v = args->items[1];

        if (i.type != VALUE_INTEGER) {
                vm_panic("non-integer passed as the index to the insert method on array");
        }

        int index = i.integer;

        if (index < 0) {
                index += array->array->count + 1;
        }
        if (index < 0 || index > array->array->count) {
                vm_panic("array index passed to insert is out of range: %d", index);
        }

        value_array_push(array->array, NIL);

        memmove(array->array->items + index + 1, array->array->items + index, (array->array->count - index - 1) * sizeof (struct value));
        array->array->items[index] = v;

        return *array;
}

static struct value
array_pop(struct value *array, value_vector *args)
{
        if (args->count == 0) {
                if (array->array->count == 0) {
                        vm_panic("attempt to pop from an empty array");
                }
                return array->array->items[--array->array->count];
        }

        if (args->count == 1) {
                struct value arg = args->items[0];
                if (arg.type != VALUE_INTEGER) {
                        vm_panic("the argument to pop must be an integer");
                }
                if (arg.integer < 0) {
                        arg.integer += array->array->count;
                }
                if (arg.integer < 0 || arg.integer >= array->array->count) {
                        vm_panic("array index passed to pop is out of range");
                }
                struct value out;
                vec_pop_ith(*array->array, arg.integer, out);
                return out;
        }

        vm_panic("the pop method on arrays expects 0 or 1 argument(s) but got %zu", args->count);
}

DEFINE_METHOD_TABLE(
        { .name = "clone",        .func = array_clone          },
        { .name = "consumeWhile", .func = array_consume_while  },
        { .name = "contains?",    .func = array_contains       },
        { .name = "drop",         .func = array_drop           },
        { .name = "drop!",        .func = array_drop_mut       },
        { .name = "dropWhile",    .func = array_drop_while     },
        { .name = "dropWhile!",   .func = array_drop_while_mut },
        { .name = "each",         .func = array_each           },
        { .name = "enumerate",    .func = array_enumerated     },
        { .name = "enumerate!",   .func = array_enumerate      },
        { .name = "filter",       .func = array_filtered       },
        { .name = "filter!",      .func = array_filter         },
        { .name = "foldLeft",     .func = array_fold_left      },
        { .name = "foldRight",    .func = array_fold_right     },
        { .name = "group",        .func = array_group          },
        { .name = "groupBy",      .func = array_group_by       },
        { .name = "insert",       .func = array_insert         },
        { .name = "intersperse",  .func = array_interspersed   },
        { .name = "intersperse!", .func = array_intersperse    },
        { .name = "len",          .func = array_length         },
        { .name = "map",          .func = array_mapped         },
        { .name = "map!",         .func = array_map            },
        { .name = "max",          .func = array_max            },
        { .name = "maxBy",        .func = array_max_by         },
        { .name = "min",          .func = array_min            },
        { .name = "minBy",        .func = array_min_by         },
        { .name = "pop",          .func = array_pop            },
        { .name = "push",         .func = array_push           },
        { .name = "reverse",      .func = array_reversed       },
        { .name = "reverse!",     .func = array_reverse        },
        { .name = "scanLeft",     .func = array_scanned_left   },
        { .name = "scanLeft!",    .func = array_scan_left      },
        { .name = "scanRight",    .func = array_scanned_right  },
        { .name = "scanRight!",   .func = array_scan_right     },
        { .name = "shuffle",      .func = array_shuffled       },
        { .name = "shuffle!",     .func = array_shuffle        },
        { .name = "slice",        .func = array_slice          },
        { .name = "slice!",       .func = array_slice_mut      },
        { .name = "sort",         .func = array_sorted         },
        { .name = "sort!",        .func = array_sort           },
        { .name = "sortBy",       .func = array_sorted_by      },
        { .name = "sortBy!",      .func = array_sort_by        },
        { .name = "sum",          .func = array_sum            },
        { .name = "take",         .func = array_take           },
        { .name = "take!",        .func = array_take_mut       },
        { .name = "takeWhile",    .func = array_take_while     },
        { .name = "takeWhile!",   .func = array_take_while_mut },
        { .name = "zip",          .func = array_zipped         },
        { .name = "zip!",         .func = array_zip            },
);

DEFINE_METHOD_LOOKUP(array)
