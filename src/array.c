#include <stdlib.h>
#include <string.h>

#include "value.h"
#include "dict.h"
#include "log.h"
#include "functions.h"
#include "operators.h"
#include "util.h"
#include "vm.h"

static struct value *comparison_fn;

static int
compare_by(void const *v1, void const *v2)
{
        struct value k1 = value_apply_callable(comparison_fn, (struct value *)v1);
        gc_push(&k1);

        struct value k2 = value_apply_callable(comparison_fn, (struct value *)v2);
        gc_push(&k2);

        int result = value_compare(&k1, &k2);

        gc_pop();
        gc_pop();

        return result;
}

static int
compare_by2(void const *v1, void const *v2)
{
        struct value v = vm_eval_function2(comparison_fn, (struct value *)v1, (struct value *)v2);
        gc_push(&v);

        int result;

        if (v.type == VALUE_INTEGER)
                result = v.integer;
        else
                result = value_truthy(&v) ? 1 : -1;

        gc_pop();

        return result;
}

inline static void
shrink(struct value *array)
{
        if (array->array->capacity > 8 * array->array->count || (array->array->capacity - array->array->count) > 1000) {
                array->array->capacity = array->array->count;
                if (array->array->count == 0)
                        free(array->array->items), array->array->items = NULL;
                else
                        resize(array->array->items, array->array->count * sizeof (struct value));
        }
}

static struct value
array_push(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the push method on arrays expects 1 argument but got %zu", args->count);

        value_array_push(array->array, args->items[0]);

        return NIL;
}

static struct value
array_insert(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("the insert method on arrays expects 2 arguments but got %zu", args->count);

        struct value i = args->items[0];
        struct value v = args->items[1];

        if (i.type != VALUE_INTEGER)
                vm_panic("non-integer passed as the index to the insert method on array");

        int index = i.integer;

        if (index < 0)
                index += array->array->count + 1;
        if (index < 0 || index > array->array->count)
                vm_panic("array index passed to insert is out of range: %d", index);

        value_array_push(array->array, NIL);

        memmove(array->array->items + index + 1, array->array->items + index, (array->array->count - index - 1) * sizeof (struct value));
        array->array->items[index] = v;

        return *array;
}

static struct value
array_pop(struct value *array, value_vector *args)
{
        struct value result;

        if (args->count == 0) {
                if (array->array->count == 0)
                        vm_panic("attempt to pop from an empty array");
                result = array->array->items[--array->array->count];
        } else if (args->count == 1) {
                struct value arg = args->items[0];
                if (arg.type != VALUE_INTEGER)
                        vm_panic("the argument to pop must be an integer");
                if (arg.integer < 0)
                        arg.integer += array->array->count;
                if (arg.integer < 0 || arg.integer >= array->array->count)
                        vm_panic("array index passed to pop is out of range");
                vec_pop_ith(*array->array, arg.integer, result);
        } else {
                vm_panic("the pop method on arrays expects 0 or 1 argument(s) but got %zu", args->count);
        }

        shrink(array);

        return result;
}

static struct value
array_swap(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("array.swap() expects 2 arguments but got %zu", args->count);

        struct value i = args->items[0];
        struct value j = args->items[1];

        if (i.type != VALUE_INTEGER || j.type != VALUE_INTEGER)
                vm_panic("the arguments to array.swap() must be integers");

        if (i.integer < 0)
                i.integer += array->array->count;

        if (j.integer < 0)
                j.integer += array->array->count;

        if (i.integer < 0 || i.integer >= array->array->count
         || j.integer < 0 || j.integer >= array->array->count) {
                vm_panic("invalid indices passed to array.swap(): (%d, %d)", (int) i.integer, (int) j.integer);
           }

        struct value tmp = array->array->items[i.integer];
        array->array->items[i.integer] = array->array->items[j.integer];
        array->array->items[j.integer] = tmp;

        return *array;
}

static struct value
array_slice_mut(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("array.slice!() expects 2 arguments but got %zu", args->count);
        
        struct value start = args->items[0];
        struct value count = args->items[1];

        if (start.type != VALUE_INTEGER)
                vm_panic("non-integer passed as first argument to array.slice!()");

        if (count.type != VALUE_INTEGER)
                vm_panic("non-integer passed as second argument to array.slice!()");

        int s = start.integer;
        int n = count.integer;

        if (s < 0)
                s += array->array->count;
        if (s < 0)
                vm_panic("start index passed to array.slice!() is out of range");

        s = min(s, array->array->count);
        n = min(n, array->array->count - s);

        memmove(array->array->items, array->array->items + s, n * sizeof (struct value));
        array->array->count = n;

        shrink(array);

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

        struct value a;
        gc_push(&a);

        for (int i = 0; i < n; ++i) {
                a = ARRAY(value_array_new());
                vec_push(*a.array, array->array->items[i]);
                vec_push(*a.array, other.array->items[i]);
                array->array->items[i] = a;
        }

        gc_pop();

        /*
         * TODO: implement something like this in vec.h
         */
        array->array->count = n;
        shrink(array);

        return *array;
}

static struct value
array_zip_with(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("array.zipWith() expects 2 arguments but got %zu", args->count);

        struct value f = args->items[0];
        if (!CALLABLE(f))
                vm_panic("the first argument to array.zipWith() must be callable");

        struct value other = args->items[1];
        if (other.type != VALUE_ARRAY)
                vm_panic("the argument to array.zip() must be an array");

        int n = min(array->array->count, other.array->count);

        struct value a;
        gc_push(&a);

        for (int i = 0; i < n; ++i) {
                a = vm_eval_function2(&f, &array->array->items[i], &other.array->items[i]);
                array->array->items[i] = a;
        }

        gc_pop();

        /*
         * TODO: implement something like this in vec.h
         */
        array->array->count = n;
        shrink(array);

        return *array;
}

static struct value
array_map_cons(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("array.mapCons() expects 2 arguments but got %zu", args->count);

        struct value k = args->items[0];
        if (k.type != VALUE_INTEGER)
                vm_panic("the first argument to array.mapCons() must be an integer");

        if (k.integer <= 0)
                vm_panic("the first argument to array.mapCons() must be positive");

        struct value f = args->items[1];
        if (!CALLABLE(f))
                vm_panic("the second argument to array.mapCons() must be callable");

        int n = array->array->count - k.integer + 1;

        struct value sub = NIL;
        gc_push(&sub);

        for (int i = 0; i < n; ++i) {
                sub = ARRAY(value_array_new());
                vec_push_n(*sub.array, array->array->items + i, k.integer);
                array->array->items[i] = value_apply_callable(&f, &sub);
        }

        gc_pop();

        array->array->count = n;
        shrink(array);

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
        NOGC(result.array);
        value_array_reserve(result.array, n);
        OKGC(result.array);
        memmove(result.array->items, array->array->items + s, n * sizeof (struct value));
        result.array->count = n;

        return result;
}

static struct value
array_sort(struct value *array, value_vector *args)
{
        int i;
        int n;

        switch (args->count) {
        case 0:
                i = 0;
                n = array->array->count;
                break;
        case 2:
                if (args->items[1].type != VALUE_INTEGER)
                        vm_panic("the second argument to array.sort() must be an integer");
                n = args->items[1].integer;
        case 1:
                if (args->items[0].type != VALUE_INTEGER)
                        vm_panic("the first argument to array.sort() must be an integer");
                i = args->items[0].integer;
                if (args->count == 1)
                        n = array->array->count - i;
                break;
        default:
                vm_panic("array.sort() expects 0, 1, or 2 arguments but got %zu", args->count);
        }

        if (i < 0)
                i += array->array->count;

        if (n < 0 || i < 0 || i + n > array->array->count)
                vm_panic("invalid index passed to array.sort()");

        qsort(array->array->items + i, n, sizeof (struct value), value_compare);

        return *array;
}

static struct value
array_next_permutation(struct value *array, value_vector *args)
{
#define CMP(i, j) value_compare(&array->array->items[i], &array->array->items[j])
        if (args->count != 0)
                vm_panic("array.nextPermutation() expects no arguments but got %zu", args->count);

        for (int i = array->array->count - 1; i > 0; --i) {
                if (CMP(i - 1, i) < 0) {
                        int j = i;
                        for (int k = i + 1; k < array->array->count; ++k)
                                if (CMP(k, j) < 0 && CMP(k, i - 1) > 0)
                                        j = k;

                        struct value t = array->array->items[i - 1];
                        array->array->items[i - 1] = array->array->items[j];
                        array->array->items[j] = t;

                        array_sort(array, &(value_vector){ .count = 1, .items = &INTEGER(i) });

                        return *array;
                }
        }

        return NIL;
#undef CMP
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
        shrink(array);

        return *array;
}

static struct value
array_take_while(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.takeWhile!() expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];

        if (!CALLABLE(f))
                vm_panic("non-callable predicate passed to array.takeWhile!()");

        int keep = 0;
        for (int i = 0; i < array->array->count; ++i)
                if (value_apply_predicate(&f, &array->array->items[i]))
                        ++keep;
                else
                        break;

        struct value result = ARRAY(value_array_new());
        NOGC(result.array);
        value_array_reserve(result.array, keep);
        OKGC(result.array);
        memmove(result.array->items, array->array->items, keep * sizeof (struct value));
        result.array->count = keep;

        return result;
}

static struct value
array_drop_while_mut(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.dropWhile!() expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];

        if (!CALLABLE(f))
                vm_panic("non-callable predicate passed to array.dropWhile!()");

        int drop = 0;
        for (int i = 0; i < array->array->count; ++i)
                if (value_apply_predicate(&f, &array->array->items[i]))
                        ++drop;
                else
                        break;

        memmove(array->array->items, array->array->items + drop, (array->array->count - drop) * sizeof (struct value));
        array->array->count -= drop;
        shrink(array);

        return *array;
}

static struct value
array_drop_while(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.dropWhile() expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];

        if (!CALLABLE(f))
                vm_panic("non-callable predicate passed to array.dropWhile()");

        int drop = 0;
        for (int i = 0; i < array->array->count; ++i)
                if (value_apply_predicate(&f, &array->array->items[i]))
                        ++drop;
                else
                        break;

        int n = array->array->count - drop;
        struct value result = ARRAY(value_array_new());
        NOGC(result.array);
        value_array_reserve(result.array, n);
        OKGC(result.array);
        memmove(result.array->items, array->array->items + drop, n * sizeof (struct value));
        result.array->count = n;

        return result;
}

static struct value
array_uniq(struct value *array, value_vector *args)
{
        struct value *f = NULL;

        if (args->count == 1)
                f = &args->items[0];
        else if (args->count != 0)
                vm_panic("array.uniq() expects 0 or 1 arguments but got %zu", args->count);

        if (f != NULL && !CALLABLE(*f))
                vm_panic("the argument to array.uniq() must be callable");

        struct value d = DICT(dict_new());
        gc_push(&d);

        int n = 0;
        for (int i = 0; i < array->array->count; ++i) {
                struct value e = array->array->items[i];
                struct value k = (f == NULL) ? e : vm_eval_function(f, &e);
                struct value *v = dict_put_key_if_not_exists(d.dict, k);
                if (v->type == VALUE_NIL) {
                        *v = e;
                        array->array->items[n++] = e;
                }
        }

        gc_pop();
        array->array->count = n;

        return *array;
}

static struct value
array_take_mut(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.take!() expects 1 argument but got %zu", args->count);

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER)
                vm_panic("non-integer passed to array.take!()");

        array->array->count = min(array->array->count, n.integer);
        shrink(array);

        return *array;
}

static struct value
array_take(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.take() expects 1 argument but got %zu", args->count);

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER)
                vm_panic("non-integer passed to array.take!()");

        struct value result = ARRAY(value_array_new());

        int count = min(n.integer, array->array->count);

        NOGC(result.array);
        value_array_reserve(result.array, count);
        OKGC(result.array);

        memmove(result.array->items, array->array->items, count * sizeof (struct value));
        result.array->count = count;

        return result;
}

static struct value
array_drop_mut(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.drop!() expects 1 argument but got %zu", args->count);

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER)
                vm_panic("non-integer passed to array.drop!()");

        int d = min(array->array->count, n.integer);

        memmove(array->array->items, array->array->items + d, (array->array->count - d) * sizeof (struct value));
        array->array->count -= d;
        shrink(array);

        return *array;
}

static struct value
array_drop(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.drop() expects 1 argument but got %zu", args->count);

        struct value n = args->items[0];

        if (n.type != VALUE_INTEGER)
                vm_panic("non-integer passed to array.drop()");

        struct value result = ARRAY(value_array_new());

        int d = min(n.integer, array->array->count);
        int count = array->array->count - d;

        NOGC(result.array);
        value_array_reserve(result.array, count);
        OKGC(result.array);

        memcpy(result.array->items, array->array->items + d, count * sizeof (struct value));
        result.array->count = count;

        return result;
}

static struct value
array_sum(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the sum method on arrays expects no arguments but got %zu", args->count);

        if (array->array->count == 0)
                return NIL;

        struct value sum, v;
        sum = array->array->items[0];

        gc_push(&sum);

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                sum = binary_operator_addition(&sum, &v);
        }

        gc_pop();

        return sum;
}

static struct value
array_join(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.join() expects 1 argument but got %zu", args->count);

        if (array->array->count == 0)
                return NIL;

        struct value sep = args->items[0];
        if (sep.type != VALUE_STRING)
                vm_panic("the argument to array.join() must be a string");

        struct value sum = builtin_str(&(value_vector){ .count = 1, .items = &array->array->items[0] });
        struct value v = NIL;

        gc_push(&sum);
        gc_push(&v);

        for (int i = 1; i < array->array->count; ++i) {
                v = builtin_str(&(value_vector){ .count = 1, .items = &array->array->items[i] });
                sum = binary_operator_addition(&sum, &sep);
                sum = binary_operator_addition(&sum, &v);
        }

        gc_pop();
        gc_pop();

        return sum;
}

static struct value
array_consume_while(struct value *array, value_vector *args)
{
        if (args->count != 2)
                vm_panic("array.consumeWhile() expects 2 arguments but got %zu", args->count);

        struct value f = args->items[0];
        struct value p = args->items[1];

        if (!CALLABLE(f))
                vm_panic("invalid source passed to array.consumeWhile()");

        if (!CALLABLE(p))
                vm_panic("invalid predicate passed to array.consumeWhile()");

        struct value v = NIL;
        gc_push(&v);

        for (;;) {
                v = vm_eval_function(&f, NULL);
                if (value_apply_predicate(&p, &v))
                        value_array_push(array->array, v);
                else
                        break;
        }

        gc_pop();

        return *array;
}

static struct value
array_groups_of(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.groupsOf() expects 1 argument but got %zu", args->count);

        struct value size = args->items[0];
        if (size.type != VALUE_INTEGER)
                vm_panic("the argument to array.groupsOf() must be an integer");

        if (size.integer <= 0)
                vm_panic("the argument to array.groupsOf() must be positive");

        int n = 0;
        int i = 0;
        while (i + size.integer < array->array->count) {
                struct array *group = value_array_new();
                NOGC(group);
                vec_push_n(*group, array->array->items + i, size.integer);
                OKGC(group);
                array->array->items[n++] = ARRAY(group);
                i += size.integer;
        }

        if (i != array->array->count) {
                struct array *last = value_array_new();
                NOGC(last);
                vec_push_n(*last, array->array->items + i, array->array->count - i);
                OKGC(last);
                array->array->items[n++] = ARRAY(last);
        }

        array->array->count = n;
        shrink(array);
        
        return *array;
}

static struct value
array_group_by(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.groupBy() expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];
        
        if (!CALLABLE(f))
                vm_panic("the argument to array.groupBy() must be callable");

        struct value v1, v2;
        v1 = v2 = NIL;

        gc_push(&v1);
        gc_push(&v2);

        int len = 0;
        for (int i = 0; i < array->array->count; ++i) {
                struct value group = ARRAY(value_array_new());
                NOGC(group.array);
                struct value e = array->array->items[i];
                v1 = value_apply_callable(&f, &e);
                value_array_push(group.array, e);
                while (i + 1 < array->array->count) {
                        v2 = value_apply_callable(&f, &array->array->items[i + 1]);
                        if (value_test_equality(&v1, &v2))
                                value_array_push(group.array, array->array->items[++i]);
                        else
                                break;
                }
                OKGC(group.array);
                array->array->items[len++] = group;
        }

        gc_pop();
        gc_pop();

        array->array->count = len;
        shrink(array);

        return *array;
}

static struct value
array_group(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("array.group() expects 0 arguments but got %zu", args->count);

        int len = 0;
        for (int i = 0; i < array->array->count; ++i) {
                struct value group = ARRAY(value_array_new());
                NOGC(group.array);
                value_array_push(group.array, array->array->items[i]);
                while (i + 1 < array->array->count && value_test_equality(&array->array->items[i], &array->array->items[i + 1]))
                        value_array_push(group.array, array->array->items[++i]);
                OKGC(group.array);
                array->array->items[len++] = group;
        }

        array->array->count = len;
        shrink(array);

        return *array;
}

static struct value
array_intersperse(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the intersperse method on arrays expects 1 argument but got %zu", args->count);

        struct value v = args->items[0];

        int n = array->array->count - 1;
        if (n < 1)
                return *array;

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
        if (args->count != 0)
                vm_panic("the min method on arrays expects no arguments but got %zu", args->count);

        if (array->array->count == 0)
                vm_panic("min called on empty array");

        struct value min, v;
        min = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                if (value_compare(&v, &min) < 0)
                        min = v;
        }

        return min;
}

static struct value
array_min_by(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the minBy method on arrays expects 1 argument but got %zu", args->count);

        if (array->array->count == 0)
                vm_panic("minBy called on empty array");

        struct value f = args->items[0];
        if (!CALLABLE(f))
                vm_panic("non-function passed to the minBy method on array");

        struct value min, v, k, r;
        min = array->array->items[0];

        gc_push(&k);
        gc_push(&r);

        r = k = NIL;

        if (f.type == VALUE_FUNCTION && f.params > 1) {
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function2(&f, &v, &min);
                        if ((r.type != VALUE_INTEGER && !value_truthy(&r)) || r.integer < 0)
                                min = v;

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

        gc_pop();
        gc_pop();

        return min;
}

static struct value
array_max(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the max method on arrays expects no arguments but got %zu", args->count);

        if (array->array->count == 0)
                vm_panic("max called on empty array");

        struct value max, v;
        max = array->array->items[0];

        for (int i = 1; i < array->array->count; ++i) {
                v = array->array->items[i];
                if (value_compare(&v, &max) > 0)
                        max = v;
        }

        return max;
}

static struct value
array_max_by(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the maxBy method on arrays expects 1 argument but got %zu", args->count);

        if (array->array->count == 0)
                vm_panic("maxBy called on empty array");

        struct value f = args->items[0];
        if (!CALLABLE(f))
                vm_panic("non-function passed to the maxBy method on array");

        struct value max, v, k, r;
        max = array->array->items[0];

        gc_push(&k);
        gc_push(&r);

        k = r = NIL;

        if (f.type == VALUE_FUNCTION && f.params > 1) {
                for (int i = 1; i < array->array->count; ++i) {
                        v = array->array->items[i];
                        r = vm_eval_function2(&f, &v, &max);
                        if ((r.type != VALUE_INTEGER && value_truthy(&r)) || r.integer > 0)
                                max = v;

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

        gc_pop();
        gc_pop();

        return max;
}

static struct value
array_length(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("array.len() expects no arguments but got %zu", args->count);

        return INTEGER(array->array->count);
}

static struct value
array_shuffle(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the shuffle! method on arrays expects no arguments but got %zu", args->count);

        struct value t;
        int n = array->array->count;
        for (int i = n - 1; i > 0; --i) {
                int j = rand() % (i + 1);
                t = array->array->items[i];
                array->array->items[i] = array->array->items[j];
                array->array->items[j] = t;
        }

        return *array;
}

static struct value
array_map(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the map method on arrays expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];

        if (!CALLABLE(f))
                vm_panic("non-function passed to the map method on array");

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                array->array->items[i] = value_apply_callable(&f, &array->array->items[i]);

        return *array;
}

static struct value
array_enumerate(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the enumerate method on arrays expects no arguments but got %zu", args->count);

        int n = array->array->count;
        for (int i = 0; i < n; ++i) {
                struct value entry = ARRAY(value_array_new());
                NOGC(entry.array);
                value_array_push(entry.array, INTEGER(i));
                value_array_push(entry.array, array->array->items[i]);
                OKGC(entry.array);
                array->array->items[i] =  entry;
        }

        return *array;
}

static struct value
array_filter(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the filter method on arrays expects 1 argument but got %zu", args->count);

        struct value pred = args->items[0];

        if (!CALLABLE(pred))
                vm_panic("non-predicate passed to the filter method on array");

        int n = array->array->count;
        int j = 0;
        for (int i = 0; i < n; ++i)
                if (value_apply_predicate(&pred, &array->array->items[i]))
                        array->array->items[j++] = array->array->items[i];

        array->array->count = j;
        shrink(array);

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
array_search(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("array.search() expects 1 argument but got %zu", args->count);

        struct value v = args->items[0];

        int n = array->array->count;
        for (int i = 0; i < n; ++i)
                if (value_test_equality(&v, &array->array->items[i]))
                        return INTEGER(i);

        return NIL;
}

static struct value
array_each(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the each method on arrays expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];

        if (f.type != VALUE_FUNCTION && f.type != VALUE_BUILTIN_FUNCTION && f.type != VALUE_METHOD && f.type != VALUE_BUILTIN_METHOD)
                vm_panic("non-function passed to the each method on array");

        int n = array->array->count;

        for (int i = 0; i < n; ++i)
                vm_eval_function(&f, &array->array->items[i]);

        return *array;
}

static struct value
array_fold_left(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2)
                vm_panic("the foldLeft method on arrays expects 1 or 2 arguments but got %zu", args->count);

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = 1;
                f = args->items[0];
                if (array->array->count == 0)
                        vm_panic("foldLeft called on empty array with 1 argument");
                v = array->array->items[0];
        } else {
                start = 0;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f))
                vm_panic("non-function passed to the foldLeft method on array");

        gc_push(&v);

        int n = array->array->count;
        for (int i = start; i < n; ++i)
                v = vm_eval_function2(&f, &v, &array->array->items[i]);

        gc_pop();

        return v;
}

/* TODO: fix this */
static struct value
array_fold_right(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2)
                vm_panic("the foldRight method on arrays expects 1 or 2 arguments but got %zu", args->count);

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = array->array->count - 2;
                f = args->items[0];
                if (array->array->count == 0)
                        vm_panic("foldRight called on empty array with 1 argument");
                v = array->array->items[start + 1];
        } else {
                start = array->array->count - 1;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f))
                vm_panic("non-function passed to the foldRight method on array");

        gc_push(&v);

        for (int i = start; i >= 0; --i)
                v = vm_eval_function2(&f, &array->array->items[i], &v);

        gc_pop();

        return v;
}

static struct value
array_scan_left(struct value *array, value_vector *args)
{
        if (args->count != 1 && args->count != 2)
                vm_panic("the scanLeft method on arrays expects 1 or 2 arguments but got %zu", args->count);

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = 1;
                f = args->items[0];
                if (array->array->count == 0)
                        vm_panic("scanLeft called on empty array with 1 argument");
                v = array->array->items[0];
        } else {
                start = 0;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f))
                vm_panic("non-function passed to the scanLeft method on array");

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
        if (args->count != 1 && args->count != 2)
                vm_panic("the scanRight method on arrays expects 1 or 2 arguments but got %zu", args->count);

        int start;
        struct value f, v;

        if (args->count == 1) {
                start = array->array->count - 2;
                f = args->items[0];
                if (array->array->count == 0)
                        vm_panic("scanRight called on empty array with 1 argument");
                v = array->array->items[start + 1];
        } else {
                start = array->array->count - 1;
                f = args->items[1];
                v = args->items[0];
        }

        if (!CALLABLE(f))
                vm_panic("non-function passed to the scanRight method on array");

        for (int i = start; i >= 0; --i) {
                v = vm_eval_function2(&f, &array->array->items[i], &v);
                array->array->items[i] = v;
        }

        return *array;
}

static struct value
array_reverse(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the reverse method on arrays expects no arguments but got %zu", args->count);

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
array_sort_by(struct value *array, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the sortBy method on arrays expects 1 argument but got %zu", args->count);

        struct value f = args->items[0];
        if (!CALLABLE(f))
                vm_panic("non-function passed to the sortBy method on array");

        comparison_fn = &f;

        if (f.type == VALUE_FUNCTION && f.params > 1)
                qsort(array->array->items, array->array->count, sizeof (struct value), compare_by2);
        else
                qsort(array->array->items, array->array->count, sizeof (struct value), compare_by);

        return *array;
}

static struct value
array_clone(struct value *array, value_vector *args)
{
        if (args->count != 0)
                vm_panic("the clone method on arrays expects no arguments but got %zu", args->count);

        struct value v = *array;
        v.array = value_array_clone(v.array);

        return v;
}

#define DEFINE_NO_MUT(name) \
        static struct value \
        array_ ## name ## _no_mut(struct value *array, value_vector *args) \
        { \
                struct value clone = array_clone(array, &NO_ARGS); \
                gc_push(&clone); \
                struct value result = array_ ## name(&clone, args); \
                gc_pop(); \
                return result; \
        }

DEFINE_NO_MUT(enumerate);
DEFINE_NO_MUT(filter);
DEFINE_NO_MUT(group);
DEFINE_NO_MUT(group_by);
DEFINE_NO_MUT(groups_of);
DEFINE_NO_MUT(intersperse);
DEFINE_NO_MUT(map);
DEFINE_NO_MUT(map_cons);
DEFINE_NO_MUT(reverse);
DEFINE_NO_MUT(scan_left);
DEFINE_NO_MUT(scan_right);
DEFINE_NO_MUT(shuffle);
DEFINE_NO_MUT(sort);
DEFINE_NO_MUT(sort_by);
DEFINE_NO_MUT(uniq);
DEFINE_NO_MUT(zip);
DEFINE_NO_MUT(zip_with);
DEFINE_NO_MUT(next_permutation);

DEFINE_METHOD_TABLE(
        { .name = "clone",             .func = array_clone                   },
        { .name = "consumeWhile",      .func = array_consume_while           },
        { .name = "contains?",         .func = array_contains                },
        { .name = "drop",              .func = array_drop                    },
        { .name = "drop!",             .func = array_drop_mut                },
        { .name = "dropWhile",         .func = array_drop_while              },
        { .name = "dropWhile!",        .func = array_drop_while_mut          },
        { .name = "each",              .func = array_each                    },
        { .name = "enumerate",         .func = array_enumerate_no_mut        },
        { .name = "enumerate!",        .func = array_enumerate               },
        { .name = "filter",            .func = array_filter_no_mut           },
        { .name = "filter!",           .func = array_filter                  },
        { .name = "foldLeft",          .func = array_fold_left               },
        { .name = "foldRight",         .func = array_fold_right              },
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
        { .name = "mapCons",           .func = array_map_cons_no_mut         },
        { .name = "mapCons!",          .func = array_map_cons                },
        { .name = "max",               .func = array_max                     },
        { .name = "maxBy",             .func = array_max_by                  },
        { .name = "min",               .func = array_min                     },
        { .name = "minBy",             .func = array_min_by                  },
        { .name = "nextPermutation",   .func = array_next_permutation_no_mut },
        { .name = "nextPermutation!",  .func = array_next_permutation        },
        { .name = "pop",               .func = array_pop                     },
        { .name = "push",              .func = array_push                    },
        { .name = "reverse",           .func = array_reverse_no_mut          },
        { .name = "reverse!",          .func = array_reverse                 },
        { .name = "scanLeft",          .func = array_scan_left_no_mut        },
        { .name = "scanLeft!",         .func = array_scan_left               },
        { .name = "scanRight",         .func = array_scan_right_no_mut       },
        { .name = "scanRight!",        .func = array_scan_right              },
        { .name = "search",            .func = array_search                  },
        { .name = "shuffle",           .func = array_shuffle_no_mut          },
        { .name = "shuffle!",          .func = array_shuffle                 },
        { .name = "slice",             .func = array_slice                   },
        { .name = "slice!",            .func = array_slice_mut               },
        { .name = "sort",              .func = array_sort_no_mut             },
        { .name = "sort!",             .func = array_sort                    },
        { .name = "sortBy",            .func = array_sort_by_no_mut          },
        { .name = "sortBy!",           .func = array_sort_by                 },
        { .name = "sum",               .func = array_sum                     },
        { .name = "swap",              .func = array_swap                    },
        { .name = "take",              .func = array_take                    },
        { .name = "take!",             .func = array_take_mut                },
        { .name = "takeWhile",         .func = array_take_while              },
        { .name = "takeWhile!",        .func = array_take_while_mut          },
        { .name = "uniq",              .func = array_uniq_no_mut             },
        { .name = "uniq!",             .func = array_uniq                    },
        { .name = "zip",               .func = array_zip_no_mut              },
        { .name = "zip!",              .func = array_zip                     },
        { .name = "zipWith",           .func = array_zip_with_no_mut         },
        { .name = "zipWith!",          .func = array_zip_with                },
);

DEFINE_METHOD_LOOKUP(array)
