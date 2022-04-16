#include <string.h>

#include "alloc.h"
#include "value.h"
#include "operators.h"
#include "class.h"
#include "dict.h"
#include "vm.h"
#include "gc.h"

static struct value
str_concat(struct value const *s1, struct value const *s2)
{
        size_t n = s1->bytes + s2->bytes;
        char *s = value_string_alloc(n);

        memcpy(s, s1->string, s1->bytes);
        memcpy(s + s1->bytes, s2->string, s2->bytes);

        return STRING(s, n);
}

struct value
binary_operator_addition(struct value const *left, struct value const *right)
{

        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(left->class, "+");
                if (f == NULL)
                        goto Fail;
                return vm_eval_function(f, left, right, NULL);
        }

		if (left->type == VALUE_PTR) {
			if (right->type != VALUE_INTEGER) {
				vm_panic("attempt to add non-integer to pointer: %s", value_show(right));
			}

			return PTR((char *)left->ptr + right->integer);
		}

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real + right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer + right->real);

        if (left->type != right->type)
                vm_panic("the operands to + must have the same type");

        struct value v;

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer + right->integer);
        case VALUE_REAL:    return REAL(left->real + right->real);
        case VALUE_STRING:  return str_concat(left, right);
        case VALUE_ARRAY:
                gc_push((struct value *)left);
                gc_push((struct value *)right);
                v = ARRAY(value_array_clone(left->array));
                NOGC(v.array);
                value_array_extend(v.array, right->array);
                OKGC(v.array);
                gc_pop();
                gc_pop();
                return v;
        case VALUE_DICT:
                gc_push((struct value *)left);
                gc_push((struct value *)right);
                struct value v = dict_clone((struct value *)left, 0, NULL);
                gc_push(&v);
                vm_push((struct value  *)right);
                dict_update(&v, 1, NULL);
                vm_pop();
                gc_pop();
                gc_pop();
                gc_pop();
                return v;
        default:
        Fail:
                vm_panic("+ applied to operands of invalid type");
                break;
        }
}

struct value
binary_operator_multiplication(struct value const *left, struct value const *right)
{

        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(left->class, "*");
                if (f == NULL)
                        goto Fail;
                return vm_eval_function(f, left, right, NULL);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real * right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer * right->real);

        if (left->type != right->type)
                vm_panic("the operands to * must have the same type");

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer * right->integer);
        case VALUE_REAL:    return REAL(left->real * right->real);
        case VALUE_ARRAY:;
                struct value a = ARRAY(value_array_new());
                gc_push(&a);
                gc_push(left);
                gc_push(right);
                for (int i = 0; i < left->array->count; ++i) {
                        for (int j = 0; j < right->array->count; ++j) {
                                struct array *pair = value_array_new();
                                NOGC(pair);
                                value_array_push(pair, left->array->items[i]);
                                value_array_push(pair, right->array->items[j]);
                                value_array_push(a.array, ARRAY(pair));
                                OKGC(pair);
                        }
                }
                gc_pop();
                gc_pop();
                gc_pop();
                return a;
        default:
        Fail:
                vm_panic("* applied to operands of invalid type");
        }
}

struct value
binary_operator_division(struct value const *left, struct value const *right)
{
        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(left->class, "/");
                if (f == NULL)
                        goto Fail;
                return vm_eval_function(f, left, right, NULL);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real / right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer / right->real);

        if (left->type != right->type)
                vm_panic("the operands to / must have the same type");

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer / right->integer);
        case VALUE_REAL:    return REAL(left->real / right->real);
        default:
        Fail:
                vm_panic("/ applied to operands of invalid type");
        }
}

struct value
binary_operator_subtraction(struct value const *left, struct value const *right)
{
        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(left->class, "-");
                if (f == NULL)
                        goto Fail;
                return vm_eval_function(f, left, right, NULL);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real - right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer - right->real);

        if (left->type != right->type)
                vm_panic("the operands to - must have the same type");

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer - right->integer);
        case VALUE_REAL:    return REAL(left->real - right->real);
        case VALUE_DICT:
                gc_push((struct value *)left);
                gc_push((struct value *)right);
                struct value v = dict_clone((struct value *)left, 0, NULL);
                gc_push(&v);
                vm_push((struct value  *)right);
                dict_subtract(&v, 1, NULL);
                vm_pop();
                gc_pop();
                gc_pop();
                gc_pop();
                return v;
        default:
        Fail:
                vm_panic("- applied to operands of invalid type");
        }

}

struct value
binary_operator_remainder(struct value const *left, struct value const *right)
{
        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(left->class, "%");
                if (f == NULL)
                        goto Fail;
                return vm_eval_function(f, left, right, NULL);
        }

        struct value L = *left;
        struct value R = *right;

        if (L.type == VALUE_REAL)
                L = INTEGER(L.real);

        if (R.type == VALUE_REAL)
                R = INTEGER(R.real);

        if (L.type != R.type)
                vm_panic("the operands to %% must have the same type");

        switch (L.type) {
        case VALUE_INTEGER:
                if (R.integer == 0)
                        vm_panic("attempt to use % with a modulus of 0");
                return INTEGER(L.integer % R.integer);
        default:
        Fail:
                vm_panic("the operands to %% must be integers");
        }

}

struct value
binary_operator_equality(struct value const *left, struct value const *right)
{

        return BOOLEAN(value_test_equality(left, right));
}

struct value
binary_operator_non_equality(struct value const *left, struct value const *right)
{

        return BOOLEAN(!value_test_equality(left, right));
}

struct value
binary_operator_less_than(struct value const *left, struct value const *right)
{

        if (left->type != right->type)
                vm_panic("< applied to operands of different types");

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer < right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real < right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) < 0);
        default:            vm_panic("< applied to operands of invlalid type");
        }
}

struct value
binary_operator_greater_than(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("> applied to operands of different types");
        }

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer > right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real > right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) > 0);
        default:            vm_panic("> applied to operands of invalid type");
        }
}

struct value
binary_operator_less_than_or_equal(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("<= applied to operands of different types");
        }

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer <= right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real <= right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) <= 0);
        default:            vm_panic("<= applied to operands of invalid type");
        }
}

struct value
binary_operator_greater_than_or_equal(struct value const *left, struct value const *right)
{
        if (left->type != right->type) {
                vm_panic(">= applied to operands of different types");
        }

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer >= right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real >= right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) >= 0);
        default:            vm_panic(">= applied to operands of invalid type");
        }
}

struct value
unary_operator_not(struct value const *operand)
{
        return BOOLEAN(!value_truthy(operand));
}

struct value
unary_operator_negate(struct value const *operand)
{
        if (operand->type == VALUE_INTEGER) {
                return INTEGER(-operand->integer);
        } else if (operand->type == VALUE_REAL) {
                return REAL(-operand->real);
        } else {
                vm_panic("the operand to unary - must be numeric");
        }
}
