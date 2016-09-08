#include <string.h>

#include "alloc.h"
#include "value.h"
#include "operators.h"
#include "object.h"
#include "vm.h"

static struct value
str_concat(struct value const *s1, struct value const *s2)
{
        size_t n = s1->bytes + s2->bytes;
        struct string *s = value_string_alloc(n);

        memcpy(s->data, s1->string, s1->bytes);
        memcpy(s->data + s1->bytes, s2->string, s2->bytes);

        return STRING(s->data, n, s);
}

struct value
binary_operator_addition(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("the operands to + must have the same type");
        }

        struct value v;

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer + right->integer);
        case VALUE_REAL:    return REAL(left->real + right->real);
        case VALUE_STRING:  return str_concat(left, right);
        case VALUE_ARRAY:
                v = ARRAY(value_array_clone(left->array));
                value_array_extend(v.array, right->array);
                return v;
        default:
                vm_panic("+ applied to operands of invalid type");
                break;
        }
}

struct value
binary_operator_multiplication(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("the operands to * must have the same type");
        }

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer * right->integer);
        case VALUE_REAL:    return REAL(left->real * right->real);
        default:            vm_panic("* applied to operands of invalid type");
        }
}

struct value
binary_operator_division(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("the operands to / must have the same type");
        }

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer / right->integer);
        case VALUE_REAL:    return REAL(left->real / right->real);
        default:            vm_panic("/ applied to operands of invalid type");
        }
}

struct value
binary_operator_subtraction(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("the operands to - must have the same type");
        }

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer - right->integer);
        case VALUE_REAL:    return REAL(left->real - right->real);
        default:            vm_panic("- applied to operands of invalid type");
        }

}

struct value
binary_operator_remainder(struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                vm_panic("the operands to - must have the same type");
        }

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer % right->integer);
        default:            vm_panic("the operands to - must be integers");
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

        if (left->type != right->type) {
                vm_panic("< applied to operands of different types");
        }

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

struct value
unary_operator_keys(struct value const *operand)
{
        if (operand->type != VALUE_OBJECT) {
                vm_panic("the operand to @ must be an object");
        }

        return object_keys_array(operand->object);
}
