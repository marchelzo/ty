#include <string.h>
#include <ffi.h>

#include "alloc.h"
#include "value.h"
#include "operators.h"
#include "class.h"
#include "dict.h"
#include "vm.h"
#include "gc.h"

static struct value
str_concat(Ty *ty, struct value const *s1, struct value const *s2)
{
        size_t n = s1->bytes + s2->bytes;
        char *s = value_string_alloc(ty, n);

        memcpy(s, s1->string, s1->bytes);
        memcpy(s + s1->bytes, s2->string, s2->bytes);

        return STRING(s, n);
}

struct value
binary_operator_addition(Ty *ty, struct value const *left, struct value const *right)
{

        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(ty, left->class, "+");
                if (f == NULL)
                        goto Fail;
                struct value method = METHOD("+", f, left);
                return vm_eval_function(ty, &method, right, NULL);
        }

        if (left->type == VALUE_PTR) {
                if (right->type != VALUE_INTEGER) {
                        zP("attempt to add non-integer to pointer: %s", value_show_color(ty, right));
                }

                ffi_type *t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;

                return TPTR(left->extra, (char *)left->ptr + right->integer * t->size);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real + right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer + right->real);

        if (left->type != right->type)
                zP("incompatible operands to +: %s and %s", value_show_color(ty, left), value_show_color(ty, right));

        struct value v;

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer + right->integer);
        case VALUE_REAL:    return REAL(left->real + right->real);
        case VALUE_STRING:  return str_concat(ty, left, right);
        case VALUE_ARRAY:
                gP((struct value *)left);
                gP((struct value *)right);
                v = ARRAY(value_array_clone(ty, left->array));
                NOGC(v.array);
                value_array_extend(ty, v.array, right->array);
                OKGC(v.array);
                gX();
                gX();
                return v;
        case VALUE_DICT:
                gP((struct value *)left);
                gP((struct value *)right);
                struct value v = dict_clone(ty, (struct value *)left, 0, NULL);
                gP(&v);
                vmP((struct value  *)right);
                dict_update(ty, &v, 1, NULL);
                vmX();
                gX();
                gX();
                gX();
                return v;
        default:
        Fail:
                zP("+ applied to operands of invalid type");
                break;
        }
}

struct value
binary_operator_multiplication(Ty *ty, struct value const *left, struct value const *right)
{

        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(ty, left->class, "*");
                if (f == NULL)
                        goto Fail;
                struct value method = METHOD("*", f, left);
                return vm_eval_function(ty, &method, right, NULL);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real * right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer * right->real);

        if (left->type != right->type)
                zP("the operands to * must have the same type");

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer * right->integer);
        case VALUE_REAL:    return REAL(left->real * right->real);
        case VALUE_ARRAY:;
                struct value a = ARRAY(vA());
                gP(&a);
                gP(left);
                gP(right);
                for (int i = 0; i < left->array->count; ++i) {
                        for (int j = 0; j < right->array->count; ++j) {
                                struct array *pair = vA();
                                NOGC(pair);
                                vAp(pair, left->array->items[i]);
                                vAp(pair, right->array->items[j]);
                                vAp(a.array, ARRAY(pair));
                                OKGC(pair);
                        }
                }
                gX();
                gX();
                gX();
                return a;
        default:
        Fail:
                zP("* applied to operands of invalid type");
        }
}

struct value
binary_operator_division(Ty *ty, struct value const *left, struct value const *right)
{
        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(ty, left->class, "/");
                if (f == NULL)
                        goto Fail;
                struct value method = METHOD("/", f, left);
                return vm_eval_function(ty, &method, right, NULL);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real / right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer / right->real);

        if (left->type != right->type)
                zP("the operands to / must have the same type");

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer / right->integer);
        case VALUE_REAL:    return REAL(left->real / right->real);
        default:
        Fail:
                zP("/ applied to operands of invalid type");
        }
}

struct value
binary_operator_subtraction(Ty *ty, struct value const *left, struct value const *right)
{
        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(ty, left->class, "-");
                if (f == NULL)
                        goto Fail;
                struct value method = METHOD("-", f, left);
                return vm_eval_function(ty, &method, right, NULL);
        }

        if (left->type == VALUE_STRING) {
                struct value const *f = class_method(ty, CLASS_STRING, "-");
                if (f == NULL)
                        goto Fail;
                struct value method = METHOD("-", f, left);
                return vm_eval_function(ty, &method, right, NULL);
        }

        if (left->type == VALUE_REAL && right->type == VALUE_INTEGER)
                return REAL(left->real - right->integer);

        if (left->type == VALUE_INTEGER && right->type == VALUE_REAL)
                return REAL(left->integer - right->real);

        if (left->type == VALUE_PTR && right->type == VALUE_INTEGER) {
                ffi_type *t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                return TPTR(left->extra, ((char *)left->ptr) - right->integer * t->size);
        }

        if (left->type != right->type)
                zP("the operands to - must have the same type");

        switch (left->type) {
        case VALUE_INTEGER: return INTEGER(left->integer - right->integer);
        case VALUE_REAL:    return REAL(left->real - right->real);
        case VALUE_PTR:     return INTEGER((char *)left->ptr - (char *)right->ptr);
        case VALUE_DICT:
                gP((struct value *)left);
                gP((struct value *)right);
                struct value v = dict_clone(ty, (struct value *)left, 0, NULL);
                gP(&v);
                vmP((struct value  *)right);
                dict_subtract(ty, &v, 1, NULL);
                vmX();
                gX();
                gX();
                gX();
                return v;
        default:
        Fail:
                zP("- applied to operands of invalid type");
        }

}

struct value
binary_operator_remainder(Ty *ty, struct value const *left, struct value const *right)
{
        if (left->type == VALUE_OBJECT) {
                struct value const *f = class_method(ty, left->class, "%");
                if (f == NULL)
                        goto Fail;
                struct value method = METHOD("%", f, left);
                return vm_eval_function(ty, &method, right, NULL);
        }

        struct value L = *left;
        struct value R = *right;

        if (L.type == VALUE_REAL)
                L = INTEGER(L.real);

        if (R.type == VALUE_REAL)
                R = INTEGER(R.real);

        if (L.type != R.type)
                zP("the operands to %% must have the same type");

        switch (L.type) {
        case VALUE_INTEGER:
                if (R.integer == 0)
                        zP("attempt to use % with a modulus of 0");
                return INTEGER(L.integer % R.integer);
        case VALUE_TUPLE:
                return vm_eval_function(ty, class_method(ty, CLASS_TUPLE, "%"), right, left, NULL);
        default:
        Fail:
                zP("the operands to %% must be integers");
        }

}

struct value
binary_operator_equality(Ty *ty, struct value const *left, struct value const *right)
{

        return BOOLEAN(value_test_equality(ty, left, right));
}

struct value
binary_operator_non_equality(Ty *ty, struct value const *left, struct value const *right)
{

        return BOOLEAN(!value_test_equality(ty, left, right));
}

struct value
binary_operator_less_than(Ty *ty, struct value const *left, struct value const *right)
{

        if (left->type != right->type)
                zP("< applied to operands of different types");

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer < right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real < right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) < 0);
        default:            zP("< applied to operands of invlalid type");
        }
}

struct value
binary_operator_greater_than(Ty *ty, struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                zP("> applied to operands of different types");
        }

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer > right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real > right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) > 0);
        default:            zP("> applied to operands of invalid type");
        }
}

struct value
binary_operator_less_than_or_equal(Ty *ty, struct value const *left, struct value const *right)
{

        if (left->type != right->type) {
                zP("<= applied to operands of different types");
        }

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer <= right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real <= right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) <= 0);
        default:            zP("<= applied to operands of invalid type");
        }
}

struct value
binary_operator_greater_than_or_equal(Ty *ty, struct value const *left, struct value const *right)
{
        if (left->type != right->type) {
                zP(">= applied to operands of different types");
        }

        switch (left->type) {
        case VALUE_INTEGER: return BOOLEAN(left->integer >= right->integer);
        case VALUE_REAL:    return BOOLEAN(left->real >= right->real);
        case VALUE_STRING:  return BOOLEAN(strcmp(left->string, right->string) >= 0);
        default:            zP(">= applied to operands of invalid type");
        }
}

struct value
unary_operator_not(Ty *ty, struct value const *operand)
{
        return BOOLEAN(!value_truthy(ty, operand));
}

struct value
unary_operator_negate(Ty *ty, struct value const *operand)
{
        if (operand->type == VALUE_INTEGER) {
                return INTEGER(-operand->integer);
        } else if (operand->type == VALUE_REAL) {
                return REAL(-operand->real);
        } else {
                zP("the operand to unary - must be numeric");
        }
}
