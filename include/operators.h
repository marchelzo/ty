#ifndef OPERATORS_H_INCLUDED
#define OPERATORS_H_INCLUDED

#include "value.h"

struct value
binary_operator_addition(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_multiplication(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_division(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_subtraction(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_remainder(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_and(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_or(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_equality(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_non_equality(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_less_than(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_greater_than(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_less_than_or_equal(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_greater_than_or_equal(Ty *ty, struct value const *left, struct value const *right);

struct value
unary_operator_negate(Ty *ty, struct value const *operand);

struct value
unary_operator_not(Ty *ty, struct value const *operand);

#endif
