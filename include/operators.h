#ifndef OPERATORS_H_INCLUDED
#define OPERATORS_H_INCLUDED

#include "value.h"

struct value
binary_operator_addition(struct value const *left, struct value const *right);

struct value
binary_operator_multiplication(struct value const *left, struct value const *right);

struct value
binary_operator_division(struct value const *left, struct value const *right);

struct value
binary_operator_subtraction(struct value const *left, struct value const *right);

struct value
binary_operator_remainder(struct value const *left, struct value const *right);

struct value
binary_operator_and(struct value const *left, struct value const *right);

struct value
binary_operator_or(struct value const *left, struct value const *right);

struct value
binary_operator_equality(struct value const *left, struct value const *right);

struct value
binary_operator_non_equality(struct value const *left, struct value const *right);

struct value
binary_operator_less_than(struct value const *left, struct value const *right);

struct value
binary_operator_greater_than(struct value const *left, struct value const *right);

struct value
binary_operator_less_than_or_equal(struct value const *left, struct value const *right);

struct value
binary_operator_greater_than_or_equal(struct value const *left, struct value const *right);

struct value
unary_operator_negate(struct value const *operand);

struct value
unary_operator_not(struct value const *operand);

struct value
unary_operator_keys(struct value const *operand);

#endif
