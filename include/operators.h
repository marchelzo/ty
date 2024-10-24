#ifndef OPERATORS_H_INCLUDED
#define OPERATORS_H_INCLUDED

#include <math.h>

#include <ffi.h>

#include "ty.h"
#include "dict.h"
#include "value.h"
#include "util.h"
#include "vm.h"

#define     look(i) (&ty->stack.items[ty->stack.count - 1] + i)
#define COMPLETE(x) do { ty->stack.items[--ty->stack.count - 1] = x; return true; } while (0)

inline static bool
op_builtin_add(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        size_t n;
        ffi_type *t;

        Value v;

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->integer + right->integer));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real + right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real + right->integer));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->integer + right->real));

        case PAIR_OF(VALUE_STRING):
        {
                if  (left->bytes == 0) COMPLETE(*right);
                if (right->bytes == 0) COMPLETE(*left);

                n = left->bytes + right->bytes;
                v = STRING(value_string_alloc(ty, n), n);

                memcpy(
                        (void *)v.string,
                        left->string,
                        left->bytes
                );

                memcpy(
                        (void *)(v.string + left->bytes),
                        right->string,
                        right->bytes
                );

                COMPLETE(v);
        }


        case PACK_TYPES(VALUE_INTEGER, VALUE_PTR):
                SWAP(Value const *, left, right);
        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, (char *)left->ptr + right->integer * t->size));

        case PAIR_OF(VALUE_ARRAY):
        {
                if  (left->array->count == 0) COMPLETE(ARRAY(ArrayClone(ty, right->array)));
                if (right->array->count == 0) COMPLETE(ARRAY(ArrayClone(ty, left->array)));

                n = left->array->count + right->array->count;

                v = ARRAY(vAn(n));

                memcpy(
                        v.array->items,
                        left->array->items,
                        left->array->count * sizeof (Value)
                );

                memcpy(
                        v.array->items + left->array->count,
                        right->array->items,
                        right->array->count * sizeof (Value)
                );

                COMPLETE(v);
        }

        case PAIR_OF(VALUE_DICT):
                COMPLETE(
                        DICT(
                                DictUpdate(
                                        ty,
                                        DictClone(ty, left->dict),
                                        right->dict
                                )
                        )
                );
        }

        return false;
}

inline static bool
op_builtin_mul(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        Value v;

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->integer * right->integer));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real * right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real * right->integer));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->integer * right->real));

        case PAIR_OF(VALUE_ARRAY):
                v = ARRAY(vAn(left->array->count * right->array->count));
                v.array->count = 0;

                gP(&v);

                for (int i = 0; i < left->array->count; ++i) {
                        for (int j = 0; j < right->array->count; ++j) {
                                vAp(
                                        v.array,
                                        PAIR(
                                                left->array->items[i],
                                                right->array->items[j]
                                        )
                                );
                        }
                }

                gX();

                COMPLETE(v);
        }

        return false;
}

inline static bool
op_builtin_div(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->integer / right->integer));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real / right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real / right->integer));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->integer / right->real));
        }

        return false;
}

inline static bool
op_builtin_sub(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        ffi_type *t;

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->integer - right->integer));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real - right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real - right->integer));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->integer - right->real));

        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, ((char *)left->ptr) - right->integer * t->size));

        case PACK_TYPES(VALUE_PTR, VALUE_PTR):
                if (left->extra != right->extra) {
                        zP("attempt to subtract pointers of different types");
                }
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(INTEGER(((char *)left->ptr - (char *)right->ptr) / t->size));
        }

        return false;
}

inline static bool
op_builtin_mod(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PACK_TYPES(VALUE_INTEGER, VALUE_INTEGER):
                COMPLETE(INTEGER(left->integer % right->integer));
        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(fmod(left->real, right->integer)));
        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(fmod(left->integer, right->real)));
        case PACK_TYPES(VALUE_REAL, VALUE_REAL):
                COMPLETE(REAL(fmod(left->real, right->real)));
        }

        return false;
}


struct value
binary_operator_multiplication(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_division(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_subtraction(Ty *ty, struct value const *left, struct value const *right);

struct value
binary_operator_remainder(Ty *ty, struct value const *left, struct value const *right);

struct value
_operator_equality(Ty *ty, struct value const *left, struct value const *right);

struct value
unary_operator_negate(Ty *ty, struct value const *operand);

struct value
unary_operator_not(Ty *ty, struct value const *operand);

void
op_add(int op, int t1, int t2, int ref);

int
op_dispatch(int op, int t1, int t2);

void
op_dump(int op);

#endif
