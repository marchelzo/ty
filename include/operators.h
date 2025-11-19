#ifndef OPERATORS_H_INCLUDED
#define OPERATORS_H_INCLUDED

#include <math.h>

#include <ffi.h>

#include "ty.h"
#include "dict.h"
#include "str.h"
#include "value.h"
#include "util.h"
#include "vm.h"

#define     look(i) (&ty->stack.items[ty->stack.count - 1] + i)
#define COMPLETE(x) do { Value x__ = x; ty->stack.items[--ty->stack.count - 1] = x__; return true; } while (0)

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
                COMPLETE(INTEGER(left->z + right->z));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real + right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real + right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->z + right->real));

        case PAIR_OF(VALUE_STRING):
        {
                if  (sN(*left) == 0) COMPLETE(*right);
                if (sN(*right) == 0) COMPLETE(*left);

                n = sN(*left) + sN(*right);
                v = STRING(value_string_alloc(ty, n), n);

                memcpy(
                        (void *)ss(v),
                        ss(*left),
                        sN(*left)
                );

                memcpy(
                        (void *)(ss(v) + sN(*left)),
                        ss(*right),
                        sN(*right)
                );

                COMPLETE(v);
        }

        case PACK_TYPES(VALUE_STRING, VALUE_INTEGER):
                COMPLETE(OffsetString(left, right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_PTR):
                SWAP(Value const *, left, right);
        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, (char *)left->ptr + right->z * t->size));

        case PAIR_OF(VALUE_ARRAY):
        {
                if  (left->array->count == 0) COMPLETE(ARRAY(ArrayClone(ty, right->array)));
                if (right->array->count == 0) COMPLETE(ARRAY(ArrayClone(ty, left->array)));

                n = left->array->count + right->array->count;

                v = ARRAY(vAn(n));
                v.array->count = n;

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
        {
                Dict *new = DictClone(ty, left->dict);
                NOGC(new);

                DictUpdate(ty, new, right->dict);

                OKGC(new);

                COMPLETE(DICT(new));
        }
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
                COMPLETE(INTEGER(left->z * right->z));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real * right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real * right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->z * right->real));

        case PAIR_OF(VALUE_ARRAY):
                v = ARRAY(vAn(left->array->count * right->array->count));

                gP(&v);

                for (int i = 0; i < left->array->count; ++i) {
                        for (int j = 0; j < right->array->count; ++j) {
                                vPx(
                                        *v.array,
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
                if (right->z == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(INTEGER(left->z / right->z));

        case PAIR_OF(VALUE_REAL):
                if (right->real == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(left->real / right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                if (right->z == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(left->real / right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                if (right->real == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(left->z / right->real));
        }

        return false;
}

inline static bool
op_builtin_sub(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        Value v;
        ffi_type *t;

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z - right->z));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real - right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real - right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->z - right->real));

        case PACK_TYPES(VALUE_STRING, VALUE_INTEGER):
                COMPLETE(OffsetString(left, -right->z));

        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, ((char *)left->ptr) - right->z * t->size));

        case PACK_TYPES(VALUE_PTR, VALUE_PTR):
                if (left->extra != right->extra) {
                        zP("attempt to subtract pointers of different types");
                }
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(INTEGER(((char *)left->ptr - (char *)right->ptr) / t->size));

        case PAIR_OF(VALUE_DICT):
        {
                Value new = DICT(DictClone(ty, left->dict));
                NOGC(new.dict);

                vm_push(ty, right);
                dict_subtract(ty, &new, 1, NULL);
                vm_pop(ty);

                OKGC(new.dict);

                COMPLETE(new);
        }
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
                if (right->z == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(INTEGER(left->z % right->z));
        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                if (right->z == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(fmod(left->real, right->z)));
        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                if (right->real == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(fmod(left->z, right->real)));
        case PACK_TYPES(VALUE_REAL, VALUE_REAL):
                if (right->real == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(fmod(left->real, right->real)));
        }

        return false;
}

inline static bool
op_builtin_and(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z & right->z));
        }

        return false;
}

inline static bool
op_builtin_or(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z | right->z));
        }

        return false;
}

inline static bool
op_builtin_xor(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z ^ right->z));
        }

        return false;
}

inline static bool
op_builtin_shl(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z << right->z));
        }

        return false;
}

inline static bool
op_builtin_shr(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z >> right->z));
        }

        return false;
}

void
op_add(int op, int t1, int t2, int ref, Expr *fun);

int
op_dispatch(Ty *ty, int op, int t1, int t2);

Expr *
op_fun_info(int op, int t1, int t2);

void
op_dump(int op);

Type *
op_type(int op);

int
op_defs_for(int op, int c, bool left, expression_vector *defs);

int
op_defs_for_l(int op, int c, expression_vector *defs);

int
op_defs_for_r(int op, int c, expression_vector *defs);

#endif
