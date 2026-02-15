#ifndef OPERATORS_H_INCLUDED
#define OPERATORS_H_INCLUDED

#include <math.h>

#include <ffi.h>

#include "ty.h"
#include "dict.h"
#include "str.h"
#include "value.h"
#include "xd.h"
#include "vm.h"

#define     look(i) (&ty->stack.items[ty->stack.count - 1] + i)
#define COMPLETE(x) do { Value x__ = x; ty->stack.items[--ty->stack.count - 1] = x__; return true; } while (0)

inline static bool
op_builtin_add(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        usize n;
        ffi_type *t;

        Value v;

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(left->z + right->z));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(left->real + right->real));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->boolean + right->boolean));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real + right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->z + right->real));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z + right->boolean));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(left->boolean + right->z));

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

        case PACK_TYPES(VALUE_STRING, VALUE_BOOLEAN):
                COMPLETE(OffsetString(left, right->boolean));

        case PACK_TYPES(VALUE_INTEGER, VALUE_PTR):
                SWAP(Value const *, left, right);
        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, (char *)left->ptr + right->z * t->size));

        case PAIR_OF(VALUE_ARRAY):
        {
                if  (vN(*left->array) == 0) COMPLETE(ARRAY(ArrayClone(ty, right->array)));
                if (vN(*right->array) == 0) COMPLETE(ARRAY(ArrayClone(ty, left->array)));

                n = vN(*left->array) + vN(*right->array);

                v = ARRAY(vAn(n));
                v.array->count = n;

                memcpy(
                        vv(*v.array),
                        vv(*left->array),
                        vN(*left->array) * sizeof (Value)
                );

                memcpy(
                        vv(*v.array) + vN(*left->array),
                        vv(*right->array),
                        vN(*right->array) * sizeof (Value)
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

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->boolean * right->boolean));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real * right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->z * right->real));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(left->boolean * right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z * right->boolean));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_REAL):
                COMPLETE(REAL(left->boolean * right->real));

        case PACK_TYPES(VALUE_REAL, VALUE_BOOLEAN):
                COMPLETE(REAL(left->real * right->boolean));

        case PACK_TYPES(VALUE_STRING, VALUE_INTEGER):
        {
                if (right->z <= 0) {
                        COMPLETE(STRING_EMPTY);
                }

                usize n = sN(*left) * right->z;

                v = STRING(value_string_alloc(ty, n), n);

                for (imax i = 0; i < right->z; ++i) {
                        memcpy(
                                (void *)(ss(v) + i * sN(*left)),
                                ss(*left),
                                sN(*left)
                        );
                }

                COMPLETE(v);
        }

        case PACK_TYPES(VALUE_STRING, VALUE_BOOLEAN):
                COMPLETE(right->boolean ? *left : STRING_EMPTY);


        case PAIR_OF(VALUE_ARRAY):
                v = ARRAY(vAn(vN(*left->array) * vN(*right->array)));
                gP(&v);
                for (int i = 0; i < vN(*left->array); ++i) {
                        for (int j = 0; j < vN(*right->array); ++j) {
                                vPx(
                                        *v.array,
                                        PAIR(
                                                v__(*left->array, i),
                                                v__(*right->array, j)
                                        )
                                );
                        }
                }
                gX();
                COMPLETE(v);

        case PACK_TYPES(VALUE_ARRAY, VALUE_INTEGER):
        {
                if (right->z <= 0) {
                        COMPLETE(ARRAY(ArrayClone(ty, NULL)));
                }
                v = ARRAY(vAn(vN(*left->array) * right->z));
                vN(*v.array) = vN(*left->array) * right->z;
                for (int i = 0; i < right->z; ++i) {
                        memcpy(
                                v.array->items + i * left->array->count,
                                left->array->items,
                                left->array->count * sizeof (Value)
                        );
                }

                COMPLETE(v);
        }

        case PACK_TYPES(VALUE_ARRAY, VALUE_BOOLEAN):
                if (right->boolean) {
                        COMPLETE(ARRAY(ArrayClone(ty, left->array)));
                } else {
                        COMPLETE(ARRAY(vAn(0)));
                }
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

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_REAL):
                if (right->real == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(left->boolean / right->real));
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

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->boolean - (int)right->boolean));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(left->real - right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(left->z - right->real));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(left->boolean - right->z));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z - right->boolean));

        case PACK_TYPES(VALUE_STRING, VALUE_INTEGER):
                COMPLETE(OffsetString(left, -right->z));

        case PACK_TYPES(VALUE_STRING, VALUE_BOOLEAN):
                COMPLETE(OffsetString(left, -(int)right->boolean));

        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, ((char *)left->ptr) - right->z * t->size));

        case PACK_TYPES(VALUE_PTR, VALUE_BOOLEAN):
                t = (left->extra == NULL) ? &ffi_type_uint8 : left->extra;
                COMPLETE(TPTR(left->extra, ((char *)left->ptr) - right->boolean * t->size));

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
op_builtin_divmod(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        imaxdiv_t div;

        switch (PACK_TYPES(left->type, right->type)) {
        case PAIR_OF(VALUE_INTEGER):
                if (right->z == 0) {
                        ZeroDividePanic(ty);
                }
                div = imaxdiv(left->z, right->z);
                COMPLETE(PAIR(INTEGER(div.quot), INTEGER(div.rem)));
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

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->boolean & right->boolean));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z & right->boolean));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(left->boolean & right->z));
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

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->boolean | right->boolean));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z | right->boolean));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(left->boolean | right->z));
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

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->boolean ^ right->boolean));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z ^ right->boolean));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(left->boolean ^ right->z));
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

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z << right->boolean));
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

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(left->z >> right->boolean));
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
op_type(Ty *ty, int op);

int
op_defs_for(int op, int c, bool left, ExprVec *defs);

int
op_defs_for_l(int op, int c, ExprVec *defs);

int
op_defs_for_r(int op, int c, ExprVec *defs);

#endif
