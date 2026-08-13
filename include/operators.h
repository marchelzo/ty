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

#define     look(i) (&STACK.items[STACK.count - 1] + i)
#define COMPLETE(x) do { Value x__ = x; STACK.items[--STACK.count - 1] = x__; return true; } while (0)

inline static bool
op_builtin_add(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        usize n;
        ffi_type *t;

        Value v;

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) + V_Z(*right)));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(V_REAL(*left) + V_REAL(*right)));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_BOOL(*left) + V_BOOL(*right)));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(V_REAL(*left) + V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(V_Z(*left) + V_REAL(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) + V_BOOL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(V_BOOL(*left) + V_Z(*right)));

        case PAIR_OF(VALUE_STRING):
        {
                if  (sN(*left) == 0) COMPLETE(*right);
                if (sN(*right) == 0) COMPLETE(*left);

                n = sN(*left) + sN(*right);
                v = STRING(ty, value_string_alloc(ty, n), n);

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
                COMPLETE(OffsetString(left, V_Z(*right)));

        case PACK_TYPES(VALUE_STRING, VALUE_BOOLEAN):
                COMPLETE(OffsetString(left, V_BOOL(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_PTR):
                SWAP(Value const *, left, right);
        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (V_EXTRA(*(left)) == NULL) ? &ffi_type_uint8 : V_EXTRA(*(left));
                COMPLETE(TPTR(V_EXTRA(*left), (char *)V_PTR(*left) + V_Z(*right) * t->size));

        case PAIR_OF(VALUE_ARRAY):
        {
                if  (vN(*V_ARRAY(*left)) == 0) COMPLETE(ARRAY(ArrayClone(ty, V_ARRAY(*right))));
                if (vN(*V_ARRAY(*right)) == 0) COMPLETE(ARRAY(ArrayClone(ty, V_ARRAY(*left))));

                n = vN(*V_ARRAY(*left)) + vN(*V_ARRAY(*right));

                v = ARRAY(vAn(n));
                V_ARRAY(v)->count = n;

                memcpy(
                        vv(*V_ARRAY(v)),
                        vv(*V_ARRAY(*left)),
                        vN(*V_ARRAY(*left)) * sizeof (Value)
                );

                memcpy(
                        vv(*V_ARRAY(v)) + vN(*V_ARRAY(*left)),
                        vv(*V_ARRAY(*right)),
                        vN(*V_ARRAY(*right)) * sizeof (Value)
                );

                COMPLETE(v);
        }

        case PAIR_OF(VALUE_DICT):
        {
                Dict *new = DictClone(ty, V_DICT(*(left)));
                NOGC(new);

                DictUpdate(ty, new, V_DICT(*(right)));

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

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) * V_Z(*right)));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(V_REAL(*left) * V_REAL(*right)));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_BOOL(*left) * V_BOOL(*right)));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(V_REAL(*left) * V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(V_Z(*left) * V_REAL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(V_BOOL(*left) * V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) * V_BOOL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_REAL):
                COMPLETE(REAL(V_BOOL(*left) * V_REAL(*right)));

        case PACK_TYPES(VALUE_REAL, VALUE_BOOLEAN):
                COMPLETE(REAL(V_REAL(*left) * V_BOOL(*right)));

        case PACK_TYPES(VALUE_STRING, VALUE_INTEGER):
        {
                if (V_Z(*(right)) <= 0) {
                        COMPLETE(STRING_EMPTY);
                }

                usize n = sN(*left) * V_Z(*(right));

                v = STRING(ty, value_string_alloc(ty, n), n);

                for (imax i = 0; i < V_Z(*(right)); ++i) {
                        memcpy(
                                (void *)(ss(v) + i * sN(*left)),
                                ss(*left),
                                sN(*left)
                        );
                }

                COMPLETE(v);
        }

        case PACK_TYPES(VALUE_STRING, VALUE_BOOLEAN):
                COMPLETE(V_BOOL(*right) ? *left : STRING_EMPTY);


        case PAIR_OF(VALUE_ARRAY):
                v = ARRAY(vAn(vN(*V_ARRAY(*left)) * vN(*V_ARRAY(*right))));
                gP(&v);
                for (int i = 0; i < vN(*V_ARRAY(*left)); ++i) {
                        for (int j = 0; j < vN(*V_ARRAY(*right)); ++j) {
                                vPx(
                                        *V_ARRAY(v),
                                        PAIR(
                                                v__(*V_ARRAY(*left), i),
                                                v__(*V_ARRAY(*right), j)
                                        )
                                );
                        }
                }
                gX();
                COMPLETE(v);

        case PACK_TYPES(VALUE_ARRAY, VALUE_INTEGER):
        {
                if (V_Z(*(right)) <= 0) {
                        COMPLETE(ARRAY(ArrayClone(ty, NULL)));
                }
                v = ARRAY(vAn(vN(*V_ARRAY(*left)) * V_Z(*right)));
                vN(*V_ARRAY(v)) = vN(*V_ARRAY(*left)) * V_Z(*(right));
                for (int i = 0; i < V_Z(*(right)); ++i) {
                        memcpy(
                                V_ARRAY(v)->items + i * V_ARRAY(*left)->count,
                                V_ARRAY(*left)->items,
                                V_ARRAY(*left)->count * sizeof (Value)
                        );
                }

                COMPLETE(v);
        }

        case PACK_TYPES(VALUE_ARRAY, VALUE_BOOLEAN):
                if (V_BOOL(*(right))) {
                        COMPLETE(ARRAY(ArrayClone(ty, V_ARRAY(*left))));
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

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                if (V_Z(*(right)) == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(INTEGER(V_Z(*left) / V_Z(*right)));

        case PAIR_OF(VALUE_REAL):
                if (V_REAL(*(right)) == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(V_REAL(*left) / V_REAL(*right)));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                if (V_Z(*(right)) == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(V_REAL(*left) / V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                if (V_REAL(*(right)) == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(V_Z(*left) / V_REAL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_REAL):
                if (V_REAL(*(right)) == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(V_BOOL(*left) / V_REAL(*right)));
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

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) - V_Z(*right)));

        case PAIR_OF(VALUE_REAL):
                COMPLETE(REAL(V_REAL(*left) - V_REAL(*right)));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_BOOL(*left) - (int)V_BOOL(*right)));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                COMPLETE(REAL(V_REAL(*left) - V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                COMPLETE(REAL(V_Z(*left) - V_REAL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(V_BOOL(*left) - V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) - V_BOOL(*right)));

        case PACK_TYPES(VALUE_STRING, VALUE_INTEGER):
                COMPLETE(OffsetString(left, -V_Z(*right)));

        case PACK_TYPES(VALUE_STRING, VALUE_BOOLEAN):
                COMPLETE(OffsetString(left, -(int)V_BOOL(*right)));

        case PACK_TYPES(VALUE_PTR, VALUE_INTEGER):
                t = (V_EXTRA(*(left)) == NULL) ? &ffi_type_uint8 : V_EXTRA(*(left));
                COMPLETE(TPTR(V_EXTRA(*left), ((char *)V_PTR(*left)) - V_Z(*right) * t->size));

        case PACK_TYPES(VALUE_PTR, VALUE_BOOLEAN):
                t = (V_EXTRA(*(left)) == NULL) ? &ffi_type_uint8 : V_EXTRA(*(left));
                COMPLETE(TPTR(V_EXTRA(*left), ((char *)V_PTR(*left)) - V_BOOL(*right) * t->size));

        case PACK_TYPES(VALUE_PTR, VALUE_PTR):
                if (V_EXTRA(*(left)) != V_EXTRA(*(right))) {
                        zP("attempt to subtract pointers of different types");
                }
                t = (V_EXTRA(*(left)) == NULL) ? &ffi_type_uint8 : V_EXTRA(*(left));
                COMPLETE(INTEGER(((char *)V_PTR(*left) - (char *)V_PTR(*right)) / t->size));

        case PAIR_OF(VALUE_DICT):
        {
                Value new = DICT(DictClone(ty, V_DICT(*left)));
                NOGC(V_DICT(new));

                vm_push(ty, right);
                dict_subtract(ty, &new, 1, NULL);
                vm_pop(ty);

                OKGC(V_DICT(new));

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

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PACK_TYPES(VALUE_INTEGER, VALUE_INTEGER):
                if (V_Z(*(right)) == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(INTEGER(V_Z(*left) % V_Z(*right)));

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                if (V_Z(*(right)) == 0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(fmod(V_REAL(*left), V_Z(*right))));

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                if (V_REAL(*(right)) == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(fmod(V_Z(*left), V_REAL(*right))));

        case PACK_TYPES(VALUE_REAL, VALUE_REAL):
                if (V_REAL(*(right)) == 0.0) {
                        ZeroDividePanic(ty);
                }
                COMPLETE(REAL(fmod(V_REAL(*left), V_REAL(*right))));
        }

        return false;
}

inline static bool
op_builtin_divmod(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        imaxdiv_t div;

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                if (V_Z(*(right)) == 0) {
                        ZeroDividePanic(ty);
                }
                div = imaxdiv(V_Z(*(left)), V_Z(*(right)));
                COMPLETE(PAIR(INTEGER(div.quot), INTEGER(div.rem)));
        }

        return false;
}

inline static bool
op_builtin_and(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) & V_Z(*right)));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_BOOL(*left) & V_BOOL(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) & V_BOOL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(V_BOOL(*left) & V_Z(*right)));
        }

        return false;
}

inline static bool
op_builtin_or(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) | V_Z(*right)));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_BOOL(*left) | V_BOOL(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) | V_BOOL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(V_BOOL(*left) | V_Z(*right)));
        }

        return false;
}

inline static bool
op_builtin_xor(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) ^ V_Z(*right)));

        case PAIR_OF(VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_BOOL(*left) ^ V_BOOL(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) ^ V_BOOL(*right)));

        case PACK_TYPES(VALUE_BOOLEAN, VALUE_INTEGER):
                COMPLETE(INTEGER(V_BOOL(*left) ^ V_Z(*right)));
        }

        return false;
}

inline static bool
op_builtin_shl(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) << V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) << V_BOOL(*right)));
        }

        return false;
}

inline static bool
op_builtin_shr(Ty *ty)
{
        Value const *left = look(-1);
        Value const *right = look(0);

        switch (PACK_TYPES(V_TYPE(*left), V_TYPE(*right))) {
        case PAIR_OF(VALUE_INTEGER):
                COMPLETE(INTEGER(V_Z(*left) >> V_Z(*right)));

        case PACK_TYPES(VALUE_INTEGER, VALUE_BOOLEAN):
                COMPLETE(INTEGER(V_Z(*left) >> V_BOOL(*right)));
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

void
op_reset(U32Vector const *base);

U32Vector
op_baseline(Ty *ty);

Type *
op_type(Ty *ty, int op);

int
op_defs_for(int op, int c, bool left, ExprVec *defs);

int
op_defs_for_l(int op, int c, ExprVec *defs);

int
op_defs_for_r(int op, int c, ExprVec *defs);

#endif
