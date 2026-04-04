#include <ffi.h>
#include <stdatomic.h>

#include "gc.h"
#include "ty.h"
#include "polyfill_dlfcn.h"
#include "value.h"
#include "alloc.h"
#include "dict.h"
#include "xd.h"
#include "vm.h"
#include "cffi.h"
#include "class.h"

inline static double
float_from(Value const *v)
{
        return (v->type == VALUE_INTEGER) ? v->z : v->real;
}

inline static imax
int_from(Value const *v)
{
        return (v->type == VALUE_INTEGER) ? v->z
             : (v->type == VALUE_PTR)     ? (iptr)v->ptr
             : v->real;
}

inline static void *
ptr_from(Ty *ty, Value const *v)
{
        Value *f;

        switch (v->type) {
        case VALUE_PTR:
                return v->ptr;

        case VALUE_INTEGER:
                return (void *)v->z;

        case VALUE_STRING:
                return (void *)ss(*v);

        case VALUE_NIL:
                return NULL;

        case VALUE_BLOB:
                return (void *)v->blob->items;

        case VALUE_FOREIGN_FUNCTION:
                return (void *)v->ff;

        case VALUE_OBJECT:
                f = class_lookup_method_i(ty, v->class, NAMES.ptr);
                if (f != NULL) {
                        return vm_call_method(ty, v, f, 0).ptr;
                }
                // fallthrough
        }

        zP("FFI: attempt to use non-addressable value as pointer: %s", VSC(v));
}

static void
xstore(Ty *ty, ffi_type *t, void *p, Value const *v)
{
        switch (t->type) {
        case FFI_TYPE_INT:
                *(_Atomic int *)p = int_from(v);
                break;

        case FFI_TYPE_UINT8:
                *(_Atomic u8 *)p = int_from(v);
                break;

        case FFI_TYPE_UINT16:
                *(_Atomic u16 *)p = int_from(v);
                break;

        case FFI_TYPE_UINT32:
                *(_Atomic u32 *)p = int_from(v);
                break;

        case FFI_TYPE_UINT64:
                *(_Atomic u64 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT8:
                *(_Atomic i8 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT16:
                *(_Atomic i16 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT32:
                *(_Atomic i32 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT64:
                *(_Atomic i64 *)p = int_from(v);
                break;

        case FFI_TYPE_POINTER:
                *(void * _Atomic *)p = ptr_from(ty, v);
                break;

        default:
                zP("attempt to store unsupported atomic type: %d", t->type);
        }
}

static void
store(Ty *ty, ffi_type *t, void *p, Value const *v)
{
        usize offsets[64];
        Value *f;

        switch (t->type) {
        case FFI_TYPE_INT:
                *(int *)p = int_from(v);
                break;

        case FFI_TYPE_UINT8:
                *(u8 *)p = int_from(v);
                break;

        case FFI_TYPE_UINT16:
                *(u16 *)p = int_from(v);
                break;

        case FFI_TYPE_UINT32:
                *(u32 *)p = int_from(v);
                break;

        case FFI_TYPE_UINT64:
                *(u64 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT8:
                *(i8 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT16:
                *(i16 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT32:
                *(i32 *)p = int_from(v);
                break;

        case FFI_TYPE_SINT64:
                *(i64 *)p = int_from(v);
                break;

        case FFI_TYPE_FLOAT:
                *(float *)p = float_from(v);
                break;

        case FFI_TYPE_DOUBLE:
                *(double *)p = float_from(v);
                break;

        case FFI_TYPE_POINTER:
                *(void **)p = ptr_from(ty, v);
                break;

        case FFI_TYPE_STRUCT:
                switch (v->type) {
                case VALUE_TUPLE:
                        ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, offsets);
                        for (int i = 0; i < v->count; ++i) {
                                store(ty, t->elements[i], (char *)p + offsets[i], &v->items[i]);
                        }
                        break;

                case VALUE_PTR:
                        memcpy(p, v->ptr, t->size);
                        break;

                case VALUE_OBJECT:
                        f = class_lookup_method_i(ty, v->class, NAMES.ptr);
                        if (f != NULL) {
                                memcpy(p, vm_call_method(ty, v, f, 0).ptr, t->size);
                        } else {
                                zP("attempt to dereference null-pointer: %s.__ptr__()", VSC(v));
                        }
                        break;
                }
                break;
        }
}

static Value
xload(Ty *ty, ffi_type *t, void const *p)
{
        void * _Atomic const *vp;

        switch (t->type) {
        case FFI_TYPE_INT:    return INTEGER(*(int _Atomic const *)p);
        case FFI_TYPE_SINT8:  return INTEGER(*(i8  _Atomic const *)p);
        case FFI_TYPE_SINT16: return INTEGER(*(i16 _Atomic const *)p);
        case FFI_TYPE_SINT32: return INTEGER(*(i32 _Atomic const *)p);
        case FFI_TYPE_SINT64: return INTEGER(*(i64 _Atomic const *)p);
        case FFI_TYPE_UINT8:  return INTEGER(*(u8  _Atomic const *)p);
        case FFI_TYPE_UINT16: return INTEGER(*(u16 _Atomic const *)p);
        case FFI_TYPE_UINT32: return INTEGER(*(u32 _Atomic const *)p);
        case FFI_TYPE_UINT64: return INTEGER(*(u64 _Atomic const *)p);

        case FFI_TYPE_POINTER:
                vp = p;
                return (*vp == NULL) ? NIL : PTR(*vp);
        }

        return NIL;
}

static Value
load(Ty *ty, ffi_type *t, void const *p)
{
        void * const *vp;
        Value v;
        int n;

        usize offsets[128];

        switch (t->type) {
        case FFI_TYPE_INT:    return INTEGER(*(int const *)p);
        case FFI_TYPE_SINT8:  return INTEGER(*(i8  const *)p);
        case FFI_TYPE_SINT16: return INTEGER(*(i16 const *)p);
        case FFI_TYPE_SINT32: return INTEGER(*(i32 const *)p);
        case FFI_TYPE_SINT64: return INTEGER(*(i64 const *)p);
        case FFI_TYPE_UINT8:  return INTEGER(*(u8  const *)p);
        case FFI_TYPE_UINT16: return INTEGER(*(u16 const *)p);
        case FFI_TYPE_UINT32: return INTEGER(*(u32 const *)p);
        case FFI_TYPE_UINT64: return INTEGER(*(u64 const *)p);

        case FFI_TYPE_POINTER:
                vp = p;
                return (*vp == NULL) ? NIL : PTR(*vp);

        case FFI_TYPE_FLOAT:  return REAL(*(float const *)p);
        case FFI_TYPE_DOUBLE: return REAL(*(double const *)p);

        case FFI_TYPE_STRUCT:
                for (n = 0; t->elements[n] != NULL; ++n) {
                        ;
                }

                v = vT(n);
                gP(&v);

                ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, offsets);

                for (int i = 0; i < (n & 0x7F); ++i) {
                        v.items[i] = load(ty, t->elements[i], (char *)p + offsets[i]);
                }

                gX();

                return v;
        }

        return NIL;
}

static void
closure_func(ffi_cif *cif, void *ret, void **args, void *data)
{
        static int depth = 0;

        Ty *ty = GetMyTy();

        Value *ctx = data;
        Value *f = &ctx->items[0];

        depth += 1;

        bool need_unlock = MaybeTakeLock(ty);

        for (int i = 0; i < cif->nargs; ++i) {
                Value arg = load(ty, cif->arg_types[i], args[i]);
                vmP(&arg);
        }

        Value val;

        if (TY_IS(FOREIGN)) {
                if (TY_CATCH_ERROR()) {
                        char *trace = FormatTrace(ty, NULL, NULL);
                        Value error = TY_CATCH();
                        fprintf(
                                stderr,
                                "%sERROR:%s uncaught exception in FFI callback "
                                "on foreign thread:\n%s\n%s",
                                TERM(91;1),
                                TERM(0),
                                VSC(&error),
                                trace
                        );
                        val = error;
                } else {
                        val = vmC(f, cif->nargs);
                        TY_CATCH_END();
                }
        } else {
                val = vmC(f, cif->nargs);
        }

        switch (cif->rtype->type) {
        case FFI_TYPE_VOID:
                break;

        case FFI_TYPE_INT:
        case FFI_TYPE_SINT8:
        case FFI_TYPE_SINT16:
        case FFI_TYPE_SINT32:
                store(ty, &ffi_type_sint64, ret, &val);
                break;

        case FFI_TYPE_UINT8:
        case FFI_TYPE_UINT16:
        case FFI_TYPE_UINT32:
                store(ty, &ffi_type_uint64, ret, &val);
                break;

        default:
                store(ty, cif->rtype, ret, &val);
        }

        depth -= 1;

        if (need_unlock) {
                UnlockTy();
        }
}

Value
cffi_cif(Ty *ty, int argc, Value *kwargs)
{
        ffi_type *rt;
        vec(ffi_type *) ats = {0};

        if (argc == 0) {
                rt = &ffi_type_void;
        } else if (ARG(0).type == VALUE_PTR) {
                rt = ARG(0).ptr;
        } else {
Bad:
                xvF(ats);
                zP("invalid type passed to ffi.cif()");
        }

        for (int i = 1; i < argc; ++i) {
                if (ARG(i).type != VALUE_PTR) {
                        goto Bad;
                }
                xvP(ats, ARG(i).ptr);
        }

        ffi_cif *cif = mA(sizeof *cif);

        Value *nFixed = NAMED("nFixed");

        if (nFixed != NULL && nFixed->type != VALUE_NIL) {
                if (nFixed->type != VALUE_INTEGER) {
                        xvF(ats);
                        mF(cif);
                        zP("ffi.cif(): expected nFixed to be an integer but got: %s", VSC(nFixed));
                }
                if (ffi_prep_cif_var(cif, FFI_DEFAULT_ABI, nFixed->z, max(0, argc - 1), rt, ats.items) != FFI_OK) {
                        xvF(ats);
                        mF(cif);
                        return NIL;
                }
        } else if (ffi_prep_cif(cif, FFI_DEFAULT_ABI, max(0, argc - 1), rt, vv(ats)) != FFI_OK) {
                xvF(ats);
                mF(cif);
                return NIL;
        }

        return PTR(cif);
}

Value
cffi_addr(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.addr()", 1);
        void *v = PTR_ARG(0);
        void **p = mA(sizeof *p);
        *p = v;
        return PTR(p);
}

Value
cffi_free(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.free()", 1);
        Value object = ARG(0);
        void *addr = ptr_from(ty, &object);
        free(addr);
        return NIL;
}

Value
cffi_alloc(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.alloc()", 1);
        void *p = malloc(max(0, INT_ARG(0)));
        return (p == NULL) ? NIL : PTR(p);
}

Value
cffi_realloc(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.realloc()", 2);

        Value _ptr = ARG(0);
        usize size = INT_ARG(1);

        void *ptr = ptr_from(ty, &_ptr);
        void *new = realloc(ptr, size);

        return (new == NULL) ? NIL : PTR(new);
}

Value
cffi_size(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("ffi.size() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("the argument to ffi.size() must be a pointer");
        }

        return INTEGER(((ffi_type *)ARG(0).ptr)->size);
}

Value
cffi_auto(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.auto()", 1, 2);

        Value ptr = ARGx(0, VALUE_PTR);
        Value *dtor = mAo(sizeof (Value [2]), GC_FFI_AUTO);

        if (argc == 1) {
                dtor[0] = PTR(free);
        } else {
                dtor[0] = ARG(1);
        }

        dtor[1] = PTR(ptr.ptr);

        return TGCPTR(ptr.ptr, ptr.extra, dtor);
}

Value
cffi_new(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.new()", 1, 2, 3);

        ffi_type *t = PTR_ARG(0);
        isize count = (argc > 1) ? INT_ARG(1) : 1;
        void *init  = (argc > 2) ? ptr_from(ty, &ARG(2)) : NULL;

        if (count < 0) {
                bP("negative count: %zd", count);
        }

        if (count == 0) {
                return TPTR(t, NULL);
        }

        unsigned align = max(t->alignment, sizeof (void *));
        usize total = max(t->size * count, sizeof (void *));
        total += (total % align);

#ifdef _WIN32
        Value p = TPTR(t, _aligned_malloc(total, align));
#else
        Value p = TPTR(t, aligned_alloc(align, total));
#endif

        if (p.ptr == NULL) {
                return NIL;
        }

        if (init == NULL) {
                memset(p.ptr, 0, total);
        } else {
                memcpy(p.ptr, init, count * t->size);
        }

        return p;
}

Value
cffi_box(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.box()", 1, 2);

        ffi_type *t = PTR_ARG(0);

        unsigned align = max(t->alignment, sizeof (void *));
        unsigned size = max(t->size, sizeof (void *));
        size += (size % align);

#ifdef _WIN32
        Value p = TPTR(t, _aligned_malloc(size, align));
#else
        Value p = TPTR(t, aligned_alloc(align, size));
#endif

        if (p.ptr == NULL) {
                return NIL;
        }

        if (argc == 2) {
                Value v = ARG(1);
                store(ty, t, p.ptr, &v);
        } else {
                memset(p.ptr, 0, t->size);
        }

        return p;
}

Value
cffi_new_auto(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.new-auto()", 1, 2, 3);

        ffi_type *t = PTR_ARG(0);
        usize count = (argc >= 2) ? INT_ARG(1) : 1;
        void *init  = (argc >= 3) ? ptr_from(ty, &ARG(2)) : NULL;

        void *mem;
        if (init == NULL) {
                mem = mAo0(count * t->size, GC_ANY);
        } else {
                mem = mAo(count * t->size, GC_ANY);
                memcpy(mem, init, count * t->size);
        }

        return TGCPTR(mem, t, mem);
}

Value
cffi_box_auto(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.box-auto()", 1, 2);

        ffi_type *t = PTR_ARG(0);
        Value init  = (argc == 2) ? ARG(1) : ZERO;

        void *mem;
        if (IsZero(init)) {
                mem = mAo0(t->size, GC_ANY);
        } else {
                mem = mAo(t->size, GC_ANY);
                NOGC(mem);
                store(ty, t, mem, &init);
                OKGC(mem);
        }

        return TGCPTR(mem, t, mem);
}

Value
cffi_pmember(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 3) {
                zP("ffi.pmember(): expected 3 arguments but got %d", argc);
        }

        Value t = ARG(0);
        if (t.type != VALUE_PTR) {
                zP("the first argument to ffi.member() must be a pointer");
        }

        ffi_type *type = t.ptr;

        int n = 0;
        while (type->elements[n] != NULL) {
                n += 1;
        }

        unsigned char *p;
        switch (ARG(1).type) {
        case VALUE_PTR:
                p = ARG(1).ptr;
                break;

        case VALUE_BLOB:
                p = ARG(1).blob->items;
                break;

        default:
                zP("ffi.pmember(): invalid second argument: %s", VSC(&ARG(1)));
        }

        Value i = ARG(2);
        if (
                (i.type != VALUE_INTEGER)
             || (i.z < 0)
             || (i.z >= n)
        ) {
                zP("invalid third argument to ffi.pmember(): %s", VSC(&i));
        }

        usize offsets[64];
        ffi_get_struct_offsets(FFI_DEFAULT_ABI, type, offsets);

        return PTR(p + offsets[i.z]);
}

Value
cffi_member(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 3 && argc != 4) {
                zP("ffi.member() expects 3 or 4 arguments but got %d", argc);
        }

        Value t = ARG(0);
        if (t.type != VALUE_PTR) {
                zP("the first argument to ffi.member() must be a pointer");
        }

        ffi_type *type = t.ptr;

        int n = 0;
        while (type->elements[n] != NULL) {
                n += 1;
        }

        unsigned char *p;
        switch (ARG(1).type) {
        case VALUE_PTR:
                p = ARG(1).ptr;
                break;

        case VALUE_BLOB:
                p = ARG(1).blob->items;
                break;

        default:
                zP("ffi.member(): invalid second argument: %s", VSC(&ARG(1)));
        }

        Value i = ARG(2);
        if (
                (i.type != VALUE_INTEGER)
             || (i.z < 0)
             || (i.z >= n)
        ) {
                zP("invalid third argument to ffi.member(): %s", VSC(&i));
        }

        usize offsets[64];
        ffi_get_struct_offsets(FFI_DEFAULT_ABI, type, offsets);

        if (argc == 3) {
                return load(ty, type->elements[i.z], p + offsets[i.z]);
        } else {
                Value val = ARG(3);
                store(ty, type->elements[i.z], p + offsets[i.z], &val);
                return val;
        }
}

Value
cffi_fields(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.fields()", 1);

        usize *offsets;
        ffi_type *type = PTR_ARG(0);

        if (type->type != FFI_TYPE_STRUCT) {
                return NIL;
        }

        usize count = 0;

        while (type->elements[count] != NULL) {
                count += 1;
        }

        Array *fields = vA();

        SCRATCH_SAVE();
        offsets = smA(count * sizeof (usize));
        ffi_get_struct_offsets(FFI_DEFAULT_ABI, type, offsets);
        GC_STOP();
        for (usize i = 0; i < count; ++i) {
                uvP(*fields, PAIR(
                        INTEGER(offsets[i]),
                        PTR(type->elements[i])
                ));
        }
        GC_RESUME();
        SCRATCH_RESTORE();

        return ARRAY(fields);
}

Value
cffi_load(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.load()", 1, 2, 3);

        if (argc == 3) {
                return cffi_load_n(ty, argc, kwargs);
        }

        Value arg0 = ARGx(0, VALUE_PTR);

        if (argc == 1) {
                ffi_type *t = (arg0.extra == NULL)
                            ? &ffi_type_uint8
                            : arg0.extra;
                return load(ty, t, arg0.ptr);
        }

        Value addr = ARG(1);

        return load(ty, arg0.ptr, ptr_from(ty, &addr));
}

Value
cffi_load_atomic(Ty *ty, int argc, Value *kwargs)
{
        ffi_type *t;

        switch (argc) {
        case 1:
                t = (ARG(0).extra == NULL)
                  ? &ffi_type_uint8
                  : ARG(0).extra;
                return xload(ty, t, ARG(0).ptr);

        case 2:
                return xload(ty, ARG(0).ptr, ARG(1).ptr);

        default:
                zP("atomic.load(): expected 1 or 2 arguments but got %d", argc);
        }
}

Value
cffi_load_n(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.load()", 3);

        ffi_type *t = PTR_ARG(0);
        char *p = PTR_ARG(1);
        usize n = INT_ARG(2);

        Array *a = vA();
        Value result = ARRAY(a);

        gP(&result);
        for (int i = 0; i < n; ++i) {
            uvP(*a, load(ty, t, p + (i * t->size)));
        }
        gX();

        return result;
}

Value
cffi_store(Ty *ty, int argc, Value *kwargs)
{
        Value vType;
        Value vPtr;
        Value vVal;

        switch (argc) {
        case 3:
                vType = ARG(0);
                vPtr = ARG(1);
                vVal = ARG(2);
                break;

        case 2:
                vType = NONE;
                vPtr = ARG(0);
                vVal = ARG(1);
                break;

        default:
                zP("ffi.store(): expected 2 or 3 arguments but got %d", argc);
        }

        if (vPtr.type != VALUE_PTR) {
                zP("ffi.store(): expected pointer but got: %s", VSC(&vPtr));
        }

        if (vType.type == VALUE_NONE) {
                vType = PTR(
                        (vPtr.extra == NULL)
                      ? &ffi_type_uint8
                      : (ffi_type *)vPtr.extra
                );
        } else if (vType.type != VALUE_PTR) {
                zP("ffi.store(): expected pointer but got: %s", VSC(&vType));
        }

        store(ty, vType.ptr, vPtr.ptr, &vVal);

        return load(ty, vType.ptr, vPtr.ptr);
}

Value
cffi_store_atomic(Ty *ty, int argc, Value *kwargs)
{
        Value vType;
        Value vPtr;
        Value vVal;

        switch (argc) {
        case 3:
                vType = ARG(0);
                vPtr = ARG(1);
                vVal = ARG(2);
                break;

        case 2:
                vType = NONE;
                vPtr = ARG(0);
                vVal = ARG(1);
                break;

        default:
                zP("atomic.store(): expected 2 or 3 arguments but got %d", argc);
        }

        if (vPtr.type != VALUE_PTR) {
                zP("atomic.store(): expected pointer but got: %s", VSC(&vPtr));
        }

        if (vType.type == VALUE_NONE) {
                vType = PTR(
                        (vPtr.extra == NULL)
                      ? &ffi_type_uint8
                      : (ffi_type *)vPtr.extra
                );
        } else if (vType.type != VALUE_PTR) {
                zP("atomic.store(): expected pointer but got: %s", VSC(&vType));
        }

        xstore(ty, vType.ptr, vPtr.ptr, &vVal);

        return NIL;
}

Value
cffi_call(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("ffi.call()", 2, INT_MAX);

        ffi_cif *cif = PTR_ARG(0);
        void (*func)(void) = (void (*)(void))PTR_ARG(1);

        if (UNLIKELY(cif->nargs != argc - 2)) {
                bP("bad FFI call: %u arguments expected but got %d", cif->nargs, argc - 2);
        }

        vec(void *) args = {0};

        SCRATCH_SAVE();

        svR(args, cif->nargs);

        for (int i = 2; i < argc; ++i) {
                ffi_type *c_type = cif->arg_types[i - 2];
                void *mem = smA(c_type->size);
                store(ty, c_type, mem, &ARG(i));
                vPx(args, mem);
        }

        Value *out = NAMED("out");
        void  *buf = (out == NULL) ? smA(cif->rtype->size) : ptr_from(ty, out);

        UnlockTy();
        ffi_call(cif, func, buf, vv(args));
        LockTy();

        Value ret = (out == NULL) ? load(ty, cif->rtype, buf) : PTR(buf);

        SCRATCH_RESTORE();

        return ret;
}

Value
cffi_fun(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.fun()", 2, 3);

        void (*ff)(void) = (void (*)(void))PTR_ARG(0);
        ffi_cif *cif = PTR_ARG(1);
        FunUserInfo *xinfo = NULL;

        if (ARG_T(2) == VALUE_STRING) {
                xinfo = mAo0(sizeof (FunUserInfo), GC_ANY);
                xinfo->name = TY_C_STR(ARG(2));
        }

        return FOREIGN_FUN(ff, cif, xinfo);
}

Value
cffi_fast_call(Ty *ty, Value const *fun, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("ffi.call()", 0, INT_MAX);

        ffi_cif *cif = fun->ffi;
        void (*func)(void) = (void (*)(void))fun->ff;

        if (UNLIKELY(cif->nargs != argc)) {
                bP("bad FFI call: %u arguments expected but got %d", cif->nargs, argc);
        }

        vec(void *) args = {0};

        SCRATCH_SAVE();

        svR(args, cif->nargs);

        for (int i = 0; i < argc; ++i) {
                ffi_type *c_type = cif->arg_types[i];
                void *mem = smA(c_type->size);
                store(ty, c_type, mem, &ARG(i));
                vPx(args, mem);
        }

        Value *out = NAMED("out");
        void  *buf = (out == NULL) ? smA(cif->rtype->size) : ptr_from(ty, out);

        UnlockTy();
        ffi_call(cif, func, buf, vv(args));
        LockTy();

        Value ret = (out == NULL) ? load(ty, cif->rtype, buf) : PTR(buf);

        SCRATCH_RESTORE();

        return ret;
}

Value
cffi_dlopen(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.dlopen()", 1, 2);

        Value lib = ARGx(0, VALUE_STRING);
#ifdef _WIN32
        void *p = LoadLibraryA(b);
#else
        void *p = dlopen(TY_TMP_C_STR(lib), RTLD_NOW);
#endif
        return (p == NULL) ? NIL : PTR(p);
}

Value
cffi_blob(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.blob()", 2);

        void *mem = ARGx(0, VALUE_PTR).ptr;
        usize n = INT_ARG(1);

        // TODO: should be a 'frozen' blob or something
        // cant realloc() this pointer and don't know
        // how long it's valid -- risky
        Blob *b = mA(sizeof *b);
        b->items = mem;
        b->count = n;
        b->capacity = n;

        return BLOB(b);
}

Value
cffi_clone(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.clone()", 2);

        void *p;
        store(ty, &ffi_type_pointer, &p, &ARG(0));

        usize n = INT_ARG(1);
        void *clone = mAo(n, GC_ANY);

        memcpy(clone, p, n);

        return PTR(clone);
}

Value
cffi_c_str(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.c_str()", 1);
        Value str = ARGx(0, VALUE_STRING, VALUE_BLOB);
        return PTR(TY_C_STR(str));
}

Value
cffi_str(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.str()", 1, 2);

        Value arg = ARG(0);
        void *str = ptr_from(ty, &arg);

        usize n;
        if (argc == 2) {
                n = INT_ARG(1);
        } else {
                n = strlen(str);
        }

        return vSs(str, n);
}

Value
cffi_as_str(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.as_str()", 1, 2);

        Value arg = ARG(0);
        void *str = ptr_from(ty, &arg);

        usize n;
        if (argc == 2) {
                n = INT_ARG(1);
        } else {
                n = strlen(str);
        }

        return xSs(str, n);
}

Value
cffi_dlerror(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("ffi.dlerror(): expected 0 arguments but got %d", argc);
        }

#ifdef _WIN32
        return NIL;
#else
        char *error = dlerror();

        if (error == NULL)
                return NIL;

        return vSsz(error);
#endif
}

Value
cffi_dlsym(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.dlsym()", 1, 2);

        Value symbol = ARGx(0, VALUE_STRING);

        void *handle;
        if (argc == 2 && ARG(1).type != VALUE_NIL) {
                handle = PTR_ARG(1);
        } else {
#ifdef _WIN32
                handle = GetModuleHandleA("ucrtbase.dll");
#else
                handle = RTLD_DEFAULT;
#endif
        }

#ifdef _WIN32
        void *p = GetProcAddress(handle, b);
#else
        void *p = dlsym(handle, TY_TMP_C_STR(symbol));
#endif

        return (p == NULL) ? NIL : PTR(p);
}

Value
cffi_struct(Ty *ty, int argc, Value *kwargs)
{
        if (argc == 0) {
                zP("ffi.struct() expects at least 1 argument");
        }

        ffi_type *t = mA(sizeof *t);

        t->type = FFI_TYPE_STRUCT;
        t->size = 0;
        t->alignment = 0;
        t->elements = mA((argc + 1) * sizeof (ffi_type *));

        for (int i = 0; i < argc; ++i) {
                Value member = ARG(i);

                if (member.type != VALUE_PTR) {
                        zP("non-pointer passed to ffi.struct(): %s", VSC(&member));
                }

                t->elements[i] = member.ptr;
        }

        t->elements[argc] = NULL;

        ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, NULL);

        return PTR(t);
}

Value
cffi_closure(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("ffi.closure()", 1, INT_MAX);

        Value f = ARG(argc - 1);
        vmX();

        if (!CALLABLE(f)) {
                bP("argument is not callable: %s", VSC(&f));
        }

        Value cif = cffi_cif(ty, argc - 1, NULL);
        if (cif.type == VALUE_NIL) {
                bP("failed to construct ffi_cif");
        }

        void *code;
        ffi_closure *closure = ffi_closure_alloc(sizeof *closure, &code);
        if (closure == NULL) {
                bP("ffi_closure_alloc() failed");
        }

        GC_STOP();

        Value *data = mAo(sizeof *data, GC_VALUE);
        *data = vT(2);
        data->items[0] = f;
        data->items[1] = PTR(ty);

        void **pointers = mA(sizeof (void *[2]));
        pointers[0] = closure;
        pointers[1] = cif.ptr;

        GC_RESUME();

        if (ffi_prep_closure_loc(closure, cif.ptr, closure_func, data, code) == FFI_OK) {
                return EPTR(code, data, pointers);
        } else {
                mF(data);
                ffi_closure_free(closure);
                return NIL;
        }
}

Value
cffi_closure_free(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.freeClosure()", 1);

        Value p = ARGx(0, VALUE_PTR);
        void **pointers = p.extra;

        ffi_closure_free(pointers[0]);

        ffi_cif *cif = pointers[1];
        ty_free(cif->arg_types);
        mF(cif);

        mF(pointers);

        return NIL;
}

inline static int
struct_field_size(int c)
{
        switch (c) {
        case 'b': case 'B': case '?': case 'x': return  1;
        case 'h': case 'H':                     return  2;
        case 'i': case 'I': case 'f':           return  4;
        case 'q': case 'Q': case 'd':           return  8;
        default:                                return -1;
        }
}

Value
cffi_calcsize(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.calcsize()", 1);

        Value vFmt = ARGx(0, VALUE_STRING);
        u8 const *fmt = ss(vFmt);
        isize n = sN(vFmt);

        int i = 0;
        int size = 0;

        if (i < n && contains("><!=@", fmt[i])) {
                i += 1;
        }

        for (int count = 0; i < n; count = 0) {
                while (i < n && fmt[i] >= '0' && fmt[i] <= '9') {
                        count = count * 10 + (fmt[i++] - '0');
                }

                if (count == 0) {
                        count = 1;
                }

                if (i >= n) {
                        break;
                }

                int ch = fmt[i++];

                if (ch == 's') {
                        size += count;
                } else {
                        int fs = struct_field_size(ch);
                        if (fs < 0) {
                                bP("bad format char '%c'", ch);
                        }
                        size += fs * count;
                }
        }

        return INTEGER(size);
}

inline static int
parsefmt(u8 const *fmt, int n, int *start, bool *big)
{
        int i = 0;

        *big = false;

        if (i < n) switch (fmt[i]) {
        case '>':
        case '!':
                *big = true;
        case '<':
        case '=':
        case '@':
                i += 1;
                break;
        }

        *start = i;

        int total = 0;

        for (int count = 0; i < n; count = 0) {
                while (i < n && fmt[i] >= '0' && fmt[i] <= '9') {
                        count = count * 10 + (fmt[i++] - '0');
                }

                if (count == 0) {
                        count = 1;
                }

                if (i >= n) {
                        break;
                }

                int ch = fmt[i++];

                if (ch == 's') {
                        total += count;
                } else {
                        int fs = struct_field_size(ch);
                        if (fs < 0) {
                                return -1;
                        }
                        total += fs * count;
                }
        }

        return total;
}

inline static int
countfields(u8 const *fmt, int n, int start)
{
        int nf = 0;
        int i  = start;

        for (int count = 0; i < n; count = 0) {
                while (i < n && fmt[i] >= '0' && fmt[i] <= '9') {
                        count = count * 10 + (fmt[i++] - '0');
                }

                if (count == 0) {
                        count = 1;
                }

                if (i >= n) {
                        break;
                }

                int ch = fmt[i++];

                if (ch == 'x') {
                        continue;
                }

                nf += (ch == 's') ? 1 : count;
        }

        return nf;
}

Value
cffi_pack(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("ffi.pack()", 1, 64);

        Blob *b;
        u8 *buf;
        u8 const *fmt;
        usize nfmt;

        Value arg0 = ARG(0);
        Value arg1;

        int ai;

        switch (arg0.type) {
        case VALUE_STRING:
                fmt  = ss(arg0);
                nfmt = sN(arg0);
                b    = NULL;
                buf  = NULL;
                ai   = 1;
                break;

        case VALUE_PTR:
                arg1 = ARGx(1, VALUE_STRING);
                fmt  = ss(arg1);
                nfmt = sN(arg1);
                b    = NULL;
                buf  = arg0.ptr;
                ai   = 2;
                break;

        case VALUE_BLOB:
                arg1 = ARGx(1, VALUE_STRING);
                fmt  = ss(arg1);
                nfmt = sN(arg1);
                b    = arg0.blob;
                buf  = NULL;
                ai   = 2;
                break;

        default:
                ARGx(0, VALUE_STRING, VALUE_PTR, VALUE_BLOB);
                UNREACHABLE();
        }

        int i;
        bool big;
        int total = parsefmt(fmt, nfmt, &i, &big);

        if (total < 0) {
                bP("bad format");
        }

        GC_STOP();

        if (buf == NULL) {
                if (b != NULL) {
                        usize old = vN(*b);
                        usize new = old + total;
                        uvR(*b, new);
                        vN(*b) = new;
                        buf = vv(*b) + old;
                } else {
                        buf = malloc(total);
                        if (UNLIKELY(buf == NULL)) {
                                GC_RESUME();
                                bP("malloc() fail");
                        }
                }
        }

        memset(buf, 0, total);

        isize off = 0;

        while (i < nfmt) {
                int count = 0;
                while (i < nfmt && fmt[i] >= '0' && fmt[i] <= '9') {
                        count = count * 10 + (fmt[i++] - '0');
                }

                if (count == 0) {
                        count = 1;
                }

                if (i >= nfmt) {
                        break;
                }

                int ch = fmt[i++];

                if (ch == 'x') {
                        off += count;
                        continue;
                }

                if (ch == 's') {
                        if (ai >= argc) {
                                goto NotEnoughArgs;
                        }
                        Value v = ARGx(ai++, VALUE_STRING, VALUE_BLOB);
                        u8 const *src;
                        isize srclen;
                        if (v.type == VALUE_STRING) {
                                src = ss(v);
                                srclen = sN(v);
                        } else {
                                src = vv(*v.blob);
                                srclen = vN(*v.blob);
                        }
                        memcpy(buf + off, src, min(srclen, count));
                        off += count;
                        continue;
                }

                isize size = struct_field_size(ch);

                for (int r = 0; r < count; ++r) {
                        if (ai >= argc) {
                                goto NotEnoughArgs;
                        }

                        Value v = ARG(ai++);

                        float  _f;
                        double _d;
                        u64    _z;

                        switch (ch) {
                        case '?':
                                buf[off] = value_truthy(ty, &v) ? 1 : 0;
                                break;

                        case 'f':
                                _f = float_from(&v);
                                memcpy(buf + off, &_f, 4);
                                if (big) {
                                        SWAP(u8, buf[off+0], buf[off+3]);
                                        SWAP(u8, buf[off+1], buf[off+2]);
                                }
                                break;

                        case 'd':
                                _d = float_from(&v);
                                memcpy(buf + off, &_d, 8);
                                if (big) {
                                        for (int k = 0; k < 4; ++k) {
                                                SWAP(u8, buf[off + k], buf[off + 7 - k]);
                                        }
                                }
                                break;

                        default:
                                _z = (u64)int_from(&v);
                                if (big) {
                                        for (int k = size - 1; k >= 0; --k) {
                                                buf[off + k] = _z & 0xff;
                                                _z >>= 8;
                                        }
                                } else {
                                        for (int k = 0; k < size; ++k) {
                                                buf[off + k] = _z & 0xff;
                                                _z >>= 8;
                                        }
                                }
                                break;
                        }
                        off += size;
                }
        }

        GC_RESUME();

        return (b != NULL) ? BLOB(b) : PTR(buf);

NotEnoughArgs:
        GC_RESUME();
        zP("ffi.pack(): not enough arguments");
}

Value
cffi_unpack(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.unpack()", 2, 3);

        Value vFmt = ARGx(0, VALUE_STRING);
        u8 const *fmt = ss(vFmt);
        int fmtlen = sN(vFmt);

        Value vBuf = ARGx(1, VALUE_BLOB, VALUE_PTR);

        unsigned char const *buf = (vBuf.type == VALUE_BLOB)
                                 ? vv(*vBuf.blob)
                                 : vBuf.ptr;

        isize offset = (argc == 3) ? INT_ARG(2) : 0;

        int fi;
        bool big;

        parsefmt(fmt, fmtlen, &fi, &big);

        int nfields = countfields(fmt, fmtlen, fi);

        GC_STOP();

        Value t = (nfields > 1) ? vT(nfields) : NIL;
        int ti = 0;
        int off = offset;

        for (int count = 0; fi < fmtlen; count = 0) {
                while (fi < fmtlen && fmt[fi] >= '0' && fmt[fi] <= '9') {
                        count = count * 10 + (fmt[fi++] - '0');
                }

                if (count == 0) {
                        count = 1;
                }

                if (fi >= fmtlen) {
                        break;
                }

                int ch = fmt[fi++];

                if (ch == 'x') {
                        off += count;
                        continue;
                }

                if (ch == 's') {
                        Blob *sb = value_blob_new(ty);
                        uvR(*sb, count);
                        vN(*sb) = count;
                        memcpy(vv(*sb), buf + off, count);
                        t.items[ti++] = BLOB(sb);
                        off += count;
                        continue;
                }

                isize size = struct_field_size(ch);

                for (int r = 0; r < count; ++r) {
                        Value v;

                        float  _f;
                        double _d;
                        u64    _z;

                        switch (ch) {
                        case '?':
                                v = BOOLEAN(buf[off] != 0);
                                break;

                        case 'f':
                                if (big) {
                                        u8 tmp[4] = { buf[off+3], buf[off+2], buf[off+1], buf[off] };
                                        memcpy(&_f, tmp, 4);
                                } else {
                                        memcpy(&_f, buf + off, 4);
                                }
                                v = REAL(_f);
                                break;

                        case 'd':
                                if (big) {
                                        u8 tmp[8];
                                        for (int k = 0; k < 8; ++k)
                                                tmp[k] = buf[off + 7 - k];
                                        memcpy(&_d, tmp, 8);
                                } else {
                                        memcpy(&_d, buf + off, 8);
                                }
                                v = REAL(_d);
                                break;

                        default:
                                _z = 0;
                                if (big) {
                                        for (int k = 0; k < size; ++k)
                                                _z = (_z << 8) | buf[off + k];
                                } else {
                                        for (int k = size - 1; k >= 0; --k)
                                                _z = (_z << 8) | buf[off + k];
                                }

                                imax ival;
                                switch (ch) {
                                case 'b': ival = (i8)(u8)_z;   break;
                                case 'h': ival = (i16)(u16)_z; break;
                                case 'i': ival = (i32)(u32)_z; break;
                                case 'q': ival = (i64)_z;      break;
                                default:  ival = (imax)_z;     break;
                                }

                                v = INTEGER(ival);
                                break;
                        }

                        if (nfields == 1) {
                                GC_RESUME();
                                return v;
                        }

                        t.items[ti++] = v;
                        off += size;
                }
        }

        GC_RESUME();

        return t;
}

/* vim: set sts=8 sw=8 expandtab: */
