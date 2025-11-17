#include <ffi.h>
#include <stdatomic.h>

#include "gc.h"
#include "ty.h"
#include "polyfill_dlfcn.h"
#include "value.h"
#include "alloc.h"
#include "dict.h"
#include "util.h"
#include "vm.h"
#include "cffi.h"
#include "class.h"

inline static double
float_from(Value const *v)
{
        return (v->type == VALUE_INTEGER) ? v->integer : v->real;
}

inline static imax
int_from(Value const *v)
{
        return (v->type == VALUE_INTEGER) ? v->integer
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
                return (void *)v->integer;

        case VALUE_STRING:
                return (void *)v->str;

        case VALUE_NIL:
                return NULL;

        case VALUE_BLOB:
                return (void *)v->blob->items;

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
        size_t offsets[64];
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
                        if (f != NULL)
                                memcpy(p, vm_call_method(ty, v, f, 0).ptr, t->size);
                        else
                                zP("attempt to dereference null-pointer: %s.__ptr__()", VSC(v));
                        break;
                }
                break;
        }
}

static Value
xload(Ty *ty, ffi_type *t, void const *p)
{
        void * _Atomic const *vp;
        Value v;
        int n;

        switch (t->type) {
        case FFI_TYPE_INT:    return INTEGER(*(int _Atomic const *)p);
        case FFI_TYPE_SINT8:  return INTEGER(*(i8 _Atomic const *)p);
        case FFI_TYPE_SINT16: return INTEGER(*(i16 _Atomic const *)p);
        case FFI_TYPE_SINT32: return INTEGER(*(i32 _Atomic const *)p);
        case FFI_TYPE_SINT64: return INTEGER(*(i64 _Atomic const *)p);
        case FFI_TYPE_UINT8:  return INTEGER(*(u8 _Atomic const *)p);
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

        switch (t->type) {
        case FFI_TYPE_INT:    return INTEGER(*(int const *)p);
        case FFI_TYPE_SINT8:  return INTEGER(*(i8 const *)p);
        case FFI_TYPE_SINT16: return INTEGER(*(i16 const *)p);
        case FFI_TYPE_SINT32: return INTEGER(*(i32 const *)p);
        case FFI_TYPE_SINT64: return INTEGER(*(i64 const *)p);
        case FFI_TYPE_UINT8:  return INTEGER(*(u8 const *)p);
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

                usize offsets[128];
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
        Value *ctx = data;
        Value *f = &ctx->items[0];
        Ty *ty = ctx->items[1].ptr;

        bool need_unlock = MaybeTakeLock(ty);

        for (int i = 0; i < cif->nargs; ++i) {
                Value arg = load(ty, cif->arg_types[i], args[i]);
                vmP(&arg);
        }

        Value rv = vmC(f, cif->nargs);

        switch (cif->rtype->type) {
        case FFI_TYPE_VOID:
                break;
        case FFI_TYPE_INT:
        case FFI_TYPE_SINT8:
        case FFI_TYPE_SINT16:
        case FFI_TYPE_SINT32:
                store(ty, &ffi_type_sint64, ret, &rv);
                break;
        case FFI_TYPE_UINT8:
        case FFI_TYPE_UINT16:
        case FFI_TYPE_UINT32:
                store(ty, &ffi_type_uint64, ret, &rv);
                break;
        default:
                store(ty, cif->rtype, ret, &rv);
        }

        if (need_unlock) {
                ReleaseLock(ty, true);
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
                vec_empty(ats);
                zP("invalid type passed to ffi.cif()");
        }

        for (int i = 1; i < argc; ++i) {
                if (ARG(i).type != VALUE_PTR) {
                        goto Bad;
                }

                vvP(ats, ARG(i).ptr);
        }

        ffi_cif *cif = mA(sizeof *cif);

        Value *nFixed = NAMED("nFixed");

        if (nFixed != NULL && nFixed->type != VALUE_NIL) {
                if (nFixed->type != VALUE_INTEGER) {
                        zP("ffi.cif(): expected nFixed to be an integer but got: %s", VSC(nFixed));
                }
                if (ffi_prep_cif_var(cif, FFI_DEFAULT_ABI, nFixed->integer, max(0, argc - 1), rt, ats.items) != FFI_OK) {
                        vec_empty(ats);
                        mF(cif);
                        return NIL;
                }
        } else if (ffi_prep_cif(cif, FFI_DEFAULT_ABI, max(0, argc - 1), rt, ats.items) != FFI_OK) {
                vec_empty(ats);
                mF(cif);
                return NIL;
        }

        return PTR(cif);
}

Value
cffi_addr(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("ffi.addr() expects 1 argument but got %d", argc);
        }

        Value v = ARG(0);

        if (v.type != VALUE_PTR) {
                zP("ffi.addr() expects a pointer but got: %s", VSC(&v));
        }

        void **p = mA(sizeof *p);
        *p = v.ptr;

        return PTR(p);
}

Value
cffi_free(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("ffi.free()", 1);
        free(ARGx(0, VALUE_PTR).ptr);
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
        if (argc != 2) {
                zP("ffi.realloc() expects 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
            zP("ffi.realloc(): expected pointer as first argument but got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("ffi.realloc(): expected integer as second argument but got: %s", VSC(&ARG(1)));
        }

        if (ARG(1).integer <= 0)
                return NIL;

        void *p = realloc(ARG(0).ptr, ARG(1).integer);

        return (p == NULL) ? NIL : PTR(p);
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
        if (argc != 1 && argc != 2) {
                zP("ffi.new() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("the argument to ffi.new() must be a pointer");
        }

        ffi_type *t = ARG(0).ptr;

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
             || (i.integer < 0)
             || (i.integer >= n)
        ) {
                zP("invalid third argument to ffi.pmember(): %s", VSC(&i));
        }

        size_t offsets[64];
        ffi_get_struct_offsets(FFI_DEFAULT_ABI, type, offsets);

        return PTR(p + offsets[i.integer]);
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
             || (i.integer < 0)
             || (i.integer >= n)
        ) {
                zP("invalid third argument to ffi.member(): %s", VSC(&i));
        }

        size_t offsets[64];
        ffi_get_struct_offsets(FFI_DEFAULT_ABI, type, offsets);

        if (argc == 3) {
                return load(ty, type->elements[i.integer], p + offsets[i.integer]);
        } else {
                store(ty, type->elements[i.integer], p + offsets[i.integer], &ARG(3));
                return NIL;
        }
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
        ffi_type *t = ARG(0).ptr;
        char *p = ARG(1).ptr;
        size_t n = ARG(2).integer;

        struct array *a = vA();

        NOGC(a);

        for (int i = 0; i < n; ++i) {
            vAp(a, load(ty, t, p + (i * t->size)));
        }

        OKGC(a);

        return ARRAY(a);
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

        return NIL;
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

        lGv(true);
        ffi_call(cif, func, buf, vv(args));
        lTk();

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

        lGv(true);
        ffi_call(cif, func, buf, vv(args));
        lTk();

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
        if (argc != 1 && argc != 2) {
                zP("ffi.str() expects 1 or 2 arguments but got %d", argc);
        }

        void *p;
        store(ty, &ffi_type_pointer, &p, &ARG(0));

        size_t n;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("the second argument to ffi.str() must be an integer");
                }
                n = ARG(1).integer;
        } else {
                n = strlen(p);
        }

        return vSs(p, n);
}

Value
cffi_as_str(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2) {
                zP("ffi.as_str() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("the first argument to ffi.as_str() must be a pointer");
        }

        size_t n;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("the second argument to ffi.as_str() must be an integer");
                }
                n = ARG(1).integer;
        } else {
                n = strlen(ARG(0).ptr);
        }

        return STRING_NOGC(ARG(0).ptr, n);
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
        if (argc == 0) {
                zP("ffi.closure(): expected at least 1 argument but got %d", argc);
        }

        Value f = ARG(argc - 1);
        vmX();

        if (!CALLABLE(f)) {
                zP("ffi.closure(): last argument must be callable");
        }

        Value cif = cffi_cif(ty, argc - 1, NULL);
        if (cif.type == VALUE_NIL) {
                zP("ffi.closure(): failed to construct cif");
        }

        void *code;
        ffi_closure *closure = ffi_closure_alloc(sizeof *closure, &code);
        if (closure == NULL) {
                zP("ffi.closure(): ffi_closure_alloc() failed");
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
        if (argc != 1) {
                zP("ffi.freeClosure(): expected 1 argument but got %d", argc);
        }

        Value p = ARG(0);
        void **pointers = p.extra;

        ffi_closure_free(pointers[0]);
        mF(pointers[1]);
        mF(pointers);

        return NIL;
}

/* vim: set sts=8 sw=8 expandtab: */
