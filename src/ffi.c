#include <ffi.h>

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

inline static intmax_t
int_from(Value const *v)
{
        return (v->type == VALUE_INTEGER) ? v->integer : v->real;
}

static void
store(Ty *ty, ffi_type *t, void *p, Value const *v)
{
        size_t offsets[64];
        Value *f, ptr;

        switch (t->type) {
        case FFI_TYPE_INT:
                *(int *)p = int_from(v);
                break;
        case FFI_TYPE_UINT32:
                *(uint32_t *)p = int_from(v);
                break;
        case FFI_TYPE_UINT16:
                *(uint16_t *)p = int_from(v);
                break;
        case FFI_TYPE_UINT64:
                *(uint64_t *)p = int_from(v);
                break;
        case FFI_TYPE_UINT8:
                *(uint8_t *)p = int_from(v);
                break;
        case FFI_TYPE_SINT32:
                *(int32_t *)p = int_from(v);
                break;
        case FFI_TYPE_SINT16:
                *(int16_t *)p = int_from(v);
                break;
        case FFI_TYPE_SINT64:
                *(int64_t *)p = int_from(v);
                break;
        case FFI_TYPE_SINT8:
                *(int8_t *)p = int_from(v);
                break;
        case FFI_TYPE_FLOAT:
                *(float *)p = float_from(v);
                break;
        case FFI_TYPE_DOUBLE:
                *(double *)p = float_from(v);
                break;
        case FFI_TYPE_POINTER:
                switch (v->type) {
                case VALUE_PTR:
                        *(void **)p = v->ptr;
                        break;
                case VALUE_STRING:
                        *(void **)p = (void *)v->string;
                        break;
                case VALUE_NIL:
                        *(void **)p = NULL;
                        break;
                case VALUE_BLOB:
                        *(void **)p = (void *)v->blob->items;
                        break;
                case VALUE_OBJECT:
                        f = class_method(ty, v->class, "__ptr__");
                        if (f != NULL)
                                *(void **)p = vm_call_method(ty, v, f, 0).ptr;
                        else
                                *(void **)p = NULL;
                        break;
                }
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
                        f = class_method(ty, v->class, "__ptr__");
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
load(Ty *ty, ffi_type *t, void const *p)
{
        void * const *vp;
        Value v;
        int n;

        switch (t->type) {
        case FFI_TYPE_INT:    return INTEGER(*(int const *)p);
        case FFI_TYPE_SINT8:  return INTEGER(*(int8_t const *)p);
        case FFI_TYPE_SINT16: return INTEGER(*(int16_t const *)p);
        case FFI_TYPE_SINT32: return INTEGER(*(int32_t const *)p);
        case FFI_TYPE_SINT64: return INTEGER(*(int64_t const *)p);
        case FFI_TYPE_UINT8:  return INTEGER(*(uint8_t const *)p);
        case FFI_TYPE_UINT16: return INTEGER(*(uint16_t const *)p);
        case FFI_TYPE_UINT32: return INTEGER(*(uint32_t const *)p);
        case FFI_TYPE_UINT64: return INTEGER(*(uint64_t const *)p);

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

                size_t offsets[64];
                ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, offsets);

                for (int i = 0; i < n; ++i) {
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
                vec_empty(ty, ats);
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
                        vec_empty(ty, ats);
                        mF(cif);
                        return NIL;
                }
        } else if (ffi_prep_cif(cif, FFI_DEFAULT_ABI, max(0, argc - 1), rt, ats.items) != FFI_OK) {
                vec_empty(ty, ats);
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
        if (argc != 1) {
                zP("ffi.free() expects exactly 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("ffi.free() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        free(ARG(0).ptr);

        return NIL;
}

Value
cffi_alloc(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("ffi.alloc() expects 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER) {
                zP("ffi.alloc() expects an integer but got: %s", VSC(&ARG(0)));
        }

        if (ARG(0).integer <= 0)
                return NIL;

        void *p = malloc(ARG(0).integer);

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
        if (i.type != VALUE_INTEGER || i.integer < 0 || i.integer >= n) {
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
        if (i.type != VALUE_INTEGER || i.integer < 0 || i.integer >= n) {
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
        if (argc == 3) {
                return cffi_load_n(ty, argc, kwargs);
        }

        if (argc == 1) {
                ffi_type *t = (ARG(0).extra == NULL) ? &ffi_type_uint8 : ARG(0).extra;
                return load(ty, t, ARG(0).ptr);
        }

        return load(ty, ARG(0).ptr, ARG(1).ptr);
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
                zP("ffi.store(ty): expected 2 or 3 arguments but got %d", argc);
        }

        if (vPtr.type != VALUE_PTR) {
                zP("ffi.store(ty): expected pointer but got: %s", VSC(&vPtr));
        }

        if (vType.type == VALUE_NONE) {
                vType = PTR(vPtr.extra == NULL ? &ffi_type_uint8 : (ffi_type *)vPtr.extra);
        } else if (vType.type != VALUE_PTR) {
                zP("ffi.store(ty): expected pointer but got: %s", VSC(&vType));
        }

        store(ty, vType.ptr, vPtr.ptr, &vVal);

        return NIL;
}

Value
cffi_call(Ty *ty, int argc, Value *kwargs)
{
        if (argc < 2) {
                zP("ffi.call() expects at least 2 arguments (cif, function) but got %d", argc);
        }

        ffi_cif *cif;
        if (ARG(0).type == VALUE_PTR) {
                cif = ARG(0).ptr;
        } else {
                zP("the first argument to ffi.call() must be a pointer");
        }

        void (*func)(void);
        if (ARG(1).type == VALUE_PTR) {
                func = (void (*)(void))ARG(1).ptr;
        } else {
                zP("the second argument to ffi.call() must be a pointer");
        }

        vec(void *) args = {0};
        for (int i = 2; i < argc; ++i) {
                if (ARG(i).type == VALUE_PTR) {
                        vec_nogc_push(args, ARG(i).ptr);
                } else {
                        free(args.items);
                        zP("non-pointer passed as argument %d to ffi.call()", i + 1);
                }
        }

        char buf[4096] __attribute__((aligned (_Alignof (max_align_t))));
        Value *out = NAMED("out");
        void *ret;

        if (out == NULL) {
                ret = buf;
        } else switch (out->type) {
        case VALUE_PTR:
                ret = out->ptr;
                break;
        case VALUE_BLOB:
                ret = out->blob->items;
                break;
        default:
                zP("invalid `out` argument to ffi.call(): %s", VSC(out));
        }

        lGv(true);
        ffi_call(cif, func, ret, args.items);
        lTk();

        free(args.items);

        return (out == NULL) ? load(ty, cif->rtype, ret) : PTR(ret);
}

Value
cffi_dlopen(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2) {
                zP("ffi.dlopen() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_STRING) {
                zP("the first argument to ffi.dlopen() must be a string");
        }

        char b[512];
        int n = min(ARG(0).bytes, sizeof b - 1);

        memcpy(b, ARG(0).string, n);
        b[n] = '\0';

#ifdef _WIN32
        void *p = LoadLibraryA(b);
#else
        void *p = dlopen(b, RTLD_NOW);
#endif
        return (p == NULL) ? NIL : PTR(p);
}

Value
cffi_blob(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 2) {
                zP("ffi.blob() expects 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                zP("the first argument to ffi.blob() must be a pointer, instead got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("the second argument to ffi.blob() must be an integer, instead got: %s", VSC(&ARG(1)));
        }

        // TODO: should be a 'frozen' blob or something
        // cant realloc() this pointer and don't know
        // how long it's valid -- risky
        struct blob *b = mA(sizeof *b);
        b->items = ARG(0).ptr;
        b->count = ARG(1).integer;
        b->capacity = b->count;

        return BLOB(b);
}

Value
cffi_clone(Ty *ty, int argc, Value *kwargs)
{
        if (argc != 2) {
                zP("ffi.clone() expects 2 arguments but got %d", argc);
        }

        void *p;
        store(ty, &ffi_type_pointer, &p, &ARG(0));

        if (ARG(1).type != VALUE_INTEGER) {
                zP("the second argument to ffi.clone() must be an integer");
        }

        size_t n = ARG(1).integer;
        void *clone = mAo(n, GC_ANY);

        memcpy(clone, p, n);


        return PTR(clone);
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

        return vSc(p, n);
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

        return vSc(error, strlen(error));
#endif
}

Value
cffi_dlsym(Ty *ty, int argc, Value *kwargs)
{
        if (argc == 0 || argc > 2) {
                zP("ffi.dlsym() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_STRING) {
                zP("the first argument to ffi.dlsym() must be a string");
        }

        char b[64];
        int n = min(ARG(0).bytes, sizeof b - 1);

        memcpy(b, ARG(0).string, n);
        b[n] = '\0';

        void *handle;
        if (argc == 2 && ARG(1).type != VALUE_NIL) {
                if (ARG(1).type != VALUE_PTR) {
                        zP("the second argument to ffi.dlsym() must be a pointer, instead got: %s", VSC(&ARG(1)));
                }
                handle = ARG(1).ptr;
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
        void *p = dlsym(handle, b);
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
        t->alignment = 0;
        t->size = 0;
        t->elements = mA((argc + 1) * sizeof (ffi_type *));

        for (int i = 0; i < argc; ++i) {
                Value member = ARG(i);

                if (member.type != VALUE_PTR) {
                        zP("non-pointer passed to ffi.struct()");
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
