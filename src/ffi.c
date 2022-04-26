#include <ffi.h>
#include <dlfcn.h>

#include "value.h"
#include "alloc.h"
#include "util.h"
#include "vm.h"
#include "cffi.h"

static void
store(ffi_type *t, void *p, struct value const *v)
{
        size_t offsets[64];

        switch (t->type) {
        case FFI_TYPE_INT:
                *(int *)p = v->integer;
                break;
        case FFI_TYPE_UINT32:
                *(uint32_t *)p = v->integer;
                break;
        case FFI_TYPE_UINT16:
                *(uint16_t *)p = v->integer;
                break;
        case FFI_TYPE_UINT64:
                *(uint64_t *)p = v->integer;
                break;
        case FFI_TYPE_UINT8:
                *(uint8_t *)p = v->integer;
                break;
        case FFI_TYPE_SINT32:
                *(int32_t *)p = v->integer;
                break;
        case FFI_TYPE_SINT16:
                *(int16_t *)p = v->integer;
                break;
        case FFI_TYPE_SINT64:
                *(int64_t *)p = v->integer;
                break;
        case FFI_TYPE_SINT8:
                *(int8_t *)p = v->integer;
                break;
        case FFI_TYPE_FLOAT:
                *(float *)p = v->real;
                break;
        case FFI_TYPE_DOUBLE:
                *(double *)p = v->real;
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
                }
                break;
        case FFI_TYPE_STRUCT:
                if (v->type == VALUE_TUPLE) {
                        ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, offsets);

                        for (int i = 0; i < v->count; ++i) {
                                store(t->elements[i], (char *)p + offsets[i], &v->items[i]);
                        }
                } else if (v->type == VALUE_PTR) {
                        memcpy(p, v->ptr, t->size);
                }
        }
}

static struct value
load(ffi_type *t, void const *p)
{
        void * const *vp;
        struct value v;
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

                v = value_tuple(n);
                NOGC(v.items);

                size_t offsets[64];
                ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, offsets);

                for (int i = 0; i < n; ++i) {
                        v.items[i] = load(t->elements[i], (char *)p + offsets[i]);
                }

                OKGC(v.items);

                return v;
        }

        return NIL;
}

static void
closure_func(ffi_cif *cif, void *ret, void **args, void *data)
{
        for (int i = 0; i < cif->nargs; ++i) {
                struct value arg = load(cif->arg_types[i], args[i]);
                vm_push(&arg);
        }

        struct value rv = vm_call(data, cif->nargs);

        switch (cif->rtype->type) {
        case FFI_TYPE_VOID:
                break;
        case FFI_TYPE_INT:
        case FFI_TYPE_SINT8:
        case FFI_TYPE_SINT16:
        case FFI_TYPE_SINT32:
                store(&ffi_type_sint64, ret, &rv);
                break;
        case FFI_TYPE_UINT8:
        case FFI_TYPE_UINT16:
        case FFI_TYPE_UINT32:
                store(&ffi_type_uint64, ret, &rv);
                break;
        default:
                store(cif->rtype, ret, &rv);
        }
}

struct value
cffi_cif(int argc, struct value *kwargs)
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
                vm_panic("invalid type passed to ffi.cif()");
        }

        for (int i = 1; i < argc; ++i) {
                if (ARG(i).type != VALUE_PTR) {
                        goto Bad;
                }

                vec_push(ats, ARG(i).ptr);
        }

        ffi_cif *cif = gc_alloc(sizeof *cif);

        if (ffi_prep_cif(cif, FFI_DEFAULT_ABI, max(0, argc - 1), rt, ats.items) != FFI_OK) {
                vec_empty(ats);
                gc_free(cif);
                return NIL;
        }

        return PTR(cif);
}

struct value
cffi_addr(int argc, struct value *kwargs)
{
        if (argc != 1) {
                vm_panic("ffi.addr() expects 1 argument but got %d", argc);
        }

        struct value v = ARG(0);

        if (v.type != VALUE_PTR) {
                vm_panic("ffi.addr() expects a pointer but got: %s", value_show(&v));
        }

        void **p = gc_alloc(sizeof *p);
        *p = v.ptr;

        return PTR(p);
}

struct value
cffi_free(int argc, struct value *kwargs)
{
        if (argc != 1) {
                vm_panic("ffi.free() expects exactly 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("ffi.free() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        free(ARG(0).ptr);

        return NIL;
}

struct value
cffi_alloc(int argc, struct value *kwargs)
{
        if (argc != 1) {
                vm_panic("ffi.alloc() expects 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER) {
                vm_panic("ffi.alloc() expects an integer but got: %s", value_show(&ARG(0)));
        }

        if (ARG(0).integer <= 0)
                return NIL;

        void *p = malloc(ARG(0).integer);

        return (p == NULL) ? NIL : PTR(p);
}

struct value
cffi_realloc(int argc, struct value *kwargs)
{
        if (argc != 2) {
                vm_panic("ffi.realloc() expects 2 arguments but got %d", argc);
        }

		if (ARG(0).type != VALUE_PTR) {
			vm_panic("ffi.realloc(): expected pointer as first argument but got: %s", value_show(&ARG(0)));
		}

        if (ARG(1).type != VALUE_INTEGER) {
                vm_panic("ffi.realloc(): expected integer as second argument but got: %s", value_show(&ARG(1)));
        }

        if (ARG(1).integer <= 0)
                return NIL;

        void *p = realloc(ARG(0).ptr, ARG(1).integer);

        return (p == NULL) ? NIL : PTR(p);
}

struct value
cffi_size(int argc, struct value *kwargs)
{
        if (argc != 1) {
                vm_panic("ffi.size() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("the argument to ffi.size() must be a pointer");
        }

        return INTEGER(((ffi_type *)ARG(0).ptr)->size);
}

struct value
cffi_new(int argc, struct value *kwargs)
{
        if (argc != 1 && argc != 2) {
                vm_panic("ffi.new() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("the argument to ffi.new() must be a pointer");
        }

        ffi_type *t = ARG(0).ptr;

        struct value p = PTR(aligned_alloc(t->alignment, t->size));

        if (argc == 2) {
                struct value v = ARG(1);
                store(t, p.ptr, &v);
        } else {
                memset(p.ptr, 0, t->size);
        }

        return p;
}

struct value
cffi_member(int argc, struct value *kwargs)
{
        if (argc != 3 && argc != 4) {
                vm_panic("ffi.member() expects 3 or 4 arguments but got %d", argc);
        }

        struct value t = ARG(0);
        if (t.type != VALUE_PTR) {
                vm_panic("the first argument to ffi.member() must be a pointer");
        }

        ffi_type *type = t.ptr;

        int n = 0;
        while (type->elements[n] != NULL) {
                n += 1;
        }

        struct value p = ARG(1);
        if (p.type != VALUE_PTR) {
                vm_panic("the second argument to ffi.member() must be a pointer");
        }

        struct value i = ARG(2);
        if (i.type != VALUE_INTEGER || i.integer < 0 || i.integer >= n) {
                vm_panic("invalid third argument to ffi.member(): %s", value_show(&i));
        }

        size_t offsets[64];
        ffi_get_struct_offsets(FFI_DEFAULT_ABI, type, offsets);

        if (argc == 3) {
                return load(type->elements[i.integer], (char const *)p.ptr + offsets[i.integer]);
        } else {
                store(type->elements[i.integer], (char *)p.ptr + offsets[i.integer], &ARG(3));
                return NIL;
        }
}

struct value
cffi_load(int argc, struct value *kwargs)
{
        if (argc == 3) {
                return cffi_load_n(argc, kwargs);
        }

        ffi_type *t = ARG(0).ptr;
        return load(t, ARG(1).ptr);
}

struct value
cffi_load_n(int argc, struct value *kwargs)
{
        ffi_type *t = ARG(0).ptr;
        char *p = ARG(1).ptr;
        size_t n = ARG(2).integer;

        struct array *a = value_array_new();

        NOGC(a);

        for (int i = 0; i < n; ++i) {
            value_array_push(a, load(t, p + (i * t->size)));
        }

        OKGC(a);

        return ARRAY(a);
}

struct value
cffi_store(int argc, struct value *kwargs)
{
        if (argc != 3) {
                vm_panic("ffi.store(): expected 3 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("ffi.store(): expected pointer as first argument but got: %s", value_show(&ARG(0)));
        }

        ffi_type *t = ARG(0).ptr;

        if (ARG(1).type != VALUE_PTR) {
                vm_panic("ffi.store(): expected pointer as second argument but got: %s", value_show(&ARG(1)));
        }

        void *p = ARG(1).ptr;

        struct value v = ARG(2);

        store(t, p, &v);

        return NIL;
}

struct value
cffi_call(int argc, struct value *kwargs)
{
        if (argc < 2) {
                vm_panic("ffi.call() expects at least 2 arguments (cif, function) but got %d", argc);
        }

        ffi_cif *cif;
        if (ARG(0).type == VALUE_PTR) {
                cif = ARG(0).ptr;
        } else {
                vm_panic("the first argument to ffi.call() must be a pointer");
        }

        void (*func)(void);
        if (ARG(1).type == VALUE_PTR) {
                func = (void (*)(void))ARG(1).ptr;
        } else {
                vm_panic("the second argument to ffi.call() must be a pointer");
        }

        vec(void *) args = {0};
        for (int i = 2; i < argc; ++i) {
                if (ARG(i).type == VALUE_PTR) {
                        vec_push(args, ARG(i).ptr);
                } else {
                        vec_empty(args);
                        vm_panic("non-pointer passed as argument %d to ffi.call()", i + 1);
                }
        }

        char ret[sizeof (ffi_arg)] __attribute__((aligned (_Alignof (max_align_t))));

        ffi_call(cif, func, ret, args.items);

        vec_empty(args);

        return load(cif->rtype, ret);
}

struct value
cffi_dlopen(int argc, struct value *kwargs)
{
        if (argc != 1 && argc != 2) {
                vm_panic("ffi.dlopen() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_STRING) {
                vm_panic("the first argument to ffi.dlopen() must be a string");
        }

        char b[512];
        int n = min(ARG(0).bytes, sizeof b - 1);

        memcpy(b, ARG(0).string, n);
        b[n] = '\0';

        void *p = dlopen(b, RTLD_NOW);

        return (p == NULL) ? NIL : PTR(p);
}

struct value
cffi_blob(int argc, struct value *kwargs)
{
        if (argc != 2) {
                vm_panic("ffi.blob() expects 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("the first argument to ffi.blob() must be a pointer, instead got: %s", value_show(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                vm_panic("the second argument to ffi.blob() must be an integer, instead got: %s", value_show(&ARG(1)));
        }

        // TODO: should be a 'frozen' blob or something
        // cant realloc() this pointer and don't know
        // how long it's valid -- risky
        struct blob *b = gc_alloc(sizeof *b);
        b->items = ARG(0).ptr;
        b->count = ARG(1).integer;
        b->capacity = b->count;

        return BLOB(b);
}

struct value
cffi_clone(int argc, struct value *kwargs)
{
        if (argc != 2) {
                vm_panic("ffi.clone() expects 2 arguments but got %d", argc);
        }

        void *p;
        store(&ffi_type_pointer, &p, &ARG(0));

        if (ARG(1).type != VALUE_INTEGER) {
                vm_panic("the second argument to ffi.clone() must be an integer");
        }

        size_t n = ARG(1).integer;
        void *clone = gc_alloc_object(n, GC_NONE);

        memcpy(clone, p, n);


        return PTR(clone);
}

struct value
cffi_str(int argc, struct value *kwargs)
{
        if (argc != 1 && argc != 2) {
                vm_panic("ffi.str() expects 1 or 2 arguments but got %d", argc);
        }

        void *p;
        store(&ffi_type_pointer, &p, &ARG(0));

        size_t n;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        vm_panic("the second argument to ffi.str() must be an integer");
                }
                n = ARG(1).integer;
        } else {
                n = strlen(p);
        }

        return STRING_CLONE(p, n);
}

struct value
cffi_as_str(int argc, struct value *kwargs)
{
        if (argc != 1 && argc != 2) {
                vm_panic("ffi.as_str() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("the first argument to ffi.as_str() must be a pointer");
        }

        size_t n;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        vm_panic("the second argument to ffi.as_str() must be an integer");
                }
                n = ARG(1).integer;
        } else {
                n = strlen(ARG(0).ptr);
        }

        return STRING_NOGC(ARG(0).ptr, n);
}

struct value
cffi_dlsym(int argc, struct value *kwargs)
{
        if (argc == 0 || argc > 2) {
                vm_panic("ffi.dlsym() expects 1 or 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_STRING) {
                vm_panic("the first argument to ffi.dlsym() must be a string");
        }

        char b[64];
        int n = min(ARG(0).bytes, sizeof b - 1);

        memcpy(b, ARG(0).string, n);
        b[n] = '\0';

        void *handle;
        if (argc == 2 && ARG(1).type != VALUE_NIL) {
                if (ARG(1).type != VALUE_PTR) {
                        vm_panic("the second argument to ffi.dlsym() must be a pointer, instead got: %s", value_show(&ARG(1)));
                }
                handle = ARG(1).ptr;
        } else {
                handle = RTLD_DEFAULT;
        }

        void *p = dlsym(handle, b);

        return (p == NULL) ? NIL : PTR(p);
}

struct value
cffi_struct(int argc, struct value *kwargs)
{
        if (argc == 0) {
                vm_panic("ffi.struct() expects at least 1 argument");
        }

        ffi_type *t = gc_alloc(sizeof *t);

        t->type = FFI_TYPE_STRUCT;
        t->alignment = 0;
        t->size = 0;
        t->elements = gc_alloc(sizeof (ffi_type *[argc + 1]));

        for (int i = 0; i < argc; ++i) {
                struct value member = ARG(i);

                if (member.type != VALUE_PTR) {
                        vm_panic("non-pointer passed to ffi.struct()");
                }

                t->elements[i] = member.ptr;
        }

        t->elements[argc] = NULL;

        ffi_get_struct_offsets(FFI_DEFAULT_ABI, t, NULL);

        return PTR(t);
}

struct value
cffi_closure(int argc, struct value *kwargs)
{
        if (argc == 0) {
                vm_panic("ffi.closure(): expected at least 1 argument but got %d", argc);
        }

        struct value f = ARG(argc - 1);
		vm_pop();

        if (!CALLABLE(f)) {
                vm_panic("ffi.closure(): last argument must be callable");
        }

        struct value cif = cffi_cif(argc - 1, NULL);

		if (cif.type == VALUE_NIL) {
			vm_panic("ffi.closure(): failed to construct cif");
		}

        void *code;

        ffi_closure *closure = ffi_closure_alloc(sizeof *closure, &code);

        if (closure == NULL) {
                vm_panic("ffi.closure(): ffi_closure_alloc() failed");
        }

        struct value *data = gc_alloc_object(sizeof *data, GC_VALUE);
        *data = f;

		void **pointers = gc_alloc(sizeof (void *[2]));
		pointers[0] = closure;
		pointers[1] = cif.ptr;

        if (ffi_prep_closure_loc(closure, cif.ptr, closure_func, data, code) == FFI_OK) {
                return EPTR(code, data, pointers);
        } else {
                gc_free(data);
                ffi_closure_free(closure);
                return NIL;
        }
}

struct value
cffi_closure_free(int argc, struct value *kwargs)
{
	if (argc != 1) {
		vm_panic("ffi.freeClosure(): expected 1 argument but got %d", argc);
	}

	struct value p = ARG(0);

	void **pointers = p.extra;

	ffi_closure_free(pointers[0]);
	gc_free(pointers[1]);
	gc_free(pointers);

	return NIL;
}
