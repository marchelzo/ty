#include <libco.h>

#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"
#include "class.h"
#include "tthread.h"
#include "compiler.h"
#include "itable.h"

static GCRootSet ImmortalSet;

#define A_LOAD(p)     atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x) atomic_store_explicit((p), (x), memory_order_relaxed)

inline static void
collect(Ty *ty, struct alloc *a)
{
        void *p = a->data;

        Value o;
        Value finalizer;
        Regex *re;
        Thread *t;
        Generator *gen;

        switch (a->type) {
        case GC_ARRAY:
                mF(((struct array *)p)->items);
                break;

        case GC_BLOB:
                mF(((struct blob *)p)->items);
                break;

        case GC_DICT:
                dict_free(ty, p);
                break;

        case GC_GENERATOR:
                gen = p;

                free(gen->frame.items);
                free(gen->st.calls.items);
                free(gen->st.frames.items);
                free(gen->st.targets.items);
                free(gen->st.sps.items);
                free(gen->st.to_drop.items);
                free(gen->gc_roots.items);

                for (int i = 0; i < gen->st.try_stack.capacity; ++i) {
                        free(v__(gen->st.try_stack, i));
                }

                free(gen->st.try_stack.items);

                GCLOG("collect(): free generator   co=%p   ip=%p\n", (void *)gen->co, (void *)gen->ip);

                if (gen->co != ty->co_top) {
                        co_delete(gen->co);
                }
                break;

        case GC_THREAD:
                t = p;

                if (t->v.type == VALUE_NONE) {
                        TyThreadDetach(((Thread *)p)->t);
                }

                TyMutexDestroy(&t->mutex);
                TyCondVarDestroy(&t->cond);
                break;

        case GC_OBJECT:
                o = OBJECT((struct itable *)p, ((struct itable *)p)->class);
                finalizer = class_get_finalizer(ty, o.class);
                if (finalizer.type != VALUE_NONE) {
                        vm_call_method(ty, &o, &finalizer, 0);
                }
                itable_release(ty, p);
                break;

        case GC_REGEX:
                re = p;
                pcre2_code_free(re->pcre2);
                free((char *)re->pattern);
                break;

        case GC_ARENA:
                ForgetSourceNodesFrom(p, a->size);
                break;

        case GC_FUN_INFO:
                mF(((FunUserInfo *)p)->doc);
                mF(((FunUserInfo *)p)->proto);
                mF(((FunUserInfo *)p)->name);
                break;

        case GC_FFI_AUTO:
                finalizer = ((Value *)p)[0];
                o = ((Value *)p)[1];
                if (finalizer.type == VALUE_PTR) {
                        ((void (*)(void *))finalizer.ptr)(o.ptr);
                } else {
                        vmP(&o);
                        vmC(&finalizer, 1);
                }
                break;
        }
}

void
GCForgetObject(Ty *ty, void const *o)
{
        usize n = 0;

        for (usize i = 0; i < vN(ty->allocs); ++i) {
                if (v__(ty->allocs, i)->data != o) {
                        *v_(ty->allocs, n++) = v__(ty->allocs, i);
                } else {
                        MemoryUsed -= v__(ty->allocs, i)->size;
                }
        }

        vN(ty->allocs) = n;
}

void
GCForget(Ty *ty, AllocList *allocs, isize *used)
{
        usize n = 0;

        for (usize i = 0; i < allocs->count;) {
                if (
                        !A_LOAD(&allocs->items[i]->mark)
                     && (A_LOAD(&allocs->items[i]->hard) == 0)
                ) {
                        allocs->items[n++] = allocs->items[i++];
                } else {
                        *used -= min(allocs->items[i]->size, *used);
                }
        }
}

void
GCSweepOwn(Ty *ty)
{
        GC_STOP();

        usize n = 0;

        for (int i = 0; i < vN(ty->allocs); ++i) {
                if (
                        !A_LOAD(&v__(ty->allocs, i)->mark)
                     && (A_LOAD(&v__(ty->allocs, i)->hard) == 0)
                ) {
                        ty->memory_used -= min(v__(ty->allocs, i)->size, ty->memory_used);
                        collect(ty, v__(ty->allocs, i));
                        free(v__(ty->allocs, i));
                } else {
                        A_STORE(&v__(ty->allocs, i)->mark, false);
                        *v_(ty->allocs, n++) = v__(ty->allocs, i);
                }
        }

        vN(ty->allocs) = n;

        GC_RESUME();
}

void
GCSweep(Ty *ty, AllocList *allocs, isize *used)
{
        GC_STOP();

        usize n = 0;

        for (int i = 0; i < vN(*allocs); ++i) {
                if (
                        !A_LOAD(&v__(*allocs, i)->mark)
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        collect(ty, v__(*allocs, i));
                        free(v__(*allocs, i));
                } else {
                        A_STORE(&v__(*allocs, i)->mark, false);
                        *v_(*allocs, n++) = v__(*allocs, i);
                }
        }

        vN(*allocs) = n;

        GC_RESUME();
}

void
GCTakeOwnership(Ty *ty, AllocList *new)
{
        for (usize i = 0; i < new->count; ++i) {
                xvP(ty->allocs, new->items[i]);
                MemoryUsed += new->items[i]->size;
        }
}

void
gc(Ty *ty)
{
        DoGC(ty);
}

void
gc_register(Ty *ty, void *p)
{
        xvP(ty->allocs, ALLOC_OF(p));
}

void
gc_immortalize(Ty *ty, Value const *v)
{
        xvP(ImmortalSet, *v);
}

void
gc_clear_root_set(Ty *ty)
{
        RootSet.count = 0;
}

void
gc_truncate_root_set(Ty *ty, usize n)
{
        RootSet.count = n;
}

usize
gc_root_set_count(Ty *ty)
{
        return RootSet.count;
}

GCRootSet *
GCRoots(Ty *ty)
{
        return &RootSet;
}

void *
GCImmortalSet(Ty *ty)
{
        return &ImmortalSet;
}

/* vim: set sts=8 sw=8 expandtab: */
