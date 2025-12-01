#include <sys/mman.h>

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
                mF(((Array *)p)->items);
                break;

        case GC_BLOB:
                mF(((Blob *)p)->items);
                break;

        case GC_DICT:
                dict_free(ty, p);
                break;

        case GC_GENERATOR:
                gen = p;

                ty_free(gen->frame.items);
                ty_free(gen->st.calls.items);
                ty_free(gen->st.frames.items);
                ty_free(gen->st.targets.items);
                ty_free(gen->st.sps.items);
                ty_free(gen->st.to_drop.items);
                ty_free(gen->gc_roots.items);

                for (int i = 0; i < gen->st.try_stack.capacity; ++i) {
                        ty_free(v__(gen->st.try_stack, i));
                }

                ty_free(gen->st.try_stack.items);

                GCLOG("collect(): free generator   co=%p   ip=%p\n", (void *)gen->co, (void *)gen->ip);

                if (gen->co != ty->co_top) {
                        ty_free(gen->co);
                }
                break;

        case GC_THREAD:
                t = p;
                if (!t->joined) {
                        if (!t->alive) {
                                TyThreadJoin(((Thread *)p)->t);
                        } else {
                                TyThreadDetach(((Thread *)p)->t);
                        }
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
                ty_free((char *)re->pattern);
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
        for (usize i = 0; i < vN(*allocs); ++i) {
                if (
                        A_LOAD(&v__(*allocs, i)->mark)
                     || (A_LOAD(&v__(*allocs, i)->hard) != 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        A_STORE(&v__(*allocs, i)->mark, false);
                        SWAP(struct alloc *, v__(*allocs, i), v_L(*allocs));
                        vvX(*allocs);
                }
        }
}

void
GCSweepTy(Ty *ty)
{
        usize n = 0;

        GC_STOP();
        for (int i = 0; i < vN(ty->allocs); ++i) {
                struct alloc *a = v__(ty->allocs, i);
                if (
                        !A_LOAD(&a->mark)
                     && (A_LOAD(&a->hard) == 0)
                ) {
                        ty->memory_used -= min(a->size, ty->memory_used);
                        collect(ty, a);
                        ty_free(a);
                } else {
                        A_STORE(&a->mark, false);
                        *v_(ty->allocs, n++) = a;
                }
        }
        GC_RESUME();

        vN(ty->allocs) = n;
}

void
GCSweep(Ty *ty, AllocList *allocs, isize *used)
{
        usize n = 0;

        GC_STOP();
        for (int i = 0; i < vN(*allocs); ++i) {
                if (
                        !A_LOAD(&v__(*allocs, i)->mark)
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        collect(ty, v__(*allocs, i));
                        ty_free(v__(*allocs, i));
                } else {
                        A_STORE(&v__(*allocs, i)->mark, false);
                        *v_(*allocs, n++) = v__(*allocs, i);
                }
        }
        GC_RESUME();

        vN(*allocs) = n;
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
        v0(RootSet);
}

void
gc_truncate_root_set(Ty *ty, usize n)
{
        vN(RootSet) = n;
}

usize
gc_root_set_count(Ty *ty)
{
        return vN(RootSet);
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
