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
#include "chan.h"

static GCRootSet ImmortalSet;

#define A_LOAD(p)      atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x)  atomic_store_explicit((p), (x), memory_order_relaxed)
#define IS_WHITE(a)    (A_LOAD(&(a)->color) == GC_WHITE)

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

        case GC_QUEUE:
                mF(((Queue *)p)->items);
                break;

        case GC_SHARED_QUEUE:
                mF(((Queue *)p)->items);
                TyMutexDestroy(&((SharedQueue *)p)->mutex);
                TyCondVarDestroy(&((SharedQueue *)p)->cond);
                break;

        case GC_GENERATOR:
                gen = p;
                if (UNLIKELY((gen->co != ty->co_top) & (gen->co != NULL))) {
                        xvP(ty->cothreads, gen->co);
                }
#if !defined(TY_NO_JIT) && 0
                if (gen->st.jit.cont != NULL) {
                        xvP(ty->jit_stacks, gen->st.jit.cont);
                }
                m0(gen->st.jit);
#endif
                if (LIKELY(gen->st != NULL)) {
                        xvP(ty->co_states, gen->st);
                }
                break;

        case GC_MUTEX:
                TyMutexDestroy(p);
                break;

        case GC_SPINLOCK:
                TySpinLockDestroy(p);
                break;

        case GC_CONDVAR:
                TyCondVarDestroy(p);
                break;

        case GC_NOTE:
                TyNoteFree(*(TyNote *)p);
                break;

        case GC_COUNTER:
                TyCounterFree(*(TyCounter *)p);
                break;

        case GC_CHANNEL:
                chan_destroy(ty, p);
                break;

        case GC_THREAD:
                t = p;
                if (!t->joined && !t->detached) {
                        TyMutexLock(&t->mutex);
                        if (!t->alive) {
                                TyThreadJoin(t->t);
                        } else {
                                TyThreadDetach(t->t);
                        }
                        TyMutexUnlock(&t->mutex);
                }
                TyMutexDestroy(&t->mutex);
                TyCondVarDestroy(&t->cond);
                break;

        case GC_OBJECT:
                o = OBJECT((TyObject *)p, ((TyObject *)p)->class->i);
                finalizer = class_get_finalizer(ty, o.class);
                if (finalizer.type != VALUE_NONE) {
                        vm_call_method(ty, &o, &finalizer, 0);
                }
                if (o.object->dynamic != NULL) {
                        itable_release(ty, o.object->dynamic);
                }
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
                        !IS_WHITE(v__(*allocs, i))
                     || (A_LOAD(&v__(*allocs, i)->hard) != 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        A_STORE(&v__(*allocs, i)->color, GC_WHITE);
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
                        IS_WHITE(a)
                     && (A_LOAD(&a->hard) == 0)
                ) {
                        ty->memory_used -= min(a->size, ty->memory_used);
                        collect(ty, a);
                        ty_free(a);
                } else {
                        A_STORE(&a->color, GC_WHITE);
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
                        IS_WHITE(v__(*allocs, i))
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        collect(ty, v__(*allocs, i));
                        ty_free(v__(*allocs, i));
                } else {
                        A_STORE(&v__(*allocs, i)->color, GC_WHITE);
                        *v_(*allocs, n++) = v__(*allocs, i);
                }
        }
        GC_RESUME();

        vN(*allocs) = n;
}

bool
GCSweepSome(Ty *ty, int n)
{
        GC_STOP();

        int r = ty->gc_sweep_read;
        int w = ty->gc_sweep_write;
        int end = vN(ty->allocs);
        int limit = r + n;
        if (limit > end) limit = end;

        while (r < limit) {
                struct alloc *a = v__(ty->allocs, r);
                if (
                        IS_WHITE(a)
                     && (A_LOAD(&a->hard) == 0)
                ) {
#ifndef TY_RELEASE
                        if (a->type == GC_OBJECT) {
                                for (int si = 0; si < vN(ty->stack); ++si) {
                                        Value *sv = v_(ty->stack, si);
                                        if (sv->type == VALUE_OBJECT && sv->object == (TyObject *)a->data) {
                                                fprintf(stderr, "BUG: sweeping object %p live at stack[%d]\n", (void*)a->data, si);
                                                __builtin_trap();
                                        }
                                }
                        }
#endif
                        ty->memory_used -= min(a->size, ty->memory_used);
                        collect(ty, a);
                        ty_free(a);
                } else {
                        A_STORE(&a->color, GC_WHITE);
                        *v_(ty->allocs, w++) = a;
                }
                r += 1;
        }

        ty->gc_sweep_read = r;
        ty->gc_sweep_write = w;

        GC_RESUME();

        if (r >= end) {
                vN(ty->allocs) = w;
                return true;
        }

        return false;
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
        GCRunFullCycle(ty);
}

void
gc_register(Ty *ty, void *p)
{
        xvP(ty->allocs, ALLOC_OF(p));
}

void
gc_shade_value(Ty *ty, Value const *v)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_ARRAY:            if (v->array   && !MARKED(v->array))   SHADE_GRAY(v->array);   break;
        case VALUE_DICT:             if (v->dict    && !MARKED(v->dict))    SHADE_GRAY(v->dict);    break;
        case VALUE_OBJECT:           if (v->object  && !MARKED(v->object))  SHADE_GRAY(v->object);  break;
        case VALUE_BLOB:             if (v->blob    && !MARKED(v->blob))    SHADE_GRAY(v->blob);    break;
        case VALUE_TUPLE:            if (v->items   && !MARKED(v->items))   SHADE_GRAY(v->items);   break;
        case VALUE_GENERATOR:        if (v->gen     && !MARKED(v->gen))     SHADE_GRAY(v->gen);     break;
        case VALUE_THREAD:           if (v->thread  && !MARKED(v->thread))  SHADE_GRAY(v->thread);  break;
        case VALUE_QUEUE:            if (v->queue   && !MARKED(v->queue))   SHADE_GRAY(v->queue);   break;
        case VALUE_SHARED_QUEUE:     if (v->shared_queue && !MARKED(v->shared_queue)) SHADE_GRAY(v->shared_queue); break;
        case VALUE_REF:              if (v->ref     && !MARKED(v->ref))     SHADE_GRAY(v->ref);     break;
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:   if (v->this    && !MARKED(v->this))    SHADE_GRAY(v->this);    break;
        case VALUE_NATIVE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_FUNCTION:
                if (v->info != NULL && v->env != NULL && !MARKED(v->env)) SHADE_GRAY(v->env);
                break;
        case VALUE_STRING:           if (!v->ro && v->str0 && !MARKED(v->str0)) SHADE_GRAY(v->str0); break;
        default: break;
        }
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
