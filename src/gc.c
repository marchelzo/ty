#include <sys/mman.h>

#include <libco.h>

#include "gc.h"
#include "dict.h"
#include "set.h"
#include "heap.h"
#include "object.h"
#include "vm.h"
#include "log.h"
#include "class.h"
#include "ty/thread.h"
#include "compiler.h"
#include "alloc.h"
#include "itable.h"
#include "chan.h"
#include "queue.h"
#include "screen.h"
#include "jit/lir.h"

static GCRootSet ImmortalSet;
static TySpinLock ImmortalLock = TY_MUTEX_INIT;

#define A_LOAD(p)     atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x) atomic_store_explicit((p), (x), memory_order_relaxed)

inline static void
finalize(Ty *ty, struct alloc *a)
{
        TyObject *obj = (TyObject *)a->data;
        Value     o;
        Value     f;

        switch (a->type) {
        case GC_OBJECT:
                o = OBJECT(obj, obj->class->i);
                f = class_get_finalizer(ty, o.class);
                if (!obj->finalized && f.type != VALUE_NONE) {
                        obj->finalized = true;
                        vm_call_method(ty, &o, &f, 0);
                }
                break;

        case GC_FFI_AUTO:
                o = ((Value *)a->data)[1];
                f = ((Value *)a->data)[0];
                if (f.type == VALUE_PTR) {
                        ((void (*)(void *))f.ptr)(o.ptr);
                } else {
                        vmP(&o);
                        vmC(&f, 1);
                }
                break;
        }
}

inline static void
collect(Ty *ty, struct alloc *a)
{
        void *p = a->data;

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

        case GC_SET:
                set_free(ty, p);
                break;

        case GC_HEAP:
                heap_free(ty, p);
                break;

        case GC_QUEUE:
                mF(((Queue *)p)->items);
                break;

        case GC_SHARED_QUEUE:
                shared_queue_free(ty, p);
                break;

        case GC_GENERATOR:
                gen = p;
                if (UNLIKELY((gen->co != ty->co_top) & (gen->co != NULL))) {
                        xvP(ty->cothreads, gen->co);
                }
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

        case GC_SCREEN:
                screen_free(ty, p);
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
                finalize(ty, a);
                if (((TyObject *)p)->dynamic != NULL) {
                        itable_release(ty, ((TyObject *)p)->dynamic);
                }
                break;

        case GC_REGEX:
                re = p;
                pcre2_code_free(re->pcre2);
                ty_free((char *)re->pattern);
                break;

        case GC_ARENA:
#if defined(TY_SYSMALLOC)
                FreeArenaChunks(p);
#else
                ForgetSourceNodesFrom(p, a->size);
#endif
                ArenaForget(p);
                break;

        case GC_FUN_INFO:
                mF(((FunUserInfo *)p)->doc);
                mF(((FunUserInfo *)p)->proto);
                mF(((FunUserInfo *)p)->name);
                break;

        case GC_JIT_CODE:
                lir_code_destroy(p);
                break;

        case GC_LIR:
                lir_destroy(p);
                break;

        case GC_FFI_AUTO:
                finalize(ty, a);
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
                        (A_LOAD(&v__(*allocs, i)->mark) & 1)
                     || (A_LOAD(&v__(*allocs, i)->hard) != 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        A_STORE(&v__(*allocs, i)->mark, A_LOAD(&v__(*allocs, i)->mark) & ~1);
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
                        !(A_LOAD(&a->mark) & 1)
                     && (A_LOAD(&a->hard) == 0)
                ) {
                        ty->memory_used -= min(a->size, ty->memory_used);
                        PROF_FREE(a);
                        collect(ty, a);
                        ty_free(a);
                } else {
                        A_STORE(&a->mark, A_LOAD(&a->mark) & ~1);
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
                        !(A_LOAD(&v__(*allocs, i)->mark) & 1)
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        finalize(ty, v__(*allocs, i));
                }
        }
        for (int i = 0; i < vN(*allocs); ++i) {
                if (
                        !(A_LOAD(&v__(*allocs, i)->mark) & 1)
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        PROF_FREE(v__(*allocs, i));
                        if (v__(*allocs, i)->type != GC_FFI_AUTO) {
                                collect(ty, v__(*allocs, i));
                        }
                        ty_free(v__(*allocs, i));
                } else {
                        A_STORE(&v__(*allocs, i)->mark, A_LOAD(&v__(*allocs, i)->mark) & ~1);
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
        TySpinLockLock(&ImmortalLock);
        xvP(ImmortalSet, *v);
        TySpinLockUnlock(&ImmortalLock);
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
