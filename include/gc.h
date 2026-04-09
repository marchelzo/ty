#ifndef GC_H_INCLUDED
#define GC_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#include "polyfill_stdatomic.h"
#include "ty.h"
#include "vec.h"
#include "log.h"
#include "alloc.h"

void
DoGC(Ty *ty);

void
GCStepN(Ty *ty, int budget);

void
GCStartCycle(Ty *ty);

void
GCMarkRoots(Ty *ty);

int
GCMarkSome(Ty *ty, int n);

bool
GCSweepSome(Ty *ty, int n);

void
GCRunFullCycle(Ty *ty);

u64
TyThreadId(Ty *ty);

u64
RealThreadId(void);

bool
HoldingLock(Ty *ty);

#define GC_MARK_BUDGET  256
#define GC_SWEEP_BUDGET 512
#define GC_STEP_BYTES   512

#define AddAlloc(ty, a) do {  \
        xvP(ty->allocs, (a)); \
} while (0)

#if !defined(TY_RELEASE)
 #define GC_INITIAL_LIMIT (1ULL << 20)
#else
 #define GC_INITIAL_LIMIT (1ULL << 20)
#endif


#if defined(TY_GC_STATS)
#define AddToTotalBytes(n) TotalBytesAllocated += (n)
#else
#define AddToTotalBytes(n) 0
#endif


#define resize(ptr, n) ((ptr) = gc_resize(ty, (ptr), (n)))
#define resize_unchecked(ptr, n) ((ptr) = gc_resize_unchecked(ty, (ptr), (n)))
#define resize_nogc(ptr, n) ((ptr) = mrealloc((ptr), (n)))

#define RootSet (ty->st->gc_roots)

enum {
        GC_STRING,
        GC_ARRAY,
        GC_TUPLE,
        GC_OBJECT,
        GC_DICT,
        GC_BLOB,
        GC_QUEUE,
        GC_SHARED_QUEUE,
        GC_VALUE,
        GC_ENV,
        GC_GENERATOR,
        GC_THREAD,
        GC_REGEX,
        GC_ARENA,
        GC_FUN_INFO,
        GC_FFI_AUTO,
        GC_MUTEX,
        GC_SPINLOCK,
        GC_CONDVAR,
        GC_NOTE,
        GC_COUNTER,
        GC_CHANNEL,
        GC_ANY
};

void
gc(Ty *ty);

inline static void *
mrealloc(void *p, usize n);

inline static void *
gc_resize_unchecked(Ty *ty, void *p, usize n) {
        struct alloc *a;

        if (p != NULL) {
                a = ALLOC_OF(p);
                MemoryUsed -= a->size;
        } else {
                a = NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);

        a = ty_realloc(a, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;

        return a->data;
}

inline static int
IGCState(Ty *ty)
{
        return atomic_load_explicit(&ty->group->igc.State, memory_order_acquire);
}

inline static void
CheckUsed(Ty *ty, usize n)
{
        if (ty->GC_OFF_COUNT != 0) return;

        int state = IGCState(ty);

        if (UNLIKELY(state != GC_INACTIVE)) {
                ty->gc_step_credit += n;
                if (ty->gc_step_credit < GC_STEP_BYTES) return;
                isize heap = ty->gc_cycle_heap;
                isize headroom = ty->gc_cycle_limit - MemoryUsed;
                int budget;
                if (headroom <= 0) {
                        budget = 65536;
                } else if (headroom < MemoryUsed) {
                        budget = (int)((heap * ty->gc_step_credit) / headroom);
                        if (budget < 64) budget = 64;
                        if (budget > 65536) budget = 65536;
                } else {
                        budget = (int)(ty->gc_step_credit);
                        if (budget < 16) budget = 16;
                }
                ty->gc_step_credit = 0;
                GC_STOP();
                GCStepN(ty, budget);
                GC_RESUME();
                return;
        }

#if defined(TY_RELEASE)
        if (UNLIKELY(MemoryUsed >= MemoryLimit)) {
#else
        if (MemoryUsed >= MemoryLimit || GC_EVERY_ALLOC) {
#endif
                GC_STOP();
                GCStartCycle(ty);
                GCStepN(ty, GC_MARK_BUDGET);
                GC_RESUME();
        }
}

inline static void *
gc_alloc(Ty *ty, usize n)
{
        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty, n);

        struct alloc *a = ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->color, GC_WHITE);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static void *
gc_alloc0(Ty *ty, usize n)
{
        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty, n);

        struct alloc *a = ty_calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;

        return a->data;
}

inline static void *
gc_alloc_unchecked(Ty *ty, usize n)
{
        MemoryUsed += n;
        AddToTotalBytes(n);

        struct alloc *a = ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->color, GC_WHITE);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static void *
gc_alloc0_unchecked(Ty *ty, usize n)
{
        MemoryUsed += n;
        AddToTotalBytes(n);

        struct alloc *a = ty_calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;

        return a->data;
}

#define GC_BIRTH_COLOR(ty) (IGCState(ty) != GC_INACTIVE ? GC_BLACK : GC_WHITE)

inline static void *
gc_alloc_object(Ty *ty, usize n, char type)
{
        if (n == 0) {
                return NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty, n);

        struct alloc *a = ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->color, GC_BIRTH_COLOR(ty));
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        AddAlloc(ty, a);

        return a->data;
}

inline static void *
gc_alloc_object_unchecked(Ty *ty, usize n, char type)
{
        if (n == 0) {
                return NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);

        struct alloc *a = ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->color, GC_BIRTH_COLOR(ty));
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        AddAlloc(ty, a);

        return a->data;
}

inline static void *
gc_alloc_object0(Ty *ty, usize n, char type)
{
        if (n == 0) {
                return NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty, n);

        struct alloc *a = ty_calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->color, GC_BIRTH_COLOR(ty));
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        AddAlloc(ty, a);

        return a->data;
}

inline static void *
gc_alloc_object0_unchecked(Ty *ty, usize n, char type)
{
        if (n == 0) {
                return NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);

        struct alloc *a = ty_calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->color, GC_BIRTH_COLOR(ty));
        atomic_init(&a->hard, 0);

        a->type = type;
        a->size = n;

        AddAlloc(ty, a);

        return a->data;
}

void
gc_register(Ty *ty, void *p);

void
gc_shade_value(Ty *ty, Value const *v);

void
gc_immortalize(Ty *ty, Value const *v);

void
gc_clear_root_set(Ty *ty);

void
gc_truncate_root_set(Ty *ty, usize n);

usize
gc_root_set_count(Ty *ty);

void
gc_notify(Ty *ty, usize n);

inline static void
gc_free(Ty *ty, void *p)
{
        if (p != NULL) {
                struct alloc *a = ALLOC_OF(p);
                if (a->size >= MemoryUsed) {
                        MemoryUsed = 0;
                } else {
                        MemoryUsed -= a->size;
                }
                ty_free(a);
        }
}

inline static void *
gc_resize(Ty *ty, void *p, usize n) {
        struct alloc *a;

        if (p != NULL) {
                a = ALLOC_OF(p);
                if (a->size >= MemoryUsed) {
                        MemoryUsed = 0;
                } else {
                        MemoryUsed -= a->size;
                }
        } else {
                a = NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);

        CheckUsed(ty, n);

        a = ty_realloc(a, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;

        return a->data;
}

inline static void *
gc_alloc_unregistered(Ty *ty, usize n, char type)
{
        void *p = mA(n);
        ALLOC_OF(p)->type = type;
        return p;
}

void
GCMark(Ty *ty);

void
GCSweepTy(Ty *ty);

void
GCSweep(Ty *ty, AllocList *allocs, isize *used);

void
GCForget(Ty *ty, AllocList *allocs, isize *used);

void
GCForgetObject(Ty *ty, void const *o);

void
GCTakeOwnership(Ty *ty, AllocList *new);

GCRootSet *
GCRoots(Ty *ty);

void *
GCImmortalSet(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
