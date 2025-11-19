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

typedef struct value Value;

void
DoGC(Ty *ty);

uint64_t
MyThreadId(Ty *ty);


#define GC_INITIAL_LIMIT (1ULL << 22)


#if defined(TY_GC_STATS)
#define AddToTotalBytes(n) TotalBytesAllocated += (n)
#else
#define AddToTotalBytes(n) 0
#endif


#define resize(ptr, n) ((ptr) = gc_resize(ty, (ptr), (n)))
#define resize_unchecked(ptr, n) ((ptr) = gc_resize_unchecked(ty, (ptr), (n)))
#define resize_nogc(ptr, n) ((ptr) = mrealloc((ptr), (n)))

#define RootSet (ty->gc_roots)

enum {
        GC_STRING,
        GC_ARRAY,
        GC_TUPLE,
        GC_OBJECT,
        GC_DICT,
        GC_BLOB,
        GC_VALUE,
        GC_ENV,
        GC_GENERATOR,
        GC_THREAD,
        GC_REGEX,
        GC_ARENA,
        GC_FUN_INFO,
        GC_FFI_AUTO,
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

        a = realloc(a, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;

        return a->data;
}

inline static void
CheckUsed(Ty *ty)
{
        if (UNLIKELY(
                (ty->GC_OFF_COUNT == 0)
             && (MemoryUsed >= MemoryLimit)
        )) {
                GCLOG("Running GC. Used = %zu MB, Limit = %zu MB", MemoryUsed / 1000000, MemoryLimit / 1000000);
                DoGC(ty);
                GCLOG("DoGC() returned: %zu MB still in use", MemoryUsed / 1000000);
                while (MemoryUsed >= MemoryLimit) {
                        MemoryLimit <<= 1;
                }
                GCLOG("Increasing memory limit to %zu MB", MemoryLimit / 1000000);
        }
}

inline static void *
gc_alloc(Ty *ty, usize n)
{
        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty);

        struct alloc *a = malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->mark, false);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static void *
gc_alloc0(Ty *ty, usize n)
{
        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty);

        struct alloc *a = calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;

        return a->data;
}

inline static void *
gc_alloc_object(Ty *ty, usize n, char type)
{
        if (n == 0) {
                return NULL;
        }

        MemoryUsed += n;
        AddToTotalBytes(n);
        CheckUsed(ty);

        struct alloc *a = malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->mark, false);
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        xvP(ty->allocs, a);

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

        struct alloc *a = malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->mark, false);
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        xvP(ty->allocs, a);

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
        CheckUsed(ty);

        struct alloc *a = calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->type = type;
        a->size = n;

        xvP(ty->allocs, a);

        return a->data;
}

void
gc_register(Ty *ty, void *p);

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
                free(a);
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

        CheckUsed(ty);

        a = realloc(a, sizeof *a + n);
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
GCSweepOwn(Ty *ty);

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
