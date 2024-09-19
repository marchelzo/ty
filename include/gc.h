#ifndef GC_H_INCLUDED
#define GC_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#include "polyfill_stdatomic.h"
#include "vec.h"
#include "log.h"
#include "alloc.h"

typedef struct value Value;

void
DoGC(Ty *ty);

uint64_t
MyThreadId(Ty *ty);

#define ALLOC_OF(p) ((struct alloc *)(((char *)(p)) - offsetof(struct alloc, data)))

#define resize(ptr, n) ((ptr) = gc_resize(ty, (ptr), (n)))
#define resize_unchecked(ptr, n) ((ptr) = gc_resize_unchecked(ty, (ptr), (n)))
#define resize_nogc(ptr, n) ((ptr) = mrealloc((ptr), (n)))

//#define MARKED(v) ((ALLOC_OF(v))->mark & GC_MARK)
//#define MARK(v)   ((ALLOC_OF(v))->mark |= GC_MARK)
//#define UNMARK(v) ((ALLOC_OF(v))->mark &= ~GC_MARK)

#define MARKED(v) atomic_load_explicit(&(ALLOC_OF(v))->mark, memory_order_relaxed)
#define MARK(v)   atomic_store_explicit(&(ALLOC_OF(v))->mark, true, memory_order_relaxed)

#define NOGC(v)   atomic_fetch_add_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)
#define OKGC(v)   atomic_fetch_sub_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)

#define GC_INITIAL_LIMIT (1ULL << 22)

struct alloc {
        union {
                struct {
                        char type;
                        atomic_bool mark;
                        atomic_uint_least16_t hard;
                        uint32_t size;
                };
                void const * restrict padding;
        };
        char data[];
};

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
        GC_ANY
};

void
gc(Ty *ty);

inline static void *
mrealloc(void *p, size_t n);

inline static void *
gc_resize_unchecked(Ty *ty, void *p, size_t n) {
        struct alloc *a;

        if (p != NULL) {
                a = ALLOC_OF(p);
                MemoryUsed -= a->size;
        } else {
                a = NULL;
        }

        MemoryUsed += n;

        a = realloc(a, sizeof *a + n);
        if (a == NULL) {
                panic("Out of memory!");
        }

        a->size = n;

        return a->data;
}


inline static void
CheckUsed(Ty *ty)
{
        if (
                ty->GC_OFF_COUNT == 0
#if 1
                && MemoryUsed > MemoryLimit
#endif
        ) {
                GCLOG("Running GC. Used = %zu MB, Limit = %zu MB", MemoryUsed / 1000000, MemoryLimit / 1000000);
                DoGC(ty);
                GCLOG("DoGC(ty) returned: %zu MB still in use", MemoryUsed / 1000000);
                while (MemoryUsed >= MemoryLimit) {
                        MemoryLimit <<= 1;
                        GCLOG("Increasing memory limit to %zu MB", MemoryLimit / 1000000);
                }
        }
}

inline static void *
gc_alloc(Ty *ty, size_t n)
{
        MemoryUsed += n;
        CheckUsed(ty);

        struct alloc *a = malloc(sizeof *a + n);
        if (a == NULL) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->mark, false);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static void *
gc_alloc_object(Ty *ty, size_t n, char type)
{
        if (n == 0)
                return NULL;

        MemoryUsed += n;
        CheckUsed(ty);

        struct alloc *a = malloc(sizeof *a + n);
        if (a == NULL) {
                panic("Out of memory!");
        }

        atomic_init(&a->mark, false);
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        xvP(ty->allocs, a);

        return a->data;
}

void
gc_register(Ty *ty, void *p);

void
_gc_push(Ty *ty, Value const *v);

void
gc_immortalize(Ty *ty, Value const *v);

#if 0
#define gc_push(ty, v) do { GCLOG("gc_push(ty): " __FILE__ ":%d: %p", __LINE__, (v)); _gc_push(v); } while (0)
#else
#define gc_push _gc_push
#endif

void
gc_pop(Ty *ty);

void
gc_clear_root_set(Ty *ty);

void
gc_truncate_root_set(Ty *ty, size_t n);

size_t
gc_root_set_count(Ty *ty);

void
gc_notify(Ty *ty, size_t n);

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
mrealloc(void *p, size_t n)
{
        p = realloc(p, n);

        if (p == NULL) {
                panic("Out of memory!");
        }

        return p;
}

inline static void *
gc_resize(Ty *ty, void *p, size_t n) {
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

        CheckUsed(ty);

        a = realloc(a, sizeof *a + n);
        if (a == NULL) {
                panic("Out of memory!");
        }

        a->size = n;

        return a->data;
}

inline static void *
gc_alloc_unregistered(Ty *ty, size_t n, char type)
{
        void *p = mA(n);
        ALLOC_OF(p)->type = type;
        return p;
}

void
GCMark(Ty *ty);

void
GCSweep(Ty *ty, AllocList *allocs, size_t *used);

void
GCForget(Ty *ty, AllocList *allocs, size_t *used);

void
GCTakeOwnership(Ty *ty, AllocList *new);

void *
GCRootSet(Ty *ty);

void *
GCImmortalSet(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
