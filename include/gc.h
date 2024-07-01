#ifndef GC_H_INCLUDED
#define GC_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <pthread.h>

#include "polyfill_stdatomic.h"
#include "vec.h"
#include "log.h"
#include "alloc.h"
#include "value.h"

void DoGC(void);

#define ALLOC_OF(p) ((struct alloc *)(((char *)(p)) - offsetof(struct alloc, data)))

#define resize(ptr, n) ((ptr) = gc_resize((ptr), (n)))
#define resize_unchecked(ptr, n) ((ptr) = gc_resize_unchecked((ptr), (n)))
#define resize_nogc(ptr, n) ((ptr) = mrealloc((ptr), (n)))

//#define MARKED(v) ((ALLOC_OF(v))->mark & GC_MARK)
//#define MARK(v)   ((ALLOC_OF(v))->mark |= GC_MARK)
//#define UNMARK(v) ((ALLOC_OF(v))->mark &= ~GC_MARK)

#define MARKED(v) atomic_load_explicit(&(ALLOC_OF(v))->mark, memory_order_relaxed)
#define MARK(v)   atomic_store_explicit(&(ALLOC_OF(v))->mark, true, memory_order_relaxed)

#define NOGC(v)   atomic_fetch_add_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)
#define OKGC(v)   atomic_fetch_sub_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)

#define GC_INITIAL_LIMIT (1ULL << 22)

typedef vec(struct alloc *) AllocList;

extern _Thread_local AllocList allocs;
extern _Thread_local int GC_OFF_COUNT;

extern _Thread_local size_t MemoryUsed;
extern _Thread_local size_t MemoryLimit;

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
        GC_ANY
};

void
gc(void);

inline static void *
mrealloc(void *p, size_t n);

inline static void *
gc_resize_unchecked(void *p, size_t n) {
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
CheckUsed(void)
{
        if (
                GC_OFF_COUNT == 0
#ifdef TY_RELEASE
                && MemoryUsed > MemoryLimit
#endif
        ) {
                GCLOG("Running GC. Used = %zu MB, Limit = %zu MB", MemoryUsed / 1000000, MemoryLimit / 1000000);
                DoGC();
                GCLOG("DoGC() returned: %zu MB still in use", MemoryUsed / 1000000);
                while (MemoryUsed >= MemoryLimit) {
                        MemoryLimit <<= 1;
                        GCLOG("Increasing memory limit to %zu MB", MemoryLimit / 1000000);
                }
        }
}

inline static void *
gc_alloc(size_t n)
{
        MemoryUsed += n;
        CheckUsed();

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
gc_alloc_object(size_t n, char type)
{
        if (n == 0)
                return NULL;

        MemoryUsed += n;
        CheckUsed();

        struct alloc *a = malloc(sizeof *a + n);
        if (a == NULL) {
                panic("Out of memory!");
        }

        atomic_init(&a->mark, false);
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        vec_nogc_push(allocs, a);

        return a->data;
}

void
gc_register(void *p);

void
_gc_push(struct value *v);

#if 0
#define gc_push(v) do { LOG("gc_push: " __FILE__ ":%d: %p", __LINE__, (v)); _gc_push(v); } while (0);
#else
#define gc_push _gc_push
#endif

void
gc_pop(void);

void
gc_clear_root_set(void);

void
gc_truncate_root_set(size_t n);

size_t
gc_root_set_count(void);

void
gc_notify(size_t n);

inline static void
gc_free(void *p)
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
gc_resize(void *p, size_t n) {
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

        CheckUsed();

        a = realloc(a, sizeof *a + n);
        if (a == NULL) {
                panic("Out of memory!");
        }

        a->size = n;

        return a->data;
}

inline static void *
gc_alloc_unregistered(size_t n, char type)
{
        void *p = gc_alloc(n);
        ALLOC_OF(p)->type = type;
        return p;
}

void GCMark(void);
void GCSweep(AllocList *allocs, size_t *used);
void GCForget(AllocList *allocs, size_t *used);
void GCTakeOwnership(AllocList *new);

void *GCRootSet(void);

#endif

/* vim: set sts=8 sw=8 expandtab: */
