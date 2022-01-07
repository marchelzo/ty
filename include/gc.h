#ifndef GC_H_INCLUDED
#define GC_H_INCLUDED

#include <stddef.h>
#include <stdint.h>

#include "vec.h"
#include "log.h"
#include "alloc.h"
#include "value.h"

#define ALLOC_OF(p) ((struct alloc *)(((char *)(p)) - offsetof(struct alloc, data)))

#define resize(ptr, n) ((ptr) = gc_resize((ptr), (n)))

#define MARKED(v) ((ALLOC_OF(v))->mark & GC_MARK)
#define MARK(v)   ((ALLOC_OF(v))->mark |= GC_MARK)
#define UNMARK(v) ((ALLOC_OF(v))->mark &= ~GC_MARK)
#define NOGC(v)   ((ALLOC_OF(v))->mark |= GC_HARD)
#define OKGC(v)   ((ALLOC_OF(v))->mark &= ~GC_HARD)

#define GC_INITIAL_LIMIT (1ULL << 18)

typedef vec(struct alloc *) AllocList;

extern AllocList allocs;
extern bool GC_ENABLED;

extern size_t MemoryUsed;
extern size_t MemoryLimit;

struct alloc {
        union {
                struct {
                        char type;
                        char mark;
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
        GC_ANY
};

enum {
        GC_NONE = 1 << 0,
        GC_MARK = 1 << 1,
        GC_HARD = 1 << 2,
};

void
gc(void);

inline static void
CheckUsed(void)
{
        if (GC_ENABLED && MemoryUsed > MemoryLimit) {
                gc();
                LOG("gc() returned: %zu MB still in use", MemoryUsed / 1000000);
                while ((MemoryUsed << 1) > MemoryLimit) {
                        MemoryLimit <<= 1;
                        LOG("Increasing memory limit to %zu MB", MemoryLimit / 1000000);
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
        a->mark = GC_HARD;
        a->type = GC_ANY;

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

        a->mark = GC_NONE;
        a->type = type;
        a->size = n;

        vec_push(allocs, a);

        return a->data;
}

void
gc_register(void *p);

void
_gc_push(struct value *v);

#define gc_push(v) do { LOG("gc_push: " __FILE__ ":%d: %p", __LINE__, (v)); _gc_push(v); } while (0);

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
                MemoryUsed -= a->size;
                free(a);
        }
}

inline static void *
gc_resize(void *p, size_t n) {
        struct alloc *a;

        if (p != NULL) {
                a = ALLOC_OF(p);
                MemoryUsed -= a->size;
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

inline static void
gc_disable(void)
{
        GC_ENABLED = false;
}

inline static void
gc_enable(void)
{
        GC_ENABLED = true;
}

#endif
