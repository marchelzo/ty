#include <string.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"

#define GC_ALLOC_THRESHOLD (1ULL << 24)

static size_t allocated = 0;
static vec(struct value *) root_set;
static vec(struct alloc *) allocs;

inline static void
collect(struct alloc *a)
{
        void *p = a->data;

        switch (a->type) {
        case GC_ARRAY:   free(((struct array *)p)->items); break;
        case GC_BLOB:    free(((struct blob *)p)->items);  break;
        case GC_DICT:    dict_free(p);                     break;
        case GC_OBJECT:  object_free(p);                   break;
        }

        free(a);
}

inline static void
gc(void)
{
        vm_mark();

        for (int i = 0; i < root_set.count; ++i)
                value_mark(root_set.items[i]);

        int len = 0;
        for (int i = 0; i < allocs.count; ++i) {
                if (allocs.items[i]->mark == GC_NONE) {
                        collect(allocs.items[i]);
                } else {
                        allocs.items[i]->mark &= ~GC_MARK;
                        allocs.items[len++] = allocs.items[i];
                }
        }

        allocs.count = len;
        allocated = 0;
}

void *
gc_alloc(size_t n)
{
        void *mem = alloc(n);

        allocated += n;

        if (allocated > GC_ALLOC_THRESHOLD)
                gc();

        return mem;
}

void *
gc_alloc_object(size_t n, char type)
{
        struct alloc *a = alloc(sizeof *a + n);

        allocated += n;

        a->mark = GC_NONE;
        a->type = type;

        if (allocated > GC_ALLOC_THRESHOLD)
                gc();

        vec_push(allocs, a);

        return a->data;
}

void
gc_register(void *p)
{
        vec_push(allocs, ALLOC_OF(p));
}

void
gc_push(struct value *v)
{
        vec_push(root_set, v);
}

void
gc_pop(void)
{
        --root_set.count;
}

void
gc_clear_root_set(void)
{
        root_set.count = 0;
}
