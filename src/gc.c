#include <string.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"

size_t allocated = 0;
alloc_list allocs;
static vec(struct value *) root_set;

bool GC_ENABLED = true;

inline static void
collect(struct alloc *a)
{
        void *p = a->data;

        switch (a->type) {
        case GC_ARRAY:   free(((struct array *)p)->items); break;
        case GC_BLOB:    free(((struct blob *)p)->items);  break;
        case GC_DICT:    dict_free(p);                     break;
        case GC_OBJECT:  table_release(p);                 break;
        }
}

void
gc(void)
{
        vm_mark();

        for (int i = 0; i < root_set.count; ++i)
                value_mark(root_set.items[i]);

        int n = 0;
        for (int i = 0; i < allocs.count; ++i) {
                if (allocs.items[i]->mark == GC_NONE) {
                        collect(allocs.items[i]);
                        free(allocs.items[i]);
                } else {
                        allocs.items[i]->mark &= ~GC_MARK;
                        allocs.items[n++] = allocs.items[i];
                }
        }

        allocs.count = n;
        allocated = 0;
}

void *
gc_alloc(size_t n)
{
        void *mem = alloc(n);

        allocated += n;

        if (allocated > GC_THRESHOLD)
                gc();

        return mem;
}

void
gc_notify(size_t n)
{
        allocated += n;
}

void
gc_register(void *p)
{
        vec_push(allocs, ALLOC_OF(p));
}

void
_gc_push(struct value *v)
{
        vec_push(root_set, v);
}

void
gc_pop(void)
{
        --root_set.count;
}

void
gc_remove(struct value *v)
{
        for (int i = 0; i < root_set.count; ++i) {
                if (root_set.items[i] == v) {
                        int j = root_set.count - 1;
                        root_set.items[i] = root_set.items[j];
                        --root_set.count;
                }
        }
}

void
gc_clear_root_set(void)
{
        root_set.count = 0;
}

void
gc_truncate_root_set(size_t n)
{
        root_set.count = n;
}

size_t
gc_root_set_count(void)
{
        return root_set.count;
}
