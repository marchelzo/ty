#include <string.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"

_Thread_local AllocList allocs;

_Thread_local size_t MemoryUsed = 0;
_Thread_local size_t MemoryLimit = GC_INITIAL_LIMIT;

static _Thread_local vec(struct value const *) RootSet;

_Thread_local bool GC_ENABLED = true;

inline static void
collect(struct alloc *a)
{
        void *p = a->data;
        struct value *finalizer;

        switch (a->type) {
        case GC_ARRAY:     gc_free(((struct array *)p)->items);    break;
        case GC_BLOB:      gc_free(((struct blob *)p)->items);     break;
        case GC_DICT:      dict_free(p);                           break;
        case GC_GENERATOR: gc_free(((Generator *)p)->frame.items); break;
        case GC_OBJECT:
                finalizer = &((struct table *)p)->finalizer;
                if (finalizer->type != VALUE_NIL) {
                        vm_call(finalizer, 0);
                }
                table_release(p);
                break;
        }
}

void
gc(void)
{
        if (!GC_ENABLED) {
                return;
        }

        LOG("Running GC. Used = %zu MB, Limit = %zu MB", MemoryUsed / 1000000, MemoryLimit / 1000000);

        GC_ENABLED = false;

        vm_mark();

        for (int i = 0; i < RootSet.count; ++i)
                value_mark(RootSet.items[i]);

        for (int i = 0; i < allocs.count; ++i) {
                if (allocs.items[i]->mark == GC_NONE && allocs.items[i]->type == GC_OBJECT) {
                        value_mark(&((struct table *)allocs.items[i]->data)->finalizer);
                }
        }

        int n = 0;
        for (int i = 0; i < allocs.count; ++i) {
                if (allocs.items[i]->mark == GC_NONE) {
                        MemoryUsed -= allocs.items[i]->size;
                        collect(allocs.items[i]);
                        free(allocs.items[i]);
                } else {
                        allocs.items[i]->mark &= ~GC_MARK;
                        allocs.items[n++] = allocs.items[i];
                }
        }

        allocs.count = n;

        GC_ENABLED = true;
}

void
gc_register(void *p)
{
        vec_push(allocs, ALLOC_OF(p));
}

void
_gc_push(struct value *v)
{
        vec_push_unchecked(RootSet, v);
}

void
gc_pop(void)
{
        --RootSet.count;
}

void
gc_remove(struct value *v)
{
        for (int i = 0; i < RootSet.count; ++i) {
                if (RootSet.items[i] == v) {
                        int j = RootSet.count - 1;
                        RootSet.items[i] = RootSet.items[j];
                        --RootSet.count;
                }
        }
}

void
gc_clear_root_set(void)
{
        RootSet.count = 0;
}

void
gc_truncate_root_set(size_t n)
{
        RootSet.count = n;
}

size_t
gc_root_set_count(void)
{
        return RootSet.count;
}
