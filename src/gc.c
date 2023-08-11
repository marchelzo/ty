#include <string.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"
#include "token.h"

_Thread_local AllocList allocs;
_Thread_local size_t MemoryUsed = 0;
_Thread_local size_t MemoryLimit = GC_INITIAL_LIMIT;

static _Thread_local vec(struct value const *) RootSet;

_Thread_local int GC_OFF_COUNT = 0;

inline static void
collect(struct alloc *a)
{
        void *p = a->data;

        struct value *finalizer;
        struct regex *re;

        switch (a->type) {
        case GC_ARRAY:     gc_free(((struct array *)p)->items);    break;
        case GC_BLOB:      gc_free(((struct blob *)p)->items);     break;
        case GC_DICT:      dict_free(p);                           break;
        case GC_GENERATOR:
                gc_free(((Generator *)p)->frame.items);
                gc_free(((Generator *)p)->calls.items);
                gc_free(((Generator *)p)->frames.items);
                gc_free(((Generator *)p)->targets.items);
                gc_free(((Generator *)p)->sps.items);
                break;
        case GC_THREAD:
                pthread_detach(((Thread *)p)->t);
                break;
        case GC_OBJECT:
                finalizer = &((struct table *)p)->finalizer;
                if (finalizer->type != VALUE_NIL) {
                        GCLOG("Calling finalizer %p", (void *)finalizer);
                        vm_call(finalizer, 0);
                }
                table_release(p);
                break;
        case GC_REGEX:
                re = p;
                pcre_free_study(re->extra);
                pcre_free(re->pcre);
                gc_free((char *)re->pattern);
                break;
        }
}

void
GCMark(void)
{
        vm_mark();

        for (int i = 0; i < RootSet.count; ++i) {
                value_mark(RootSet.items[i]);
        }

        for (int i = 0; i < allocs.count; ++i) {
                if (allocs.items[i]->mark == GC_NONE && allocs.items[i]->type == GC_OBJECT) {
                        value_mark(&((struct table *)allocs.items[i]->data)->finalizer);
                }
        }
}

void
GCSweep(AllocList *allocs, size_t *used)
{
        int n = 0;
        for (int i = 0; i < allocs->count; ++i) {
                if (!atomic_load(&allocs->items[i]->mark) && atomic_load(&allocs->items[i]->hard) == 0) {
                        *used -= min(allocs->items[i]->size, *used);
                        collect(allocs->items[i]);
                        free(allocs->items[i]);
                } else {
                        atomic_store(&allocs->items[i]->mark, false);
                        allocs->items[n++] = allocs->items[i];
                }
        }

        allocs->count = n;
}

void
gc(void)
{
        DoGC();
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

void *GCRootSet(void)
{
        return &RootSet;
}
