#include <string.h>

#include "value.h"
#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"
#include "token.h"
#include "class.h"
#include "tthread.h"

_Thread_local AllocList allocs;
_Thread_local size_t MemoryUsed = 0;
_Thread_local size_t MemoryLimit = GC_INITIAL_LIMIT;

static _Thread_local vec(struct value const *) RootSet;

_Thread_local int GC_OFF_COUNT = 0;

#define A_LOAD(p)     atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x) atomic_store_explicit((p), (x), memory_order_relaxed)

inline static void
collect(struct alloc *a)
{
        void *p = a->data;

        struct value o;
        struct value finalizer;
        struct regex *re;
        Thread *t;

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
                t = p;
                if (t->v.type == VALUE_NONE) {
                        TyThreadDetach(((Thread *)p)->t);
                }
                TyMutexDestroy(&t->mutex);
                TyCondVarDestroy(&t->cond);
                break;
        case GC_OBJECT:
                o = OBJECT((struct table *)p, ((struct table *)p)->class);
                finalizer = class_get_finalizer(o.class);
                if (finalizer.type != VALUE_NONE) {
                        GCLOG("Calling finalizer for: %s", value_show(&o));
                        vm_call_method(&o, &finalizer, 0);
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
GCForget(AllocList *allocs, size_t *used)
{
        size_t n = 0;

        for (size_t i = 0; i < allocs->count;) {
                if (allocs->items[i] == NULL) {
                        abort();
                }
                if (!A_LOAD(&allocs->items[i]->mark) && A_LOAD(&allocs->items[i]->hard) == 0) {
                        allocs->items[n++] = allocs->items[i++];
                } else {
                        *used -= min(allocs->items[i]->size, *used);
                        SWAP(struct alloc *, allocs->items[i], allocs->items[allocs->count - 1]);
                        allocs->count -= 1;
                }
        }
}

void
GCSweep(AllocList *allocs, size_t *used)
{
        size_t n = 0;

        for (int i = 0; i < allocs->count; ++i) {
                if (!A_LOAD(&allocs->items[i]->mark) && A_LOAD(&allocs->items[i]->hard) == 0) {
                        *used -= min(allocs->items[i]->size, *used);
                        collect(allocs->items[i]);
                        free(allocs->items[i]);
                } else {
                        A_STORE(&allocs->items[i]->mark, false);
                        allocs->items[n++] = allocs->items[i];
                }
        }

        allocs->count = n;
}

void
GCTakeOwnership(AllocList *new)
{
        for (size_t i = 0; i < new->count; ++i) {
                vec_nogc_push(allocs, new->items[i]);
                MemoryUsed += new->items[i]->size;
        }
}

void
gc(void)
{
        DoGC();
}

void
gc_register(void *p)
{
        vec_nogc_push(allocs, ALLOC_OF(p));
}

void
_gc_push(struct value *v)
{
        vec_nogc_push(RootSet, v);
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

/* vim: set sts=8 sw=8 expandtab: */
