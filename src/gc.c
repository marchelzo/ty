#include <string.h>

#include "gc.h"
#include "dict.h"
#include "object.h"
#include "vm.h"
#include "log.h"
#include "token.h"
#include "class.h"
#include "tthread.h"
#include "compiler.h"
#include "itable.h"

static _Thread_local vec(Value const *) RootSet;
static vec(Value const *) ImmortalSet;

_Thread_local int GC_OFF_COUNT = 0;

#define A_LOAD(p)     atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x) atomic_store_explicit((p), (x), memory_order_relaxed)

inline static void
collect(Ty *ty, struct alloc *a)
{
        void *p = a->data;

        struct value o;
        struct value finalizer;
        struct regex *re;
        Thread *t;

        switch (a->type) {
        case GC_ARRAY:     mF(((struct array *)p)->items);    break;
        case GC_BLOB:      mF(((struct blob *)p)->items);     break;
        case GC_DICT:      dict_free(ty, p);                           break;
        case GC_GENERATOR:
                mF(((Generator *)p)->frame.items);
                mF(((Generator *)p)->calls.items);
                mF(((Generator *)p)->frames.items);
                mF(((Generator *)p)->targets.items);
                mF(((Generator *)p)->sps.items);
                mF(((Generator *)p)->deferred.items);
                mF(((Generator *)p)->to_drop.items);
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
                o = OBJECT((struct itable *)p, ((struct itable *)p)->class);
                finalizer = class_get_finalizer(ty, o.class);
                if (finalizer.type != VALUE_NONE) {
                        GCLOG("Calling finalizer for: %s", value_show(ty, &o));
                        vm_call_method(ty, &o, &finalizer, 0);
                }
                itable_release(ty, p);
                break;
        case GC_REGEX:
                re = p;
                pcre_free_study(re->extra);
                pcre_free(re->pcre);
                mF((char *)re->pattern);
                break;
        case GC_ARENA:
                source_forget_arena(p);
                break;
        }
}

void
GCForget(Ty *ty, AllocList *allocs, size_t *used)
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
GCSweep(Ty *ty, AllocList *allocs, size_t *used)
{
        size_t n = 0;

        for (int i = 0; i < allocs->count; ++i) {
                if (!A_LOAD(&allocs->items[i]->mark) && A_LOAD(&allocs->items[i]->hard) == 0) {
                        *used -= min(allocs->items[i]->size, *used);
                        collect(ty, allocs->items[i]);
                        free(allocs->items[i]);
                } else {
                        A_STORE(&allocs->items[i]->mark, false);
                        allocs->items[n++] = allocs->items[i];
                }
        }

        allocs->count = n;
}

void
GCTakeOwnership(Ty *ty, AllocList *new)
{
        for (size_t i = 0; i < new->count; ++i) {
                vec_nogc_push(ty->allocs, new->items[i]);
                MemoryUsed += new->items[i]->size;
        }
}

void
gc(Ty *ty)
{
        DoGC(ty);
}

void
gc_register(Ty *ty, void *p)
{
        vec_nogc_push(ty->allocs, ALLOC_OF(p));
}

void
_gc_push(Ty *ty, Value const *v)
{
        vec_nogc_push(RootSet, v);
}

void
gc_immortalize(Ty *ty, Value const *v)
{
        vec_nogc_push(ImmortalSet, v);
}

void
gc_pop(Ty *ty)
{
        --RootSet.count;
}

void
gc_remove(Ty *ty, struct value *v)
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
gc_clear_root_set(Ty *ty)
{
        RootSet.count = 0;
}

void
gc_truncate_root_set(Ty *ty, size_t n)
{
        RootSet.count = n;
}

size_t
gc_root_set_count(Ty *ty)
{
        return RootSet.count;
}

void *
GCRootSet(Ty *ty)
{
        return &RootSet;
}

void *
GCImmortalSet(Ty *ty)
{
        return &ImmortalSet;
}

/* vim: set sts=8 sw=8 expandtab: */
