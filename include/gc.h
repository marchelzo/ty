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
#include "prof.h"

void
DoGC(Ty *ty);

u64
TyThreadId(Ty *ty);

u64
RealThreadId(void);

bool
HoldingLock(Ty *ty);

#define GC_SPECIAL ( (1ULL << GC_GENERATOR)     \
                   | (1ULL << GC_THREAD)        \
                   | (1ULL << GC_REGEX)         \
                   | (1ULL << GC_ARENA)         \
                   | (1ULL << GC_FUN_INFO)      \
                   | (1ULL << GC_JIT_CODE)      \
                   | (1ULL << GC_LIR)           \
                   | (1ULL << GC_FFI_AUTO)      \
                   | (1ULL << GC_MUTEX)         \
                   | (1ULL << GC_SPINLOCK)      \
                   | (1ULL << GC_CONDVAR)       \
                   | (1ULL << GC_NOTE)          \
                   | (1ULL << GC_COUNTER)       \
                   | (1ULL << GC_CHANNEL)       \
                   | (1ULL << GC_SCREEN)        \
                   | (1ULL << GC_SHARED_QUEUE)  )

#define AddAlloc(ty, a) do {                            \
        if (UNLIKELY((GC_SPECIAL >> (a)->type) & 1)) {  \
                if ((a)->type == GC_FFI_AUTO) {         \
                        xvP((ty)->ffi_autos, (a));      \
                }                                       \
                xvP((ty)->special, (a));                \
        } else {                                        \
                xvP((ty)->allocs, (a));                 \
        }                                               \
} while (0)

#if !defined(TY_RELEASE)
 #define GC_INITIAL_LIMIT (1ULL << 22)
#else
 #define GC_INITIAL_LIMIT (1ULL << 22)
#endif

#define GC_NURSERY_MAX ((isize)1 << 26)
#define GC_MINOR_MIN   ((isize)1 << 24)
#define GC_MARK_DEEP   2048


#if defined(TY_GC_STATS)
#define AddToTotalBytes(n) TotalBytesAllocated += (n)
#else
#define AddToTotalBytes(n) 0
#endif

#define NoteAlloc(n, type) do {                                   \
        AddToTotalBytes(n);                                       \
        PROF_ALLOC(ty, (n), (type));                              \
        TY_PROBE_IF(alloc, (unsigned long)(n), (int)(type));      \
} while (0)


#define resize(ptr, n) ((ptr) = gc_resize(ty, (ptr), (n)))
#define resize_unchecked(ptr, n) ((ptr) = gc_resize_unchecked(ty, (ptr), (n)))
#define resize_nogc(ptr, n) ((ptr) = mrealloc((ptr), (n)))

#define RootSet (ty->st->gc_roots)

enum {
        GC_STRING,
        GC_ARRAY,
        GC_TUPLE,
        GC_OBJECT,
        GC_DICT,
        GC_SET,
        GC_HEAP,
        GC_BLOB,
        GC_QUEUE,
        GC_SHARED_QUEUE,
        GC_VALUE,
        GC_ENV,
        GC_GENERATOR,
        GC_THREAD,
        GC_REGEX,
        GC_ARENA,
        GC_FUN_INFO,
        GC_JIT_CODE,
        GC_LIR,
        GC_FFI_AUTO,
        GC_MUTEX,
        GC_SPINLOCK,
        GC_CONDVAR,
        GC_NOTE,
        GC_COUNTER,
        GC_CHANNEL,
        GC_SCREEN,
        GC_BUF_VALUES,
        GC_BUF_BYTES,
        GC_BUF_DICT,
        GC_BUF_SET,
        GC_IDS,
        GC_ANY
};

void
gc(Ty *ty);

inline static void *
mrealloc(void *p, usize n);

void
GCRepin(Ty *ty, Alloc const *old, Alloc *new);

void
GCBlockDrop(Ty *ty, Alloc *a);

bool
GCBlockLive(Ty *ty, Alloc const *a);

inline static void *
gc_resize_unchecked(Ty *ty, void *p, usize n) {
        Alloc *a;

        if (UNLIKELY(p != NULL && InGCBlocks(ALLOC_OF(p)))) {
                void *q = gc_resize_unchecked(ty, NULL, n);
                memcpy(q, p, min(ALLOC_OF(p)->size, n));
                GCBlockDrop(ty, ALLOC_OF(p));
                return q;
        }

        if (p != NULL) {
                a = ALLOC_OF(p);
                MemoryUsed -= a->size;
        } else {
                a = NULL;
        }

        MemoryUsed += n;
        NoteAlloc(
                (a != NULL && a->size < n) ? (n - a->size)
              : (a == NULL)                ? n
              :                              0,
                (a != NULL) ? a->type : GC_ANY
        );

        Alloc *old = a;

        a = ty_realloc(a, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;

        if (old == NULL) {
                a->type = GC_ANY;
                atomic_init(&a->mark, ty->gc_owner);
                atomic_init(&a->hard, 0);
        } else if (UNLIKELY(a != old && atomic_load_explicit(&a->hard, memory_order_relaxed) != 0)) {
                GCRepin(ty, old, a);
        }

        return a->data;
}

void
GCCollect(Ty *ty);


void
GCDefer(Ty *ty);

inline static void
CheckUsed(Ty *ty)
{
#if defined(TY_RELEASE)
        if (UNLIKELY(MemoryUsed >= MemoryLimit)) {
#else
        if (MemoryUsed >= MemoryLimit || GC_EVERY_ALLOC) {
#endif
                if (ty->GC_OFF_COUNT == 0) {
                        GCCollect(ty);
                } else {
                        GCDefer(ty);
                }
        }
}

inline static void
CheckDeferredGC(Ty *ty)
{
        if (UNLIKELY(ty->gc_deferred) && (ty->GC_OFF_COUNT == 0)) {
                ty->gc_deferred = false;
                if (MemoryUsed >= MemoryLimit) {
                        GCCollect(ty);
                }
        }
}

inline static void *
gc_alloc(Ty *ty, usize n)
{
        MemoryUsed += n;
        NoteAlloc(n, GC_ANY);
        CheckUsed(ty);

        Alloc *a = ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->mark, ty->gc_owner);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static void *
gc_alloc0(Ty *ty, usize n)
{
        MemoryUsed += n;
        NoteAlloc(n, GC_ANY);
        CheckUsed(ty);

        Alloc *a = ty_calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->mark, ty->gc_owner);

        return a->data;
}

inline static void *
gc_alloc_unchecked(Ty *ty, usize n)
{
        MemoryUsed += n;
        NoteAlloc(n, GC_ANY);

        Alloc *a = ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->mark, ty->gc_owner);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static void *
gc_alloc0_unchecked(Ty *ty, usize n)
{
        MemoryUsed += n;
        NoteAlloc(n, GC_ANY);

        Alloc *a = ty_calloc(1, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = GC_ANY;
        atomic_init(&a->mark, ty->gc_owner);

        return a->data;
}

#define GC_BLOCKABLE ( (1ULL << GC_STRING)      \
                     | (1ULL << GC_TUPLE)       \
                     | (1ULL << GC_VALUE)       \
                     | (1ULL << GC_ENV)         \
                     | (1ULL << GC_OBJECT)      \
                     | (1ULL << GC_ARRAY)       \
                     | (1ULL << GC_QUEUE)       \
                     | (1ULL << GC_DICT)        \
                     | (1ULL << GC_SET)         \
                     | (1ULL << GC_HEAP)        \
                     | (1ULL << GC_BUF_VALUES)  \
                     | (1ULL << GC_BUF_DICT)    \
                     | (1ULL << GC_BUF_SET)     \
                     | (1ULL << GC_IDS)         )

#define VEC_OWNED(v) _Generic(&(v),         \
        struct array *: GC_BUF_VALUES,      \
        default:        0                   \
)

void *
GCOwnedResize(Ty *ty, void *p, usize n, usize used, char type, bool check);

void
GCTrackCleanup(Ty *ty, Alloc *a);

[[gnu::always_inline]]
inline static void
GCMarkOwned(Ty *ty, void const *owner, void const *buf)
{
        if (buf == NULL) {
                return;
        }

        if (InGCBlocks(ALLOC_OF(buf))) {
                GCBlock *b = GCBlockOf(ALLOC_OF(buf));
                u32      i = GCCellOf(b, ALLOC_OF(buf));
                if (b->owner == ty->gc_owner) {
                        b->marks[i] = 1;
                        b->refs[i]  = GCBlockRef(ALLOC_OF(owner));
                }
        } else if (InGCBlocks(ALLOC_OF(owner))) {
                GCTrackCleanup(ty, ALLOC_OF(owner));
        }
}

void *
GCBlockAlloc(Ty *ty, usize n, char type);

void *
GCLargeAlloc(Ty *ty, usize n, char type);

void
GCTrackDynamic(Ty *ty, void const *obj);

[[gnu::always_inline]]
inline static void *
gc_block_take(Ty *ty, GCBlock *b, u32 i, usize n, char type)
{
        Alloc *a = (Alloc *)(b->cells + (usize)i * b->cell);

        b->taken[i] = 1;
        b->flags[i] = 0;
        b->cursor   = i + 1;
        b->used    += 1;

        a->type = type;
        a->size = n;
        atomic_init(&a->mark, ty->gc_owner);
        atomic_init(&a->hard, 0);

        MemoryUsed += b->cell;

        return a->data;
}

[[gnu::always_inline]]
inline static void *
gc_block_object(Ty *ty, usize n, char type)
{
        GCBlock *b = ty->blocks.cur[GCBlockClass[(n + sizeof (Alloc) + 15) >> 4]];

        if (LIKELY((b != NULL) && (b->cursor < b->ncells) && (b->taken[b->cursor] == 0))) {
                return gc_block_take(ty, b, b->cursor, n, type);
        }

        return GCBlockAlloc(ty, n, type);
}

[[gnu::always_inline]]
inline static bool
gc_blockable(usize n, char type)
{
        return (GCBlockSpan != 0) && ((GC_BLOCKABLE >> type) & 1);
}

[[gnu::always_inline]]
inline static void *
gc_range_object(Ty *ty, usize n, char type)
{
        return (n <= GC_BLOCK_CELL - sizeof (Alloc))
             ? gc_block_object(ty, n, type)
             : GCLargeAlloc(ty, n, type);
}

[[gnu::always_inline]]
inline static void *
gc_object_heap(Ty *ty, usize n, char type, bool zero)
{
        MemoryUsed += n;

        Alloc *a = zero ? ty_calloc(1, sizeof *a + n) : ty_malloc(sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        atomic_init(&a->mark, ty->gc_owner);
        atomic_init(&a->hard, 0);
        a->type = type;
        a->size = n;

        AddAlloc(ty, a);
        PROF_BIND(ty, a);

        return a->data;
}

[[gnu::always_inline]]
inline static void *
gc_object(Ty *ty, usize n, char type, bool zero, bool check)
{
        if (n == 0) {
                return NULL;
        }

        NoteAlloc(n, type);

        if (check) {
                CheckUsed(ty);
        }

        void *p = gc_blockable(n, type) ? gc_range_object(ty, n, type) : NULL;

        if (p == NULL) {
                return gc_object_heap(ty, n, type, zero);
        }

        PROF_BIND(ty, ALLOC_OF(p));

        if (zero) {
                memset(p, 0, n);
        }

        return p;
}

inline static void *
gc_alloc_object(Ty *ty, usize n, char type)
{
        return gc_object(ty, n, type, false, true);
}

inline static void *
gc_alloc_object_unchecked(Ty *ty, usize n, char type)
{
        return gc_object(ty, n, type, false, false);
}

inline static void *
gc_alloc_object0(Ty *ty, usize n, char type)
{
        return gc_object(ty, n, type, true, true);
}

inline static void *
gc_alloc_object0_unchecked(Ty *ty, usize n, char type)
{
        return gc_object(ty, n, type, true, false);
}

inline static void *
gc_alloc_object_heap(Ty *ty, usize n, char type, bool zero, bool check)
{
        if (n == 0) {
                return NULL;
        }

        NoteAlloc(n, type);

        if (check) {
                CheckUsed(ty);
        }

        return gc_object_heap(ty, n, type, zero);
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
        if (p != NULL && InGCBlocks(ALLOC_OF(p))) {
                GCBlockDrop(ty, ALLOC_OF(p));
        } else if (p != NULL) {
                Alloc *a = ALLOC_OF(p);
                if (UNLIKELY(atomic_load_explicit(&a->hard, memory_order_relaxed) != 0)) {
                        GCRepin(ty, a, NULL);
                }
                PROF_FREE(a);
                if (a->size >= MemoryUsed) {
                        MemoryUsed = 0;
                } else {
                        MemoryUsed -= a->size;
                }
                ty_free(a);
        }
}

inline static void *
gc_resize(Ty *ty, void *p, usize n) {
        Alloc *a;

        if (UNLIKELY(p != NULL && InGCBlocks(ALLOC_OF(p)))) {
                void *q = gc_resize(ty, NULL, n);
                memcpy(q, p, min(ALLOC_OF(p)->size, n));
                GCBlockDrop(ty, ALLOC_OF(p));
                return q;
        }

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
        NoteAlloc((a != NULL && a->size < n) ? n - a->size : (a == NULL) ? n : 0, (a != NULL) ? a->type : GC_ANY);

        CheckUsed(ty);

        Alloc *old = a;

        a = ty_realloc(a, sizeof *a + n);
        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;

        if (old == NULL) {
                a->type = GC_ANY;
                atomic_init(&a->mark, ty->gc_owner);
                atomic_init(&a->hard, 0);
        } else if (UNLIKELY(a != old && atomic_load_explicit(&a->hard, memory_order_relaxed) != 0)) {
                GCRepin(ty, old, a);
        }

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
GCSweepTy(Ty *ty);

void
GCSweep(Ty *ty, AllocList *allocs, isize *used);

void
GCForget(Ty *ty, AllocList *allocs, isize *used);

void
GCForgetObject(Ty *ty, void const *o);

void
GCTakeOwnership(Ty *ty, AllocList *new);

void
GCTrackFinalizable(Ty *ty, TyObject const *obj);

void
GCQueueFinalizers(Ty *ty, ValueVector *queue);

void
GCDropFinalizable(Ty *ty);

void
GCDropFFIAutos(AllocList *list);

bool
GCRegistered(Ty *ty, void const *p);

void
GCDropRefIndex(ThreadGroup *group);

void
GCBlockInit(void);

void
GCSweepBlocks(Ty *ty);

void
GCSweepDeadBlocks(Ty *ty);

void
GCAdoptBlocks(GCBlockCache *to, GCBlockCache *from, u8 owner);

void
GCFreeBlockCache(GCBlockCache *bc);

void
GCMarkPinned(Ty *ty, AllocList *pinned);

void
GCPinYoung(Ty *ty, AllocList const *pinned, AllocList *young);

void
GCUnpinYoung(AllocList *young);

Alloc *
GCBufferOwner(Ty *ty, Alloc const *buf);

void
GCRetrace(Ty *ty, Alloc *a, char const *lo, char const *hi);

void
GCDrain(Ty *ty);

void
GCClearMarks(Ty *ty);

bool
GCPrepare(Ty *ty, bool minor);

bool
GCMinorOK(Ty *ty);

void
GCProtect(Ty *ty);

void
GCVerifyMinor(Ty *ty);

void
GCSnapshot(Ty *ty, byte_vector *snap, bool check);

void
DoGCKind(Ty *ty, bool minor);

extern bool       GCVerify;
extern atomic_bool GCShareWanted;

void
GCShare(Ty *ty);

bool
GCParallelBegin(Ty *ty, bool minor);

void
GCParallelEnd(Ty *ty);
extern atomic_int GCIsolatedGroups;


GCRootSet *
GCRoots(Ty *ty);

void *
GCImmortalSet(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
