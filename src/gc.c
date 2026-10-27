#include <sys/mman.h>

#include <libco.h>

#include "gc.h"
#include "dict.h"
#include "set.h"
#include "heap.h"
#include "object.h"
#include "vm.h"
#include "log.h"
#include "class.h"
#include "ty/thread.h"
#include "compiler.h"
#include "alloc.h"
#include "itable.h"
#include "chan.h"
#include "queue.h"
#include "screen.h"
#include "jit/lir.h"

static GCRootSet ImmortalSet;

uptr      GCBlockBase;
usize     GCBlockSpan;
u8  const GCBlockClass[GC_BLOCK_CELL / 16 + 1] = {
         0,  0,  0,  1,  2,  3,  4,  5,  6,  7,  7,  8,  8,  9,  9, 10,
        10, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13, 14, 14, 14,
        14
};

static u16 const GCBlockCells[GC_BLOCK_CLASSES] = {
        32, 48, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, 448, 512
};

enum { GC_BLOCK_KEEP = 128 };

static struct {
        TySpinLock  lock;
        GCBlockList free;
        usize       used;
        uptr        next;
        uptr        end;
} BlockPool;
static TySpinLock ImmortalLock = TY_MUTEX_INIT;

#define A_LOAD(p)     atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x) atomic_store_explicit((p), (x), memory_order_relaxed)

inline static void
finalize(Ty *ty, struct alloc *a)
{
        TyObject *obj = (TyObject *)a->data;
        Value     o;
        Value     f;

        switch (a->type) {
        case GC_OBJECT:
                if (obj->finalized || obj->class->finalizer.type == VALUE_NONE) {
                        break;
                }
                o = OBJECT(obj, obj->class->i);
                f = obj->class->finalizer;
                obj->finalized = true;
                vm_call_method(ty, &o, &f, 0);
                break;

        case GC_FFI_AUTO:
                o = ((Value *)a->data)[1];
                f = ((Value *)a->data)[0];
                if (f.type == VALUE_PTR) {
                        ((void (*)(void *))f.ptr)(o.ptr);
                } else {
                        vmP(&o);
                        vmC(&f, 1);
                }
                break;
        }
}

inline static bool
inert(struct alloc const *a)
{
        enum : u32 {
                INERT = (1U << GC_STRING)
                      | (1U << GC_TUPLE)
                      | (1U << GC_VALUE)
                      | (1U << GC_ENV)
                      | (1U << GC_ANY)
        };

        if ((INERT >> a->type) & 1) {
                return true;
        }

        TyObject const *obj = (TyObject const *)a->data;

        return (a->type == GC_OBJECT)
            && (obj->dynamic == NULL)
            && (obj->finalized || obj->class->finalizer.type == VALUE_NONE);
}

inline static void
collect(Ty *ty, struct alloc *a)
{
        void *p = a->data;

        Regex *re;
        Thread *t;
        Generator *gen;

        switch (a->type) {
        case GC_ARRAY:
                mF(((Array *)p)->items);
                break;

        case GC_BLOB:
                mF(((Blob *)p)->items);
                break;

        case GC_DICT:
                dict_free(ty, p);
                break;

        case GC_SET:
                set_free(ty, p);
                break;

        case GC_HEAP:
                heap_free(ty, p);
                break;

        case GC_QUEUE:
                mF(((Queue *)p)->items);
                break;

        case GC_SHARED_QUEUE:
                shared_queue_free(ty, p);
                break;

        case GC_GENERATOR:
                gen = p;
                if (UNLIKELY((gen->co != ty->co_top) & (gen->co != NULL))) {
                        xvP(ty->cothreads, gen->co);
                }
                if (gen->kept && KeptStacks > 0) {
                        KeptStacks -= 1;
                }
                if (LIKELY(gen->st != NULL)) {
                        xvP(ty->co_states, gen->st);
                }
                break;

        case GC_MUTEX:
                TyMutexDestroy(p);
                break;

        case GC_SPINLOCK:
                TySpinLockDestroy(p);
                break;

        case GC_CONDVAR:
                TyCondVarDestroy(p);
                break;

        case GC_NOTE:
                TyNoteFree(*(TyNote *)p);
                break;

        case GC_COUNTER:
                TyCounterFree(*(TyCounter *)p);
                break;

        case GC_CHANNEL:
                chan_destroy(ty, p);
                break;

        case GC_SCREEN:
                screen_free(ty, p);
                break;

        case GC_THREAD:
                t = p;
                if (!t->joined && !t->detached) {
                        TyMutexLock(&t->mutex);
                        if (!t->alive) {
                                TyThreadJoin(t->t);
                        } else {
                                TyThreadDetach(t->t);
                        }
                        TyMutexUnlock(&t->mutex);
                }
                TyMutexDestroy(&t->mutex);
                TyCondVarDestroy(&t->cond);
                break;

        case GC_OBJECT:
                finalize(ty, a);
                if (((TyObject *)p)->dynamic != NULL) {
                        itable_release(ty, ((TyObject *)p)->dynamic);
                        mF(((TyObject *)p)->dynamic);
                }
                break;

        case GC_REGEX:
                re = p;
                pcre2_code_free(re->pcre2);
                ty_free((char *)re->pattern);
                break;

        case GC_ARENA:
#if defined(TY_SYSMALLOC)
                FreeArenaChunks(p);
#else
                ForgetSourceNodesFrom(p, a->size);
#endif
                ArenaForget(p);
                break;

        case GC_FUN_INFO:
                mF(((FunUserInfo *)p)->doc);
                mF(((FunUserInfo *)p)->proto);
                mF(((FunUserInfo *)p)->name);
                break;

        case GC_JIT_CODE:
                lir_code_destroy(p);
                break;

        case GC_LIR:
                lir_destroy(p);
                break;

        case GC_FFI_AUTO:
                finalize(ty, a);
                break;
        }
}

void
GCForgetObject(Ty *ty, void const *o)
{
        AllocList *lists[] = { &ty->special, &ty->allocs };

        for (usize k = 0; k < countof(lists); ++k) {
                for (usize i = vN(*lists[k]); i > 0; --i) {
                        if (v__(*lists[k], i - 1)->data == o) {
                                MemoryUsed -= v__(*lists[k], i - 1)->size;
                                vvXi(*lists[k], i - 1);
                                return;
                        }
                }
        }
}

void
GCForget(Ty *ty, AllocList *allocs, isize *used)
{
        for (usize i = 0; i < vN(*allocs); ++i) {
                if (
                        (A_LOAD(&v__(*allocs, i)->mark) & 1)
                     || (A_LOAD(&v__(*allocs, i)->hard) != 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        A_STORE(&v__(*allocs, i)->mark, A_LOAD(&v__(*allocs, i)->mark) & ~1);
                        SWAP(struct alloc *, v__(*allocs, i), v_L(*allocs));
                        vvX(*allocs);
                }
        }
}

static void
sweep_list(Ty *ty, AllocList *list)
{
        usize n = 0;

        GC_STOP();
        for (usize i = 0; i < vN(*list); ++i) {
                struct alloc *a = v__(*list, i);
                if (i + 8 < vN(*list)) {
                        __builtin_prefetch(v__(*list, i + 8));
                }
                if (
                        !(A_LOAD(&a->mark) & 1)
                     && (A_LOAD(&a->hard) == 0)
                ) {
                        ty->memory_used -= min(a->size, ty->memory_used);
                        PROF_FREE(a);
                        if (!inert(a)) {
                                collect(ty, a);
                        }
                        ty_free(a);
                } else {
                        A_STORE(&a->mark, A_LOAD(&a->mark) & ~1);
                        *v_(*list, n++) = a;
                }
        }
        GC_RESUME();

        vN(*list) = n;
}

void
GCSweepTy(Ty *ty)
{
        GCDropRefIndex(ty->group);
        GCDropFFIAutos(&ty->ffi_autos);

        sweep_list(ty, &ty->special);
        sweep_list(ty, &ty->allocs);
        GCSweepBlocks(ty);
}

void
GCSweep(Ty *ty, AllocList *allocs, isize *used)
{
        usize n = 0;

        GCDropRefIndex(ty->group);

        GC_STOP();
        for (int i = 0; i < vN(*allocs); ++i) {
                if (
                        !(A_LOAD(&v__(*allocs, i)->mark) & 1)
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        finalize(ty, v__(*allocs, i));
                }
        }
        for (int i = 0; i < vN(*allocs); ++i) {
                if (
                        !(A_LOAD(&v__(*allocs, i)->mark) & 1)
                     && (A_LOAD(&v__(*allocs, i)->hard) == 0)
                ) {
                        *used -= min(v__(*allocs, i)->size, *used);
                        PROF_FREE(v__(*allocs, i));
                        if (v__(*allocs, i)->type != GC_FFI_AUTO) {
                                collect(ty, v__(*allocs, i));
                        }
                        ty_free(v__(*allocs, i));
                } else {
                        A_STORE(&v__(*allocs, i)->mark, A_LOAD(&v__(*allocs, i)->mark) & ~1);
                        *v_(*allocs, n++) = v__(*allocs, i);
                }
        }
        GC_RESUME();

        vN(*allocs) = n;
}

void
GCTrackFinalizable(Ty *ty, TyObject const *obj)
{
        struct alloc *a = ALLOC_OF(obj);

        xvP(ty->finalizable, a);

        for (usize i = vN(ty->allocs); i > 0; --i) {
                if (v__(ty->allocs, i - 1) == a) {
                        vvXi(ty->allocs, i - 1);
                        xvP(ty->special, a);
                        return;
                }
        }
}

inline static bool
doomed(struct alloc *a)
{
        return !(A_LOAD(&a->mark) & 1) && (A_LOAD(&a->hard) == 0);
}

static void
QueueFinalizers(Ty *ty, AllocList *list, ValueVector *queue)
{
        usize n = 0;

        for (usize i = 0; i < vN(*list); ++i) {
                struct alloc *a   = v__(*list, i);
                TyObject     *obj = (TyObject *)a->data;

                if (doomed(a) && obj->finalized) {
                        continue;
                }

                *v_(*list, n++) = a;

                if (doomed(a)) {
                        Value v = OBJECT(obj, obj->class->i);
                        obj->finalized = true;
                        xvP(*queue, v);
                        value_mark(ty, &v);
                }
        }

        vN(*list) = n;
}

void
GCQueueFinalizers(Ty *ty, ValueVector *queue)
{
        for (int i = 0; i < vN(ty->group->TyList); ++i) {
                Ty *other = v__(ty->group->TyList, i);
                if (other != ty) {
                        QueueFinalizers(ty, &other->finalizable, queue);
                }
        }

        QueueFinalizers(ty, &ty->finalizable, queue);

        TySpinLockLock(&ty->group->DLock);
        QueueFinalizers(ty, &ty->group->DeadFinalizable, queue);
        TySpinLockUnlock(&ty->group->DLock);
}

void
GCDropFinalizable(Ty *ty)
{
        AllocList *list = &ty->group->DeadFinalizable;
        usize      n    = 0;

        for (usize i = 0; i < vN(*list); ++i) {
                if (!doomed(v__(*list, i))) {
                        *v_(*list, n++) = v__(*list, i);
                }
        }

        vN(*list) = n;
}

inline static usize
ref_slot(void const *p, usize mask)
{
        u64 h = (u64)(uptr)p * 0x9E3779B97F4A7C15ULL;
        return (h ^ (h >> 29)) & mask;
}

static void
ref_add(ThreadGroup *group, void const *p)
{
        usize i = ref_slot(p, group->RefMask);

        while (group->RefIndex[i] != NULL) {
                i = (i + 1) & group->RefMask;
        }

        group->RefIndex[i] = p;
}

static void
ref_build(ThreadGroup *group)
{
        usize n   = vN(group->DeadAllocs);
        usize cap = 64;

        for (usize i = 0; i < vN(group->TyList); ++i) {
                Ty const *t = v__(group->TyList, i);
                n += vN(t->allocs) + vN(t->special);
        }

        while (cap < 2 * n + 1) {
                cap <<= 1;
        }

        if (group->RefIndex == NULL || cap > group->RefMask + 1) {
                xmF(group->RefIndex);
                group->RefIndex = mrealloc(NULL, cap * sizeof *group->RefIndex);
                group->RefMask  = cap - 1;
        }

        memset(group->RefIndex, 0, (group->RefMask + 1) * sizeof *group->RefIndex);

        for (usize i = 0; i < vN(group->TyList); ++i) {
                Ty const        *t       = v__(group->TyList, i);
                AllocList const *lists[] = { &t->allocs, &t->special };
                for (usize k = 0; k < countof(lists); ++k) {
                        for (usize j = 0; j < vN(*lists[k]); ++j) {
                                ref_add(group, v__(*lists[k], j)->data);
                        }
                }
        }

        for (usize i = 0; i < vN(group->DeadAllocs); ++i) {
                ref_add(group, v__(group->DeadAllocs, i)->data);
        }
}

static bool
ref_scan(ThreadGroup const *group, void const *p)
{
        for (usize i = 0; i < vN(group->TyList); ++i) {
                Ty const        *t       = v__(group->TyList, i);
                AllocList const *lists[] = { &t->allocs, &t->special };
                for (usize k = 0; k < countof(lists); ++k) {
                        for (usize j = 0; j < vN(*lists[k]); ++j) {
                                if (v__(*lists[k], j)->data == p) {
                                        return true;
                                }
                        }
                }
        }

        for (usize i = 0; i < vN(group->DeadAllocs); ++i) {
                if (v__(group->DeadAllocs, i)->data == p) {
                        return true;
                }
        }

        return false;
}

static bool
block_registered(Ty *ty, struct alloc const *a);

bool
GCRegistered(Ty *ty, void const *p)
{
        ThreadGroup *group = ty->group;

        if (InGCBlocks(ALLOC_OF(p))) {
                return block_registered(ty, ALLOC_OF(p));
        }

        if (
                !atomic_load_explicit(&group->RefReady, memory_order_acquire)
             && (atomic_fetch_add_explicit(&group->RefScans, 1, memory_order_relaxed) < 4)
        ) {
                return ref_scan(group, p);
        }

        if (!atomic_load_explicit(&group->RefReady, memory_order_acquire)) {
                TySpinLockLock(&group->RefLock);
                if (!atomic_load_explicit(&group->RefReady, memory_order_relaxed)) {
                        ref_build(group);
                        atomic_store_explicit(&group->RefReady, true, memory_order_release);
                }
                TySpinLockUnlock(&group->RefLock);
        }

        for (usize i = ref_slot(p, group->RefMask); group->RefIndex[i] != NULL; i = (i + 1) & group->RefMask) {
                if (group->RefIndex[i] == p) {
                        return true;
                }
        }

        return false;
}

void
GCDropRefIndex(ThreadGroup *group)
{
        atomic_store_explicit(&group->RefReady, false, memory_order_release);
        atomic_store_explicit(&group->RefScans, 0, memory_order_relaxed);
}

void
GCDropFFIAutos(AllocList *list)
{
        usize n = 0;

        for (usize i = 0; i < vN(*list); ++i) {
                if (!doomed(v__(*list, i))) {
                        *v_(*list, n++) = v__(*list, i);
                }
        }

        vN(*list) = n;
}

static isize
group_live(ThreadGroup const *group)
{
        isize live = group->DeadUsed;

        for (usize i = 0; i < vN(group->TyList); ++i) {
                live += v__(group->TyList, i)->memory_used;
        }

        return live;
}

void
GCCollect(Ty *ty)
{
        GCLOG("Running GC. Used = %zu MB, Limit = %zu MB", MemoryUsed / 1000000, MemoryLimit / 1000000);
        ty->gc_deferred = false;

        DoGC(ty);

        isize live = group_live(ty->group);

        MemoryLimit = max(GC_INITIAL_LIMIT, max(2 * MemoryUsed, MemoryUsed + live / 2));

        GCLOG("Memory limit is now %zu MB", MemoryLimit / 1000000);
}

void
GCRepin(Ty *ty, struct alloc const *old, struct alloc *new)
{
        for (usize i = vN(ty->pinned); i > 0; --i) {
                if (v__(ty->pinned, i - 1) == old) {
                        if (new != NULL) {
                                *v_(ty->pinned, i - 1) = new;
                        } else {
                                vvXi(ty->pinned, i - 1);
                        }
                }
        }
}

void
GCDefer(Ty *ty)
{
        ty->gc_deferred  = true;
        JitInterruptFlag = 1;
}

void
GCBlockInit(void)
{
        static bool once;
        char const *knob = getenv("TY_GC_BLOCKS");
        usize       span = (usize)1 << 36;

        if (once) {
                return;
        }

        once = true;

        TySpinLockInit(&BlockPool.lock);

        if ((knob != NULL && s_eq(knob, "0")) || ProfMode) {
                return;
        }

        char *base = VMap(span + GC_BLOCK_SIZE);

        if (base == NULL) {
                return;
        }

        BlockPool.next = ((uptr)base + GC_BLOCK_SIZE - 1) & ~(uptr)(GC_BLOCK_SIZE - 1);
        BlockPool.end  = BlockPool.next + span;
        GCBlockBase    = BlockPool.next;
        GCBlockSpan    = span;
}

static GCBlock *
block_new(Ty *ty, u32 cls)
{
        GCBlock *b = NULL;

        TySpinLockLock(&BlockPool.lock);
        if (vN(BlockPool.free) > 0) {
                b = vXx(BlockPool.free);
        } else if (BlockPool.next < BlockPool.end) {
                b               = (GCBlock *)BlockPool.next;
                BlockPool.next += GC_BLOCK_SIZE;
        }
        BlockPool.used += (b != NULL);
        TySpinLockUnlock(&BlockPool.lock);

        if (b == NULL) {
                return NULL;
        }

        u32   cell = GCBlockCells[cls];
        usize head = (sizeof *b + 15) & ~(usize)15;
        u32   n    = (GC_BLOCK_SIZE - head) / (cell + 2);
        usize body = (head + 2 * (usize)n + 15) & ~(usize)15;

        while (body + (usize)n * cell > GC_BLOCK_SIZE) {
                n -= 1;
        }

        *b = (GCBlock) {
                .owner  = ty->gc_owner,
                .cls    = cls,
                .cell   = cell,
                .ncells = n,
                .magic  = (((u64)1 << 32) + cell - 1) / cell,
                .marks  = (u8 *)b + head,
                .taken  = (u8 *)b + head + n,
                .cells  = (char *)b + body
        };

        memset(b->marks, 0, 2 * (usize)n);

        xvP(ty->blocks.all, b);

        return b;
}

static void
block_release(GCBlock *b)
{
        TySpinLockLock(&BlockPool.lock);
        BlockPool.used -= 1;
        if (vN(BlockPool.free) >= max(GC_BLOCK_KEEP, BlockPool.used)) {
                VDrop(b, GC_BLOCK_SIZE);
        }
        xvP(BlockPool.free, b);
        TySpinLockUnlock(&BlockPool.lock);
}

void *
GCBlockAlloc(Ty *ty, usize n, char type)
{
        u32           cls = GCBlockClass[(n + sizeof (struct alloc) + 15) >> 4];
        GCBlockCache *bc  = &ty->blocks;
        GCBlock      *b   = bc->cur[cls];

        for (;;) {
                if (b != NULL && b->cursor < b->ncells) {
                        u8 *hit = memchr(b->taken + b->cursor, 0, b->ncells - b->cursor);
                        if (hit != NULL) {
                                return gc_block_take(ty, b, (u32)(hit - b->taken), n, type);
                        }
                }

                b = (vN(bc->partial[cls]) > 0) ? vXx(bc->partial[cls]) : block_new(ty, cls);

                if (b == NULL) {
                        return NULL;
                }

                bc->cur[cls] = b;
        }
}

inline static u32
block_live(GCBlock const *b)
{
        u32       live = 0;
        u64 const *w   = (u64 const *)b->marks;
        u32       i    = 0;

        for (; i + 8 <= b->ncells; i += 8) {
                u64 x;
                memcpy(&x, (u8 const *)w + i, sizeof x);
                live += __builtin_popcountll(x);
        }

        for (; i < b->ncells; ++i) {
                live += b->marks[i];
        }

        return live;
}

static void
sweep_cleanup(Ty *ty, AllocList *cleanup)
{
        usize n = 0;

        for (usize i = 0; i < vN(*cleanup); ++i) {
                struct alloc *a   = v__(*cleanup, i);
                TyObject     *obj = (TyObject *)a->data;
                if (gc_marked(a, ty->gc_owner)) {
                        *v_(*cleanup, n++) = a;
                } else if (obj->dynamic != NULL) {
                        itable_release(ty, obj->dynamic);
                        mF(obj->dynamic);
                }
        }

        vN(*cleanup) = n;
}

static void
sweep_blocks(Ty *ty, GCBlockCache *bc, isize *used, AllocList *cleanup)
{
        usize n = 0;

        sweep_cleanup(ty, cleanup);

        for (u32 c = 0; c < GC_BLOCK_CLASSES; ++c) {
                bc->cur[c] = NULL;
                v0(bc->partial[c]);
        }

        for (usize i = 0; i < vN(bc->all); ++i) {
                GCBlock *b    = v__(bc->all, i);
                u32      live = block_live(b);

                *used      = max(0, *used + ((isize)live - (isize)b->used) * b->cell);
                b->used    = live;
                b->cursor  = 0;

                SWAP(u8 *, b->taken, b->marks);
                memset(b->marks, 0, b->ncells);

                if (live == 0) {
                        block_release(b);
                        continue;
                }

                *v_(bc->all, n++) = b;

                if (4 * live <= 3 * b->ncells) {
                        xvP(bc->partial[b->cls], b);
                }
        }

        vN(bc->all) = n;
}

void
GCSweepBlocks(Ty *ty)
{
        sweep_blocks(ty, &ty->blocks, &ty->memory_used, &ty->cleanup);
}

void
GCSweepDeadBlocks(Ty *ty)
{
        ThreadGroup *group = ty->group;
        sweep_blocks(ty, &group->DeadBlocks, &group->DeadUsed, &group->DeadCleanup);
}

void
GCAdoptBlocks(GCBlockCache *to, GCBlockCache *from, u8 owner)
{
        for (usize i = 0; i < vN(from->all); ++i) {
                v__(from->all, i)->owner = owner;
                xvP(to->all, v__(from->all, i));
        }

        v0(from->all);

        for (u32 c = 0; c < GC_BLOCK_CLASSES; ++c) {
                from->cur[c] = NULL;
                v0(from->partial[c]);
        }
}

void
GCFreeBlockCache(GCBlockCache *bc)
{
        for (u32 c = 0; c < GC_BLOCK_CLASSES; ++c) {
                xvF(bc->partial[c]);
        }

        xvF(bc->all);
}

void
GCMarkPinned(Ty *ty, AllocList *pinned)
{
        usize n = 0;

        for (usize i = 0; i < vN(*pinned); ++i) {
                struct alloc *a = v__(*pinned, i);
                if (atomic_load_explicit(&a->hard, memory_order_relaxed) != 0) {
                        gc_mark_alloc(a, ty->gc_owner);
                        *v_(*pinned, n++) = a;
                }
        }

        vN(*pinned) = n;
}

void
GCTrackDynamic(Ty *ty, void const *obj)
{
        struct alloc *a = ALLOC_OF(obj);

        if (InGCBlocks(a)) {
                xvP(ty->cleanup, a);
        }
}

static bool
block_registered(Ty *ty, struct alloc const *a)
{
        GCBlock const *b = GCBlockOf(a);

        if (b->owner != ty->gc_owner || (char const *)a < b->cells) {
                return false;
        }

        usize off = (usize)((char const *)a - b->cells);
        u32   i   = GCCellOf(b, a);

        return (off == (usize)i * b->cell) && (i < b->ncells) && (b->taken[i] != 0);
}

void
GCTakeOwnership(Ty *ty, AllocList *new)
{
        for (usize i = 0; i < new->count; ++i) {
                xvP(ty->allocs, new->items[i]);
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
        xvP(ty->allocs, ALLOC_OF(p));
}

void
gc_immortalize(Ty *ty, Value const *v)
{
        TySpinLockLock(&ImmortalLock);
        xvP(ImmortalSet, *v);
        TySpinLockUnlock(&ImmortalLock);
}

void
gc_clear_root_set(Ty *ty)
{
        v0(RootSet);
}

void
gc_truncate_root_set(Ty *ty, usize n)
{
        vN(RootSet) = n;
}

usize
gc_root_set_count(Ty *ty)
{
        return vN(RootSet);
}

GCRootSet *
GCRoots(Ty *ty)
{
        return &RootSet;
}

void *
GCImmortalSet(Ty *ty)
{
        return &ImmortalSet;
}

/* vim: set sts=8 sw=8 expandtab: */
