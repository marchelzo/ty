#include <sys/mman.h>

#if defined(__linux__)
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/syscall.h>
#include <linux/fs.h>
#include <linux/userfaultfd.h>
#endif

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

uptr     GCBlockBase;
usize    GCBlockSpan;
GCBlock *GCBlockMeta;
u8       GCBlockClass[GC_BLOCK_CELL / 16 + 1];
bool     GCGen;
bool     GCVerify;

atomic_int GCIsolatedGroups;

atomic_bool GCShareWanted;

enum {
        GC_HELPERS_MAX = 15,
        GC_SHARE_MIN   = 32,
        GC_TAKE        = 1024,
        GC_PAR_MIN     = 1 << 25
};

typedef struct {
        Ty          ty;
        GCWorkStack generic;
        TyThread    thread;
} GCHelper;

static struct {
        TyMutex     lock;
        TyCondVar   cv;
        TyCondVar   done;
        GCWorkStack work;
        GCWorkStack generic;
        GCHelper   *helpers[GC_HELPERS_MAX];
        int         want;
        int         n;
        int         idle;
        u8          owner;
        bool        active;
        atomic_bool busy;
} Pool = { .want = -1 };

#if defined(__linux__) && defined(UFFD_FEATURE_WP_ASYNC) && defined(PAGEMAP_SCAN)
 #define TY_GC_DIRTY 1
#endif

static struct {
        int                     uffd;
        int                     pagemap;
        bool                    ok;
        bool                    taint;
        vec(struct page_region) seen;
        vec(struct page_region) old;
} Dirty = { .uffd = -1, .pagemap = -1 };

static u32 const GCBlockCells[GC_BLOCK_CLASSES] = {
           32,    48,    64,    80,    96,   112,   128,   160,
          192,   224,   256,   320,   384,   448,   512,   640,
          768,  1024,  1280,  1536,  2048,  2720,  3264,  4096,
         5456,  6544,  8192, 10912, 13104, 16384, 21840, 32768
};

enum { GC_BLOCK_KEEP = 128 };

typedef struct {
        uptr  at;
        usize units;
} BlockRun;

static struct {
        TySpinLock    lock;
        GCBlockList   free;
        GCBlockList   cold;
        vec(BlockRun) runs;
        usize         used;
        usize         cached;
        u8           *maps;
        uptr          next;
        uptr          end;
} BlockPool;

static TySpinLock ImmortalLock = TY_MUTEX_INIT;

#define A_LOAD(p)     atomic_load_explicit((p), memory_order_relaxed)
#define A_STORE(p, x) atomic_store_explicit((p), (x), memory_order_relaxed)

inline static void
finalize(Ty *ty, Alloc *a)
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
                Dirty.taint    = true;
                vm_call_method(ty, &o, &f, 0);
                break;

        case GC_FFI_AUTO:
                o = ((Value *)a->data)[1];
                f = ((Value *)a->data)[0];
                if (f.type == VALUE_PTR) {
                        ((void (*)(void *))f.ptr)(o.ptr);
                } else {
                        Dirty.taint = true;
                        vmP(&o);
                        vmC(&f, 1);
                }
                break;
        }
}

inline static bool
inert(Alloc const *a)
{
        enum : u64 {
                INERT = (1ULL << GC_STRING)
                      | (1ULL << GC_TUPLE)
                      | (1ULL << GC_VALUE)
                      | (1ULL << GC_ENV)
                      | (1ULL << GC_IDS)
                      | (1ULL << GC_ANY)
        };

        if ((INERT >> a->type) & 1) {
                return true;
        }

        TyObject const *obj = (TyObject const *)a->data;

        return (a->type == GC_OBJECT)
            && (obj->dynamic == NULL)
            && (obj->finalized || IsNone(obj->class->finalizer));
}

inline static void
collect(Ty *ty, Alloc *a)
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
        AllocList *lists[] = { &ty->special, &ty->allocs, &ty->old };

        for (usize k = 0; k < countof(lists); ++k) {
                for (usize i = vN(*lists[k]); i > 0; --i) {
                        if (v__(*lists[k], i - 1)->data == o) {
                                if (lists[k] == &ty->old) {
                                        ty->old_used -= v__(*lists[k], i - 1)->size;
                                }
                                vvXi(*lists[k], i - 1);
                                return;
                        }
                }
        }
}

void
GCForget(Ty *ty, AllocList *allocs)
{
        for (usize i = 0; i < vN(*allocs); ++i) {
                if (
                        (A_LOAD(&v__(*allocs, i)->mark) & 1)
                     || (A_LOAD(&v__(*allocs, i)->hard) != 0)
                ) {
                        A_STORE(&v__(*allocs, i)->mark, A_LOAD(&v__(*allocs, i)->mark) & ~1);
                        SWAP(Alloc *, v__(*allocs, i), v_L(*allocs));
                        vvX(*allocs);
                }
        }
}

static isize
sweep_list(Ty *ty, AllocList *restrict list, AllocList *restrict old)
{
        usize n    = 0;
        isize live = 0;

        GC_STOP();
        for (usize i = 0; i < vN(*list); ++i) {
                Alloc *a = v__(*list, i);
                if (i + 8 < vN(*list)) {
                        __builtin_prefetch(v__(*list, i + 8));
                }
                if (
                        !(A_LOAD(&a->mark) & 1)
                     && (A_LOAD(&a->hard) == 0)
                ) {
                        PROF_FREE(a);
                        if (!inert(a)) {
                                collect(ty, a);
                        }
                        ty_free(a);
                } else if (!GCGen) {
                        A_STORE(&a->mark, A_LOAD(&a->mark) & ~1);
                        *v_(*list, n++) = a;
                        live += a->size;
                } else if (old != NULL && (A_LOAD(&a->mark) & 1)) {
                        xvP(*old, a);
                        ty->old_used += a->size;
                } else {
                        *v_(*list, n++) = a;
                        live += a->size;
                }
        }
        GC_RESUME();

        vN(*list) = n;

        return live;
}

void
GCSweepTy(Ty *ty)
{
        GCDropRefIndex(ty->group);
        GCDropFFIAutos(&ty->ffi_autos);

        isize live = sweep_list(ty, &ty->special, NULL);

        if (!ty->group->GCMinor) {
                ty->old_used = sweep_list(ty, &ty->old, NULL);
        }

        live += sweep_list(ty, &ty->allocs, &ty->old);
        live += ty->old_used;
        live += GCSweepBlocks(ty);

        atomic_fetch_add_explicit(&ty->group->GCSwept, live, memory_order_relaxed);
}

isize
GCSweep(Ty *ty, AllocList *allocs)
{
        usize n    = 0;
        isize live = 0;

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
                        PROF_FREE(v__(*allocs, i));
                        if (v__(*allocs, i)->type != GC_FFI_AUTO) {
                                collect(ty, v__(*allocs, i));
                        }
                        ty_free(v__(*allocs, i));
                } else {
                        if (!GCGen) {
                                A_STORE(&v__(*allocs, i)->mark, A_LOAD(&v__(*allocs, i)->mark) & ~1);
                        }
                        live += v__(*allocs, i)->size;
                        *v_(*allocs, n++) = v__(*allocs, i);
                }
        }
        GC_RESUME();

        vN(*allocs) = n;

        return live;
}

void
GCTrackFinalizable(Ty *ty, TyObject const *obj)
{
        Alloc *a = ALLOC_OF(obj);

        xvP(ty->finalizable, a);

        if (InGCBlocks(a)) {
                return;
        }

        for (usize i = vN(ty->allocs); i > 0; --i) {
                if (v__(ty->allocs, i - 1) == a) {
                        vvXi(ty->allocs, i - 1);
                        xvP(ty->special, a);
                        return;
                }
        }
}

inline static bool
doomed(Ty *ty, Alloc *a)
{
        return !gc_marked(a, ty->gc_owner) && (A_LOAD(&a->hard) == 0);
}

static void
QueueFinalizers(Ty *ty, AllocList *list, ValueVector *queue)
{
        usize n = 0;

        for (usize i = 0; i < vN(*list); ++i) {
                Alloc *a = v__(*list, i);
                TyObject *obj = (TyObject *)a->data;

                if (doomed(ty, a) && obj->finalized) {
                        continue;
                }

                *v_(*list, n++) = a;

                if (doomed(ty, a)) {
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
                if (!doomed(ty, v__(*list, i))) {
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
                n += vN(t->allocs) + vN(t->old) + vN(t->special);
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
                AllocList const *lists[] = { &t->allocs, &t->old, &t->special };
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
                AllocList const *lists[] = { &t->allocs, &t->old, &t->special };
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
block_registered(Ty *ty, Alloc const *a);

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
                if ((A_LOAD(&v__(*list, i)->mark) & 1) || (A_LOAD(&v__(*list, i)->hard) != 0)) {
                        *v_(*list, n++) = v__(*list, i);
                }
        }

        vN(*list) = n;
}

isize
GCHeap(ThreadGroup const *group)
{
        isize heap = group->GCLive + group->DeadUsed;

        for (usize i = 0; i < vN(group->TyList); ++i) {
                heap += v__(group->TyList, i)->memory_used;
        }

        return heap;
}

void
GCSettle(Ty *ty)
{
        ThreadGroup *group = ty->group;
        isize        live  = group->DeadBuf
                           + atomic_exchange_explicit(&group->GCSwept, 0, memory_order_relaxed);

        for (usize i = 0; i < vN(group->TyList); ++i) {
                live += v__(group->TyList, i)->buf_used;
        }

        group->GCPromoted = group->GCMinor ? live - group->GCLive : live;
        group->GCLive     = live;

        if (!group->GCMinor) {
                group->GCFullAt = max(GC_INITIAL_LIMIT, 2 * live);
        }

        isize budget = (GCMinorOK(ty) && (live >= GC_MINOR_MIN))
                     ? max(GC_INITIAL_LIMIT, min(live / 2, GC_NURSERY_MAX))
                     : max(GC_INITIAL_LIMIT, live);

        group->GCBudget = budget;
        atomic_store_explicit(&group->DeadUsed, 0, memory_order_relaxed);

        for (usize i = 0; i < vN(group->TyList); ++i) {
                v__(group->TyList, i)->memory_used  = 0;
                v__(group->TyList, i)->memory_limit = budget;
        }
}

void
GCCollect(Ty *ty)
{
        ThreadGroup *group = ty->group;

        GCLOG("Running GC. Used = %zu MB, Limit = %zu MB", MemoryUsed / 1000000, MemoryLimit / 1000000);
        ty->gc_deferred = false;

        bool gen = GCMinorOK(ty) && (group->GCLive >= GC_MINOR_MIN);

        DoGCKind(ty, gen && (group->GCLive < group->GCFullAt));

        GCLOG("Memory limit is now %zu MB", MemoryLimit / 1000000);
}

void
GCRepin(Ty *ty, Alloc const *old, Alloc *new)
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

enum : u64 {
        GC_RETRACED = (1ULL << GC_TUPLE)
                    | (1ULL << GC_VALUE)
                    | (1ULL << GC_OBJECT)
                    | (1ULL << GC_ARRAY)
                    | (1ULL << GC_HEAP)
                    | (1ULL << GC_DICT)
                    | (1ULL << GC_SET)
                    | (1ULL << GC_QUEUE)
                    | (1ULL << GC_SHARED_QUEUE)
                    | (1ULL << GC_GENERATOR)
                    | (1ULL << GC_THREAD)
                    | (1ULL << GC_JIT_CODE)
                    | (1ULL << GC_LIR)
                    | (1ULL << GC_FFI_AUTO)
                    | (1ULL << GC_BUF_VALUES)
                    | (1ULL << GC_BUF_DICT)
                    | (1ULL << GC_BUF_SET)
                    | (1ULL << GC_ENV)
};

inline static bool
retraced(Alloc const *a)
{
        return (GC_RETRACED >> a->type) & 1;
}

#if defined(TY_GC_DIRTY)
static void
dirty_fork(void)
{
        close(Dirty.uffd);
        close(Dirty.pagemap);

        Dirty.uffd    = -1;
        Dirty.pagemap = -1;
        Dirty.ok      = false;
}

static bool
dirty_init(uptr base, usize span)
{
        struct uffdio_api api = {
                .api      = UFFD_API,
                .features = UFFD_FEATURE_WP_ASYNC | UFFD_FEATURE_WP_UNPOPULATED
        };

        struct uffdio_register reg = {
                .range = { .start = base, .len = span },
                .mode  = UFFDIO_REGISTER_MODE_WP
        };

        Dirty.uffd    = syscall(SYS_userfaultfd, O_CLOEXEC | O_NONBLOCK | UFFD_USER_MODE_ONLY);
        Dirty.pagemap = open("/proc/self/pagemap", O_RDONLY | O_CLOEXEC);

        if (
                (Dirty.uffd    < 0)
             || (Dirty.pagemap < 0)
             || (ioctl(Dirty.uffd, UFFDIO_API,      &api) != 0)
             || (ioctl(Dirty.uffd, UFFDIO_REGISTER, &reg) != 0)
        ) {
                dirty_fork();
                return false;
        }

        pthread_atfork(NULL, NULL, dirty_fork);

        return true;
}

static void
dirty_mode(uptr at, usize n, u64 mode)
{
        struct uffdio_writeprotect wp = {
                .range = {.start = at, .len = n},
                .mode  = mode
        };

        if (Dirty.ok && n > 0 && ioctl(Dirty.uffd, UFFDIO_WRITEPROTECT, &wp) != 0) {
                Dirty.ok = false;
        }
}

static void
dirty_unprotect(uptr at, usize n)
{
        dirty_mode(at, n, 0);
}

static void
rescan_range(Ty *ty, char *lo, char *hi);

static bool
dirty_scan(Ty *ty, bool rescan)
{
        struct page_region regs[256];

        uptr at = GCBlockBase;
        uptr end;

        TySpinLockLock(&BlockPool.lock);
        end = BlockPool.next;
        TySpinLockUnlock(&BlockPool.lock);

        v0(Dirty.seen);

        while (at < end) {
                struct pm_scan_arg arg = {
                        .size          = sizeof arg,
                        .flags         = PM_SCAN_CHECK_WPASYNC,
                        .start         = at,
                        .end           = end,
                        .vec           = (uptr)regs,
                        .vec_len       = countof(regs),
                        .category_mask = PAGE_IS_WRITTEN,
                        .return_mask   = PAGE_IS_WRITTEN
                };

                long n = ioctl(Dirty.pagemap, PAGEMAP_SCAN, &arg);

                if (n < 0) {
                        Dirty.ok = (errno == EINTR);
                        return false;
                }

                for (long i = 0; i < n; ++i) {
                        xvP(Dirty.seen, regs[i]);
                }

                for (long i = 0; rescan && i < n; ++i) {
                        rescan_range(ty, (char *)regs[i].start, (char *)regs[i].end);
                }

                at = arg.walk_end;
        }

        for (usize i = 0; i < vN(Dirty.old); ++i) {
                struct page_region const *r = v_(Dirty.old, i);
                Alloc                    *a = (Alloc *)r->categories;
                if (a->type == GC_OBJECT || a->type == GC_TUPLE) {
                        xvP(ty->marking, ((GCWork) { .p = (uptr)a->data | 1 }));
                } else {
                        GCRetrace(ty, a, (char *)r->start, (char *)r->end);
                }
        }

        v0(Dirty.old);

        return true;
}

inline static bool
hashed(Alloc const *a)
{
        return (a->type == GC_BUF_DICT) || (a->type == GC_BUF_SET);
}

inline static bool
dense(GCBlock const *b, u8 young)
{
        Alloc const *a = (Alloc const *)b->cells;

        return (b->cls == GC_BLOCK_LARGE)    ? (b->age >= 1 + hashed(a)) && retraced(a)
             : (4 * b->used > 3 * b->ncells) ? (b->age >= young)
             :                                 (b->age >= 2) && (4 * b->used > b->ncells);
}

void
GCProtect(Ty *ty)
{
        uptr lo    = 0;
        uptr hi    = 0;
        u8   young = (ty->group->GCPromoted >= GC_PAR_MIN) ? 1 : 2;

        if (Dirty.taint || !Dirty.ok || atomic_load(&GCIsolatedGroups) != 0) {
                v0(Dirty.seen);
                return;
        }

        for (usize i = 0; i < vN(Dirty.seen); ++i) {
                uptr s   = v_(Dirty.seen, i)->start;
                uptr end = v_(Dirty.seen, i)->end;
                for (uptr at = s & ~(uptr)(GC_BLOCK_SIZE - 1); at < end; at += GC_BLOCK_SIZE) {
                        GCBlock *b = GCBlockOf((void *)at);
                        GCBlock *u = GCBlockAt((void *)at);
                        uptr     x = max(s, at);
                        uptr     y = min(end, at + GC_BLOCK_SIZE);
                        if (b->ncells == 0 || b->owner != ty->gc_owner) {
                                continue;
                        }
                        if (u->wp) {
                                u->wp   = 0;
                                b->cool = 3;
                        }
                        if (b->cool != 0 || !dense(b, young)) {
                                continue;
                        }
                        if (x != hi) {
                                dirty_mode(lo, hi - lo, UFFDIO_WRITEPROTECT_MODE_WP);
                                lo = x;
                        }
                        hi = y;
                        GCBlockAt((void *)at)->wp = 1;
                }
        }

        dirty_mode(lo, hi - lo, UFFDIO_WRITEPROTECT_MODE_WP);

        v0(Dirty.seen);
}
#else
static bool
dirty_init(uptr base, usize span)
{
        return false;
}

void
GCProtect(Ty *ty)
{
}

static void
dirty_unprotect(uptr at, usize n)
{
}

static bool
dirty_scan(Ty *ty, bool rescan)
{
        return false;
}
#endif

void
GCBlockInit(void)
{
        char const *knob = getenv("TY_GC_BLOCKS");
        usize       span = (usize)1 << 36;
        usize       n    = span >> GC_BLOCK_SHIFT;

        TySpinLockInit(&BlockPool.lock);

        for (usize k = 0, c = 0; k < countof(GCBlockClass); ++k) {
                while (GCBlockCells[c] < 16 * k) {
                        c += 1;
                }
                GCBlockClass[k] = c;
        }

        if (knob != NULL && s_eq(knob, "0")) {
                return;
        }

        char    *base = VMap(span + GC_BLOCK_SIZE);
        GCBlock *meta = VMap(n * sizeof (GCBlock));
        u8      *maps = VMap(n * GC_BLOCK_MAPS);

        if (base == NULL || meta == NULL || maps == NULL) {
                return;
        }

        BlockPool.next = ((uptr)base + GC_BLOCK_SIZE - 1) & ~(uptr)(GC_BLOCK_SIZE - 1);
        BlockPool.end  = BlockPool.next + span;
        BlockPool.maps = maps;
        GCBlockMeta    = meta;
        GCBlockBase    = BlockPool.next;
        GCBlockSpan    = span;

        knob = getenv("TY_GC_GEN");

        if (knob == NULL || !s_eq(knob, "0")) {
                GCGen    = true;
                Dirty.ok = dirty_init(GCBlockBase, GCBlockSpan);
                knob     = getenv("TY_GC_VERIFY");
                GCVerify = (knob != NULL) && !s_eq(knob, "0");
        }
}

inline static u8 *
block_maps(uptr at)
{
        return BlockPool.maps + ((at - GCBlockBase) >> GC_BLOCK_SHIFT) * GC_BLOCK_MAPS;
}

static int
run_cmp(void const *a, void const *b)
{
        uptr x = ((BlockRun const *)a)->at;
        uptr y = ((BlockRun const *)b)->at;
        return (x > y) - (x < y);
}

static void
pool_coalesce(void)
{
        usize n = 0;

        qsort(vv(BlockPool.runs), vN(BlockPool.runs), sizeof (BlockRun), run_cmp);

        for (usize i = 0; i < vN(BlockPool.runs); ++i) {
                BlockRun r = v__(BlockPool.runs, i);
                if (n > 0 && v_(BlockPool.runs, n - 1)->at + (v_(BlockPool.runs, n - 1)->units << GC_BLOCK_SHIFT) == r.at) {
                        v_(BlockPool.runs, n - 1)->units += r.units;
                } else {
                        *v_(BlockPool.runs, n++) = r;
                }
        }

        vN(BlockPool.runs) = n;
}

static uptr
pool_take(usize units)
{
        uptr at = 0;

        TySpinLockLock(&BlockPool.lock);

        if (units == 1 && vN(BlockPool.free) > 0) {
                at = (uptr)vXx(BlockPool.free)->cells;
        } else if (units == 1 && vN(BlockPool.cold) > 0) {
                at = (uptr)vXx(BlockPool.cold)->cells;
        } else {
                for (usize i = 0; i < vN(BlockPool.runs); ++i) {
                        BlockRun *r = v_(BlockPool.runs, i);
                        if (r->units >= units) {
                                at = r->at;
                                r->at += units << GC_BLOCK_SHIFT;
                                r->units -= units;
                                BlockPool.cached -= min(BlockPool.cached, units);
                                if (r->units == 0) {
                                        *r = vXx(BlockPool.runs);
                                }
                                break;
                        }
                }
                if (at == 0 && BlockPool.next + (units << GC_BLOCK_SHIFT) <= BlockPool.end) {
                        at = BlockPool.next;
                        BlockPool.next += units << GC_BLOCK_SHIFT;
                }
        }

        BlockPool.used += (at != 0) ? units : 0;

        TySpinLockUnlock(&BlockPool.lock);

        return at;
}

static void
pool_give(uptr at, usize units)
{
        for (usize u = 0; u < units; ++u) {
                GCBlock *b = GCBlockAt((void *)(at + (u << GC_BLOCK_SHIFT)));
                b->ncells = 0;
                b->cls    = 0;
        }

        TySpinLockLock(&BlockPool.lock);

        BlockPool.used -= units;

        usize keep = max(GC_BLOCK_KEEP, BlockPool.used);

        if (units == 1 && vN(BlockPool.free) >= keep) {
                VDrop((void *)at, GC_BLOCK_SIZE);
                xvP(BlockPool.cold, GCBlockAt((void *)at));
        } else if (units == 1) {
                xvP(BlockPool.free, GCBlockAt((void *)at));
        } else {
                if (BlockPool.cached + units > keep) {
                        VDrop((void *)at, units << GC_BLOCK_SHIFT);
                } else {
                        BlockPool.cached += units;
                }
                xvP(BlockPool.runs, ((BlockRun) { .at = at, .units = units }));
                if (vN(BlockPool.runs) > 64) {
                        pool_coalesce();
                }
        }

        TySpinLockUnlock(&BlockPool.lock);
}

static GCBlock *
block_new(Ty *ty, u32 cls)
{
        uptr at = pool_take(1);

        if (at == 0) {
                return NULL;
        }

        GCBlock *b    = GCBlockAt((void *)at);
        u32      cell = GCBlockCells[cls];

        if (b->wp) {
                dirty_unprotect(at, GC_BLOCK_SIZE);
        }

        u32      n    = GC_BLOCK_SIZE / cell;
        u8      *maps = block_maps(at);

        *b = (GCBlock) {
                .owner  = ty->gc_owner,
                .cls    = cls,
                .cell   = cell,
                .ncells = n,
                .units  = 1,
                .magic  = (((u64)1 << 32) + cell - 1) / cell,
                .marks  = maps,
                .taken  = maps + 2048,
                .flags  = maps + 4096,
                .refs   = (u32 *)(maps + 8192),
                .cells  = (char *)at,
                .home   = ty
        };

        memset(b->marks, 0, n);
        memset(b->taken, 0, n);
        memset(b->flags, 0, n);

        xvP(ty->blocks.all, b);

        return b;
}

void *
GCBlockAlloc(Ty *ty, usize n, char type)
{
        u32           cls = GCBlockClass[(n + sizeof (Alloc) + 15) >> 4];
        GCBlockCache *bc  = &ty->blocks;
        GCBlock      *b   = bc->cur[cls];

        for (;;) {
                if (b != NULL && b->cursor < b->ncells) {
                        u8 *hit = memchr(b->taken + b->cursor, 0, b->ncells - b->cursor);
                        if (hit != NULL) {
                                return gc_block_take(ty, b, (u32)(hit - b->taken), n, type);
                        }
                }

                if (vN(bc->partial[cls]) > 0) {
                        b = vXx(bc->partial[cls]);
                } else {
                        b = block_new(ty, cls);
                }

                if (b == NULL) {
                        return NULL;
                }

                if (b->wp) {
                        dirty_unprotect((uptr)b->cells, GC_BLOCK_SIZE);
                        b->wp = 0;
                }

                bc->cur[cls] = b;
        }
}

inline static usize
large_charge(GCBlock const *b)
{
        return ((Alloc const *)b->cells)->size + sizeof (Alloc);
}

void *
GCLargeAlloc(Ty *ty, usize n, char type)
{
        usize bytes = n + sizeof (Alloc);
        usize units = (bytes + GC_BLOCK_SIZE - 1) >> GC_BLOCK_SHIFT;

        if (bytes > UINT32_MAX) {
                return NULL;
        }

        uptr at = pool_take(units);
        u8   wp = 0;

        if (at == 0) {
                return NULL;
        }

        for (usize i = 0; i < units; ++i) {
                wp |= GCBlockAt((void *)(at + (i << GC_BLOCK_SHIFT)))->wp;
        }

        if (wp) {
                dirty_unprotect(at, units << GC_BLOCK_SHIFT);
        }

        GCBlock *b    = GCBlockAt((void *)at);
        u8      *maps = block_maps(at);

        *b = (GCBlock) {
                .owner  = ty->gc_owner,
                .cls    = GC_BLOCK_LARGE,
                .cell   = (u32)(units << GC_BLOCK_SHIFT),
                .ncells = 1,
                .units  = (u32)units,
                .magic  = 1,
                .marks  = maps,
                .taken  = maps + 1,
                .flags  = maps + 2,
                .refs   = (u32 *)(maps + 8192),
                .cells  = (char *)at,
                .home   = ty
        };

        b->marks[0] = 0;
        b->taken[0] = 0;

        for (usize i = 1; i < units; ++i) {
                GCBlock *c = GCBlockAt((void *)(at + (i << GC_BLOCK_SHIFT)));
                *c = (GCBlock) { .owner = ty->gc_owner, .cls = GC_BLOCK_CONT, .cells = (char *)at };
        }

        xvP(ty->blocks.large, b);

        void *p = gc_block_take(ty, b, 0, n, type);

        b->cursor   = 1;
        MemoryUsed += (isize)large_charge(b) - (isize)b->cell;

        return p;
}

inline static u32
block_live(GCBlock const *b)
{
        u32 live = 0;
        u32 i    = 0;

        for (; i + 8 <= b->ncells; i += 8) {
                u64 x;
                memcpy(&x, b->marks + i, sizeof x);
                live += (x * 0x0101010101010101ULL) >> 56;
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

        GC_STOP();
        for (usize i = 0; i < vN(*cleanup); ++i) {
                Alloc *a = v__(*cleanup, i);
                if (gc_marked(a, ty->gc_owner)) {
                        *v_(*cleanup, n++) = a;
                } else {
                        GCBlock *b = GCBlockOf(a);
                        b->flags[GCCellOf(b, a)] = 0;
                        collect(ty, a);
                }
        }
        GC_RESUME();

        vN(*cleanup) = n;
}

void
GCTrackCleanup(Ty *ty, Alloc *a)
{
        GCBlock *b = GCBlockOf(a);
        u8      *f = &b->flags[GCCellOf(b, a)];

        if ((*f & 1) == 0 && !(__atomic_fetch_or(f, 1, __ATOMIC_RELAXED) & 1)) {
                xvP(ty->cleanup, a);
        }
}

void *
GCOwnedResize(Ty *ty, void *p, usize n, usize used, char type, bool check)
{
        if (n == 0) {
                return NULL;
        }

        if (GCBlockSpan == 0) {
                char *r = check ? gc_resize(ty, p, n) : gc_resize_unchecked(ty, p, n);
                if (used < n) {
                        memset(r + used, 0, n - used);
                }
                return r;
        }

        char *q = gc_object(ty, n, type, false, check);

        used = min(used, n);

        if (p != NULL && used > 0) {
                memcpy(q, p, used);
        }

        memset(q + used, 0, n - used);

        gc_free(ty, p);

        return q;
}

static isize
sweep_blocks(Ty *ty, GCBlockCache *bc, AllocList *cleanup)
{
        usize n    = 0;
        isize used = 0;
        uptr  lo   = 0;
        uptr  hi   = 0;

        sweep_cleanup(ty, cleanup);

        for (u32 c = 0; c < GC_BLOCK_CLASSES; ++c) {
                bc->cur[c] = NULL;
                v0(bc->partial[c]);
        }

        for (usize i = 0; i < vN(bc->all); ++i) {
                GCBlock *b = v__(bc->all, i);
                u32 live = block_live(b);

                used += (isize)live * b->cell;

                b->used    = live;
                b->old     = live;
                b->age    += (b->age < 255);
                b->cool   -= (b->cool > 0);
                b->cursor  = 0;

                if (GCGen) {
                        memcpy(b->taken, b->marks, b->ncells);
                } else {
                        SWAP(u8 *, b->taken, b->marks);
                        memset(b->marks, 0, b->ncells);
                }

                if (live == 0 && b->wp) {
                        if ((uptr)b->cells != hi) {
                                dirty_unprotect(lo, hi - lo);
                                lo = (uptr)b->cells;
                        }
                        hi    = (uptr)b->cells + GC_BLOCK_SIZE;
                        b->wp = 0;
                }

                if (live == 0) {
                        pool_give((uptr)b->cells, 1);
                        continue;
                }

                *v_(bc->all, n++) = b;

                if (4 * live <= 3 * b->ncells) {
                        xvP(bc->partial[b->cls], b);
                }
        }

        dirty_unprotect(lo, hi - lo);

        vN(bc->all) = n;
        n = 0;

        for (usize i = 0; i < vN(bc->large); ++i) {
                GCBlock *b = v__(bc->large, i);

                if (b->marks[0] == 0) {
                        pool_give((uptr)b->cells, b->units);
                        continue;
                }

                b->age      += (b->age < 255);
                b->cool     -= (b->cool > 0);
                b->old       = 1;
                b->marks[0]  = GCGen;
                *v_(bc->large, n++) = b;
                used += (isize)large_charge(b);
        }

        vN(bc->large) = n;

        return used;
}

isize
GCSweepBlocks(Ty *ty)
{
        return sweep_blocks(ty, &ty->blocks, &ty->cleanup);
}

isize
GCSweepDeadBlocks(Ty *ty)
{
        ThreadGroup *group = ty->group;
        return sweep_blocks(ty, &group->DeadBlocks, &group->DeadCleanup);
}

void
GCAdoptBlocks(GCBlockCache *to, GCBlockCache *from, u8 owner)
{
        GCBlockList *lists[][2] = {
                { &to->all,   &from->all   },
                { &to->large, &from->large }
        };

        for (usize k = 0; k < countof(lists); ++k) {
                for (usize i = 0; i < vN(*lists[k][1]); ++i) {
                        GCBlock *b = v__(*lists[k][1], i);
                        b->owner = owner;
                        b->home  = NULL;
                        for (u32 u = 1; u < b->units; ++u) {
                                GCBlockAt(b->cells + ((usize)u << GC_BLOCK_SHIFT))->owner = owner;
                        }
                        xvP(*lists[k][0], b);
                }
                v0(*lists[k][1]);
        }

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
        xvF(bc->large);
}

static bool
block_cell_valid(GCBlock const *b, Alloc const *a);

void
GCBlockDrop(Ty *ty, Alloc *a)
{
        GCBlock *b = GCBlockOf(a);

        if (b->home != ty || A_LOAD(&a->hard) != 0 || !block_cell_valid(b, a)) {
                return;
        }

        if (b->cls == GC_BLOCK_LARGE) {
                for (usize i = vN(ty->blocks.large); i > 0; --i) {
                        if (v__(ty->blocks.large, i - 1) == b) {
                                *v_(ty->blocks.large, i - 1) = vXx(ty->blocks.large);
                                MemoryUsed = max(MemoryUsed - (isize)large_charge(b), 0);
                                PROF_FREE(a);
                                pool_give((uptr)b->cells, b->units);
                                return;
                        }
                }
                return;
        }

        u32 i = GCCellOf(b, a);

        if (b->flags[i] != 0) {
                return;
        }

        PROF_FREE(a);

        MemoryUsed   = max(MemoryUsed - (isize)b->cell, 0);
        b->taken[i]  = 0;
        b->marks[i]  = 0;
        b->used     -= 1;

        if (ty->blocks.cur[b->cls] == b && i < b->cursor) {
                b->cursor = i;
        }
}

static bool
block_cell_valid(GCBlock const *b, Alloc const *a)
{
        if (b->ncells == 0 || (char const *)a < b->cells) {
                return false;
        }

        u32 i = GCCellOf(b, a);

        return (i < b->ncells)
            && ((usize)((char const *)a - b->cells) == (usize)i * b->cell)
            && (b->taken[i] != 0);
}

static void const *
owned_buffer(Alloc const *a)
{
        void const *p = a->data;

        switch (a->type) {
        case GC_ARRAY: return ((Array const *)p)->items;
        case GC_BLOB:  return ((Blob const *)p)->items;
        case GC_QUEUE: return ((Queue const *)p)->items;
        case GC_DICT:  return ((Dict const *)p)->items;
        case GC_SET:   return ((Set const *)p)->items;
        case GC_HEAP:  return ((Heap const *)p)->xs.items;
        default:       return NULL;
        }
}

static Alloc *
buffer_alloc_of(Alloc const *a)
{
        void const *buf = owned_buffer(a);

        if (buf == NULL) {
                return NULL;
        }

        Alloc *buf_a = ALLOC_OF(buf);

        if (!InGCBlocks(buf_a) || !block_cell_valid(GCBlockOf(buf_a), buf_a)) {
                return NULL;
        }

        return buf_a;
}

void
GCMarkPinned(Ty *ty, AllocList *pinned)
{
        usize n = 0;

        for (usize i = 0; i < vN(*pinned); ++i) {
                Alloc *a = v__(*pinned, i);
                if (atomic_load_explicit(&a->hard, memory_order_relaxed) != 0) {
                        if (!GCGen) {
                                gc_mark_alloc(a, ty->gc_owner);
                                if (InGCBlocks(a)) {
                                        Alloc *owned = buffer_alloc_of(a);
                                        if (owned != NULL) {
                                                gc_mark_alloc(owned, ty->gc_owner);
                                        }
                                }

                        }
                        *v_(*pinned, n++) = a;
                }
        }

        vN(*pinned) = n;
}

inline static u8 *
cell_mark(Alloc const *a)
{
        GCBlock *b = GCBlockOf(a);
        return &b->marks[GCCellOf(b, a)];
}

static void
pin_young(AllocList *young, Alloc *a)
{
        if (a != NULL && InGCBlocks(a) && *cell_mark(a) == 0) {
                *cell_mark(a) = 1;
                xvP(*young, a);
        }
}

void
GCPinYoung(Ty *ty, AllocList const *pinned, AllocList *young)
{
        for (usize i = 0; i < vN(*pinned); ++i) {
                Alloc *a = v__(*pinned, i);
                if (
                        (atomic_load_explicit(&a->hard, memory_order_relaxed) != 0)
                     && InGCBlocks(a)
                     && (GCBlockOf(a)->owner == ty->gc_owner)
                ) {
                        pin_young(young, buffer_alloc_of(a));
                        pin_young(young, a);
                }
        }
}

void
GCUnpinYoung(AllocList *young)
{
        for (usize i = 0; i < vN(*young); ++i) {
                *cell_mark(v__(*young, i)) = 0;
        }

        v0(*young);
}

Alloc *
GCBufferOwner(Ty *ty, Alloc const *buf)
{
        GCBlock const *b = GCBlockOf(buf);
        Alloc *o = (Alloc *)(GCBlockBase + ((uptr)b->refs[GCCellOf(b, buf)] << 4));

        if (
                !block_registered(ty, o)
             || (*cell_mark(o) == 0)
             || (owned_buffer(o) != buf->data)
        ) {
                return NULL;
        }

        return o;
}

static void
rescan_range(Ty *ty, char *lo, char *hi)
{
        char *next;

        for (char *at = (char *)((uptr)lo & ~(uptr)(GC_BLOCK_SIZE - 1)); at < hi; at = next) {
                GCBlock *b = GCBlockOf(at);
                char    *s = (lo > b->cells) ? lo : b->cells;
                char    *e = b->cells + ((usize)b->units << GC_BLOCK_SHIFT);

                next = (e > at + GC_BLOCK_SIZE) ? e : at + GC_BLOCK_SIZE;
                e    = (hi < e) ? hi : e;

                if (b->ncells == 0 || b->owner != ty->gc_owner || s >= e || b->old == 0) {
                        continue;
                }

                u32 j = (b->cls == GC_BLOCK_LARGE) ? 1 : min(GCCellOf(b, e - 1) + 1, b->ncells);

                for (u32 i = GCCellOf(b, s); i < j; ++i) {
                        Alloc const *a = (Alloc const *)(b->cells + (usize)i * b->cell);
                        if (b->marks[i] != 0 && retraced(a)) {
                                xvP(Dirty.old, ((struct page_region) {
                                        .start      = (uptr)s,
                                        .end        = (uptr)e,
                                        .categories = (uptr)a
                                }));
                        }
                }
        }
}

static void
clear_cache(GCBlockCache const *bc)
{
        for (usize i = 0; i < vN(bc->all); ++i) {
                memset(v__(bc->all, i)->marks, 0, v__(bc->all, i)->ncells);
        }

        for (usize i = 0; i < vN(bc->large); ++i) {
                v__(bc->large, i)->marks[0] = 0;
        }
}

static void
clear_list(AllocList const *list)
{
        for (usize i = 0; i < vN(*list); ++i) {
                A_STORE(&v__(*list, i)->mark, A_LOAD(&v__(*list, i)->mark) & ~1);
        }
}

static void
retrace_list(Ty *ty, AllocList const *list)
{
        for (usize i = 0; i < vN(*list); ++i) {
                Alloc *a = v__(*list, i);
                if (A_LOAD(&a->mark) & 1) {
                        GCRetrace(ty, a, NULL, (char *)-1);
                }
        }
}

static void
retrace_cells(Ty *ty, AllocList const *list)
{
        for (usize i = 0; i < vN(*list); ++i) {
                Alloc *a = v__(*list, i);
                if (*cell_mark(a) != 0) {
                        GCRetrace(ty, a, NULL, (char *)-1);
                }
        }
}

void
GCClearMarks(Ty *ty)
{
        ThreadGroup *group = ty->group;

        for (usize i = 0; i < vN(group->TyList); ++i) {
                Ty const *t = v__(group->TyList, i);
                clear_cache(&t->blocks);
                clear_list(&t->allocs);
                clear_list(&t->old);
                clear_list(&t->special);
        }

        TySpinLockLock(&group->DLock);
        clear_cache(&group->DeadBlocks);
        clear_list(&group->DeadAllocs);
        TySpinLockUnlock(&group->DLock);
}

bool
GCPrepare(Ty *ty, bool minor)
{
        ThreadGroup *group = ty->group;
        bool         scan  = GCMinorOK(ty) && (2 * group->GCLive >= GC_MINOR_MIN);

        Dirty.taint = false;

        if (minor && !(scan && dirty_scan(ty, true))) {
                minor = false;
                scan  = false;
        }

        if (!minor) {
                if (scan) {
                        dirty_scan(ty, false);
                }
                vN(ty->marking) = 0;
                GCClearMarks(ty);
                return false;
        }

        for (usize i = 0; i < vN(group->TyList); ++i) {
                Ty const *t = v__(group->TyList, i);
                retrace_list(ty, &t->special);
                retrace_cells(ty, &t->cleanup);
        }

        TySpinLockLock(&group->DLock);
        retrace_list(ty, &group->DeadAllocs);
        retrace_cells(ty, &group->DeadCleanup);
        TySpinLockUnlock(&group->DLock);

        return true;
}

noreturn static void
verify_failed(Alloc const *a, Alloc const *owner)
{
        fprintf(
                stderr,
                "GC verify: %p (type %d, size %u) reachable but unmarked after minor GC\n",
                (void *)a,
                a->type,
                a->size
        );

        if (owner != NULL) {
                fprintf(stderr, "  recorded owner %p (type %d)\n", (void *)owner, owner->type);
        }

        abort();
}

static void
snap_cache(byte_vector *snap, GCBlockCache const *bc, bool check)
{
        GCBlockList const *lists[] = { &bc->all, &bc->large };

        for (usize k = 0; k < countof(lists); ++k) {
                for (usize i = 0; i < vN(*lists[k]); ++i) {
                        GCBlock *b = v__(*lists[k], i);
                        u32      n = (b->cls == GC_BLOCK_LARGE) ? 1 : b->ncells;
                        for (u32 c = 0; c < n; ++c) {
                                if (!check) {
                                        xvP(*snap, b->marks[c]);
                                        continue;
                                }
                                char was = v__(*snap, snap->count++);
                                if (b->marks[c] && b->taken[c] && !was) {
                                        verify_failed(
                                                (Alloc *)(b->cells + (usize)c * b->cell),
                                                (Alloc *)(GCBlockBase + ((uptr)b->refs[c] << 4))
                                        );
                                }
                                b->marks[c] = was;
                        }
                }
        }
}

static void
snap_list(byte_vector *snap, AllocList const *list, bool check)
{
        for (usize i = 0; i < vN(*list); ++i) {
                Alloc *a = v__(*list, i);
                u8            m = A_LOAD(&a->mark);
                if (!check) {
                        xvP(*snap, m);
                        continue;
                }
                char was = v__(*snap, snap->count++);
                if ((m & 1) && !(was & 1)) {
                        verify_failed(a, NULL);
                }
                A_STORE(&a->mark, was);
        }
}

void
GCSnapshot(Ty *ty, byte_vector *snap, bool check)
{
        ThreadGroup *group = ty->group;

        snap->count = 0;

        for (usize i = 0; i < vN(group->TyList); ++i) {
                Ty const *t = v__(group->TyList, i);
                snap_cache(snap, &t->blocks, check);
                snap_list(snap, &t->allocs, check);
                snap_list(snap, &t->old, check);
                snap_list(snap, &t->special, check);
        }

        snap_cache(snap, &group->DeadBlocks, check);
        snap_list(snap, &group->DeadAllocs, check);
}

bool
GCMinorOK(Ty *ty)
{
        return Dirty.ok && (atomic_load(&GCIsolatedGroups) == 0);
}

inline static void
work_signal(void)
{
        atomic_store_explicit(
                &GCShareWanted,
                Pool.active && (Pool.idle > 0) && (vN(Pool.work) == 0),
                memory_order_relaxed
        );

        if (vN(Pool.work) > 0 && Pool.idle > 0) {
                TyCondVarSignal(&Pool.cv);
        }

        TyCondVarBroadcast(&Pool.done);
}

static void
work_take(Ty *ty)
{
        usize k = min(vN(Pool.work), (usize)GC_TAKE);

        xvPn(ty->marking, vv(Pool.work) + vN(Pool.work) - k, k);
        vN(Pool.work) -= k;
}

void
GCShare(Ty *ty)
{
        usize k    = vN(ty->marking) / 2;
        bool  deep = (ty->gc_helper != NULL) && (vN(ty->marking) > GC_MARK_DEEP);

        if (
                (k < GC_SHARE_MIN)
             || (ty->gc_owner != Pool.owner)
             || !(deep || atomic_load_explicit(&GCShareWanted, memory_order_relaxed))
        ) {
                return;
        }

        TyMutexLock(&Pool.lock);
        xvPn(Pool.work, vv(ty->marking), k);
        memmove(
                vv(ty->marking),
                vv(ty->marking) + k,
                (vN(ty->marking) - k) * sizeof (GCWork)
        );
        vN(ty->marking) -= k;
        work_signal();
        TyMutexUnlock(&Pool.lock);
}

static TyThreadReturnValue
mark_helper(void *ctx)
{
        GCHelper *h = ctx;

        TyMutexLock(&Pool.lock);

        for (;;) {
                if (Pool.active && vN(Pool.work) > 0) {
                        work_take(&h->ty);
                        work_signal();
                        TyMutexUnlock(&Pool.lock);
                        GCDrain(&h->ty);
                        TyMutexLock(&Pool.lock);
                        xvPv(Pool.generic, h->generic);
                        v0(h->generic);
                        continue;
                }
                Pool.idle += 1;
                work_signal();
                TyCondVarWait(&Pool.cv, &Pool.lock);
                Pool.idle -= 1;
        }

        return TY_THREAD_OK;
}

static void
work_fork(void)
{
        TyMutexInit(&Pool.lock);
        TyCondVarInit(&Pool.cv);
        TyCondVarInit(&Pool.done);
        Pool.n      = 0;
        Pool.idle   = 0;
        Pool.active = false;
        atomic_store(&Pool.busy, false);
        atomic_store(&GCShareWanted, false);
}

static int
helper_count(void)
{
        char const *knob = getenv("TY_GC_THREADS");
        long        n    = sysconf(_SC_NPROCESSORS_ONLN) - 1;

        n = (knob != NULL) ? atol(knob) : min(n, 7L);

        return (int)max(0L, min(n, (long)GC_HELPERS_MAX));
}

bool
GCParallelBegin(Ty *ty, bool minor)
{
        bool idle = false;

        if (Pool.want < 0) {
                Pool.want = helper_count();
                TyMutexInit(&Pool.lock);
                TyCondVarInit(&Pool.cv);
                TyCondVarInit(&Pool.done);
                pthread_atfork(NULL, NULL, work_fork);
        }

        if (
                (Pool.want == 0)
             || ((minor ? ty->group->GCPromoted : GCHeap(ty->group)) < GC_PAR_MIN)
             || !atomic_compare_exchange_strong(&Pool.busy, &idle, true)
        ) {
                return false;
        }

        TyMutexLock(&Pool.lock);

        while (Pool.n < Pool.want) {
                GCHelper *h = mrealloc(NULL, sizeof *h);
                memset(h, 0, sizeof *h);
                h->ty.gc_helper = &h->generic;
                xvR(h->ty.marking, 8 * GC_MARK_DEEP);
                xvR(h->generic, GC_TAKE);
                xvR(h->ty.cleanup, GC_TAKE);
                if (TyThreadCreate(&h->thread, mark_helper, h) != 0) {
                        xvF(h->ty.marking);
                        xvF(h->generic);
                        xvF(h->ty.cleanup);
                        xmF(h);
                        Pool.want = Pool.n;
                        break;
                }
                Pool.helpers[Pool.n++] = h;
        }

        if (Pool.n == 0) {
                TyMutexUnlock(&Pool.lock);
                atomic_store(&Pool.busy, false);
                return false;
        }

        for (int i = 0; i < Pool.n; ++i) {
                Pool.helpers[i]->ty.gc_owner = ty->gc_owner;
        }

        xvR(Pool.work, 32 * GC_MARK_DEEP);

        Pool.owner = ty->gc_owner;

        Pool.active = true;
        work_signal();

        TyMutexUnlock(&Pool.lock);

        return true;
}

void
GCParallelEnd(Ty *ty)
{
        TyMutexLock(&Pool.lock);

        for (;;) {
                if (vN(Pool.work) > 0) {
                        work_take(ty);
                } else if (vN(Pool.generic) > 0) {
                        xvPv(ty->marking, Pool.generic);
                        v0(Pool.generic);
                } else if (Pool.idle == Pool.n) {
                        break;
                } else {
                        TyCondVarWait(&Pool.done, &Pool.lock);
                        continue;
                }
                work_signal();
                TyMutexUnlock(&Pool.lock);
                GCDrain(ty);
                TyMutexLock(&Pool.lock);
        }

        Pool.active = false;
        work_signal();

        for (int i = 0; i < Pool.n; ++i) {
                xvPv(ty->cleanup, Pool.helpers[i]->ty.cleanup);
                v0(Pool.helpers[i]->ty.cleanup);
        }

        TyMutexUnlock(&Pool.lock);

        atomic_store(&Pool.busy, false);
}

bool
GCBlockLive(Ty *ty, Alloc const *a)
{
        return block_registered(ty, a);
}

void
GCTrackDynamic(Ty *ty, void const *obj)
{
        Alloc *a = ALLOC_OF(obj);

        if (InGCBlocks(a)) {
                GCTrackCleanup(ty, a);
        }
}

static bool
block_registered(Ty *ty, Alloc const *a)
{
        GCBlock const *b = GCBlockOf(a);

        if (b->owner != ty->gc_owner || (char const *)a < b->cells || b->ncells == 0) {
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
        u32 t = v->type & 63;

        if (
                (v->src == 0)
             && (
                        ((GC_INERT_VALUES >> t) & 1)
                     || ((t == VALUE_PTR) && (v->gcptr == NULL))
                     || GCFrozen(v)
                )
        ) {
                return;
        }

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

typedef struct {
        Ty           *ty;
        void const  **from;
        void        **to;
        usize         mask;
        usize         n;
        Value         bad;
        bool          failed;
} Freezer;

static vec(void const *) FrozenArenas;

inline static usize
freeze_slot(void const *p, usize mask)
{
        return ((uptr)p >> 4) * 0x9E3779B97F4A7C15ULL >> 32 & mask;
}

static void *
freeze_find(Freezer const *f, void const *p)
{
        for (usize i = freeze_slot(p, f->mask);; i = (i + 1) & f->mask) {
                if (f->from[i] == p) {
                        return f->to[i];
                }
                if (f->from[i] == NULL) {
                        return NULL;
                }
        }
}

static void
freeze_link(Freezer *f, void const *p, void *q)
{
        if (2 * (f->n + 1) > f->mask) {
                usize        mask = 2 * f->mask + 1;
                void const **from = xmA((mask + 1) * sizeof *from);
                void       **to   = xmA((mask + 1) * sizeof *to);
                memset(from, 0, (mask + 1) * sizeof *from);
                for (usize i = 0; i <= f->mask; ++i) {
                        if (f->from[i] != NULL) {
                                usize j = freeze_slot(f->from[i], mask);
                                while (from[j] != NULL) {
                                        j = (j + 1) & mask;
                                }
                                from[j] = f->from[i];
                                to[j]   = f->to[i];
                        }
                }
                xmF(f->from);
                xmF(f->to);
                f->from = from;
                f->to   = to;
                f->mask = mask;
        }

        usize i = freeze_slot(p, f->mask);

        while (f->from[i] != NULL) {
                i = (i + 1) & f->mask;
        }

        f->from[i] = p;
        f->to[i]   = q;
        f->n      += 1;
}

static void *
frozen_alloc(usize n, char type)
{
        Alloc *a = ty_malloc(sizeof *a + max(n, 1));

        if (UNLIKELY(a == NULL)) {
                panic("Out of memory!");
        }

        a->size = n;
        a->type = type;
        atomic_init(&a->mark, GC_FROZEN);
        atomic_init(&a->hard, 0);

        return a->data;
}

inline static bool
frozen_ptr(void const *p)
{
        return (p != NULL)
            && !InGCBlocks(ALLOC_OF(p))
            && (atomic_load_explicit(&ALLOC_OF(p)->mark, memory_order_relaxed) == GC_FROZEN);
}

static void *
frozen_copy(Freezer *f, void const *p, char type)
{
        void *q = freeze_find(f, p);

        if (q == NULL) {
                usize n = ALLOC_OF(p)->size;
                q = frozen_alloc(n, type);
                memcpy(q, p, n);
                freeze_link(f, p, q);
        }

        return q;
}

static void
freeze_src(Ty *ty, u32 src)
{
        void const *arena = source_arena(ty, src);
        Expr const *e     = source_lookup(ty, src);
        void const *key   = (e != NULL && e->mod != NULL) ? (void const *)e->mod : arena;

        for (usize i = 0; i < vN(FrozenArenas); ++i) {
                if (v__(FrozenArenas, i) == key) {
                        return;
                }
        }

        xvP(FrozenArenas, key);

        Value v = NIL;
        v.src   = src;
        gc_immortalize(ty, &v);
}

static Value
freeze(Freezer *f, Value v);

static void
freeze_values(Freezer *f, Value *xs, usize n)
{
        for (usize i = 0; i < n && !f->failed; ++i) {
                xs[i] = freeze(f, xs[i]);
        }
}

static Dict *
freeze_dict(Freezer *f, Dict *d)
{
        Ty   *ty  = f->ty;
        Dict *out = freeze_find(f, d);

        if (out != NULL) {
                return out;
        }

        out = frozen_alloc(sizeof (Dict), GC_DICT);
        memset(out, 0, sizeof *out);
        freeze_link(f, d, out);

        Dict *tmp = dict_new(ty);
        Value root = DICT(tmp);

        gP(&root);

        for (DictItem *it = d->first; it != NULL && !f->failed; it = it->next) {
                Value k = freeze(f, it->k);
                Value x = freeze(f, it->v);
                dict_put_value(ty, tmp, k, x);
        }

        out->dflt = freeze(f, d->dflt);

        if (tmp->items != NULL) {
                usize     n     = tmp->size * sizeof (DictItem);
                DictItem *items = frozen_alloc(n, GC_BUF_DICT);
                isize     delta = (char *)items - (char *)tmp->items;
                memcpy(items, tmp->items, n);
                for (usize i = 0; i < tmp->size; ++i) {
                        DictItem *it = &items[i];
                        it->prev = (it->prev != NULL) ? (DictItem *)((char *)it->prev + delta) : NULL;
                        it->next = (it->next != NULL) ? (DictItem *)((char *)it->next + delta) : NULL;
                }
                out->items = items;
                out->first = (tmp->first != NULL) ? (DictItem *)((char *)tmp->first + delta) : NULL;
                out->last  = (tmp->last  != NULL) ? (DictItem *)((char *)tmp->last  + delta) : NULL;
        }

        out->size  = tmp->size;
        out->count = tmp->count;
        out->tombs = tmp->tombs;

        gX();

        return out;
}

static Set *
freeze_set(Freezer *f, Set *s)
{
        Ty  *ty  = f->ty;
        Set *out = freeze_find(f, s);

        if (out != NULL) {
                return out;
        }

        out = frozen_alloc(sizeof (Set), GC_SET);
        memset(out, 0, sizeof *out);
        freeze_link(f, s, out);

        Set  *tmp  = set_new(ty);
        Value root = SET(tmp);

        gP(&root);

        for (SetItem *it = s->first; it != NULL && !f->failed; it = it->next) {
                set_add(ty, tmp, freeze(f, it->k));
        }

        if (tmp->items != NULL) {
                usize    n     = tmp->size * sizeof (SetItem);
                SetItem *items = frozen_alloc(n, GC_BUF_SET);
                isize    delta = (char *)items - (char *)tmp->items;
                memcpy(items, tmp->items, n);
                for (usize i = 0; i < tmp->size; ++i) {
                        SetItem *it = &items[i];
                        it->prev = (it->prev != NULL) ? (SetItem *)((char *)it->prev + delta) : NULL;
                        it->next = (it->next != NULL) ? (SetItem *)((char *)it->next + delta) : NULL;
                }
                out->items = items;
                out->first = (tmp->first != NULL) ? (SetItem *)((char *)tmp->first + delta) : NULL;
                out->last  = (tmp->last  != NULL) ? (SetItem *)((char *)tmp->last  + delta) : NULL;
        }

        out->size  = tmp->size;
        out->count = tmp->count;
        out->tombs = tmp->tombs;

        gX();

        return out;
}

static Value
freeze_fail(Freezer *f, Value v)
{
        if (!f->failed) {
                f->failed = true;
                f->bad    = v;
        }

        return v;
}

static Value
freeze(Freezer *f, Value v)
{
        u32 t = v.type & ~VALUE_TAGGED;

        if (f->failed) {
                return v;
        }

        if (v.src != 0) {
                freeze_src(f->ty, v.src);
        }

        if ((GC_INERT_VALUES >> (t & 63)) & 1) {
                return v;
        }

        switch (t) {
        case VALUE_STRING:
                if (!v.ro && v.str0 != NULL && !frozen_ptr(v.str0)) {
                        u8 *str0 = frozen_copy(f, v.str0, GC_STRING);
                        v.str    = str0 + (v.str - v.str0);
                        v.str0   = str0;
                }
                return v;

        case VALUE_TUPLE:
                if (v.items != NULL && !frozen_ptr(v.items)) {
                        bool   seen  = (freeze_find(f, v.items) != NULL);
                        Value *items = frozen_copy(f, v.items, GC_TUPLE);
                        if (!seen) {
                                freeze_values(f, items, ALLOC_OF(items)->size / sizeof (Value));
                        }
                        v.items = items;
                }
                if (v.ids != NULL && !frozen_ptr(v.ids)) {
                        v.ids = frozen_copy(f, v.ids, GC_IDS);
                }
                return v;

        case VALUE_ARRAY:
                if (!frozen_ptr(v.array)) {
                        Array *a = freeze_find(f, v.array);
                        if (a == NULL) {
                                a = frozen_alloc(sizeof (Array), GC_ARRAY);
                                freeze_link(f, v.array, a);
                                a->count    = v.array->count;
                                a->capacity = v.array->count;
                                a->items    = NULL;
                                if (a->count > 0) {
                                        a->items = frozen_alloc(a->count * sizeof (Value), GC_BUF_VALUES);
                                        memcpy(a->items, v.array->items, a->count * sizeof (Value));
                                        freeze_values(f, a->items, a->count);
                                }
                        }
                        v.array = a;
                }
                return v;

        case VALUE_BLOB:
                if (!frozen_ptr(v.blob)) {
                        Blob *b = freeze_find(f, v.blob);
                        if (b == NULL) {
                                b = frozen_alloc(sizeof (Blob), GC_BLOB);
                                freeze_link(f, v.blob, b);
                                b->count    = v.blob->count;
                                b->capacity = v.blob->count;
                                b->items    = NULL;
                                if (b->count > 0) {
                                        b->items = frozen_alloc(b->count, GC_BUF_BYTES);
                                        memcpy(b->items, v.blob->items, b->count);
                                }
                        }
                        v.blob = b;
                }
                return v;

        case VALUE_DICT:
                if (!frozen_ptr(v.dict)) {
                        v.dict = freeze_dict(f, v.dict);
                }
                return v;

        case VALUE_SET:
                if (!frozen_ptr(v.set)) {
                        v.set = freeze_set(f, v.set);
                }
                return v;

        case VALUE_OBJECT:
                if (frozen_ptr(v.object)) {
                        return v;
                }
                if (
                        (v.object->dynamic != NULL)
                     || !IsNone(v.object->class->finalizer)
                ) {
                        return freeze_fail(f, v);
                }
                if (freeze_find(f, v.object) == NULL) {
                        TyObject *o = frozen_copy(f, v.object, GC_OBJECT);
                        freeze_values(f, o->slots, o->nslot);
                }
                v.object = freeze_find(f, v.object);
                return v;

        case VALUE_FUNCTION:
        case VALUE_NATIVE_FUNCTION:
                if (
                        (v.info[FUN_INFO_CAPTURES] != 0)
                     || from_eval(&v)
                     || has_meta(&v)
                     || (v.xinfo != NULL)
                ) {
                        return freeze_fail(f, v);
                }
                return v;

        case VALUE_REGEX:
                return v.regex->gc ? freeze_fail(f, v) : v;

        case VALUE_PTR:
                return (v.gcptr != NULL) ? freeze_fail(f, v) : v;

        default:
                return freeze_fail(f, v);
        }
}

bool
GCFreeze(Ty *ty, Value const *v, Value *out, Value *bad)
{
        Freezer f = {
                .ty   = ty,
                .mask = 63,
                .from = xmA(64 * sizeof (void const *)),
                .to   = xmA(64 * sizeof (void *))
        };

        memset(f.from, 0, 64 * sizeof (void const *));

        Value x = freeze(&f, *v);

        xmF(f.from);
        xmF(f.to);

        if (f.failed) {
                if (bad != NULL) {
                        *bad = f.bad;
                }
                return false;
        }

        *out = x;

        return true;
}

bool
GCFrozen(Value const *v)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_STRING: return !v->ro && frozen_ptr(v->str0);
        case VALUE_TUPLE:  return frozen_ptr(v->items);
        case VALUE_ARRAY:  return frozen_ptr(v->array);
        case VALUE_BLOB:   return frozen_ptr(v->blob);
        case VALUE_DICT:   return frozen_ptr(v->dict);
        case VALUE_SET:    return frozen_ptr(v->set);
        case VALUE_OBJECT: return frozen_ptr(v->object);
        default:           return false;
        }
}
