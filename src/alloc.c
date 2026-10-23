#include <stdatomic.h>

#include "alloc.h"
#include "gc.h"
#include "panic.h"
#include "compiler.h"

#define align (_Alignof(void *))
#define A ty->arena

#if defined(TY_SYSMALLOC)
typedef struct chunk Chunk;

struct chunk {
        Chunk  *next;
        Chunk **pprev;
        char   *arena;
        u32     node;
        usize   size;
        char    data[];
};

static int LeakMode = -1;

static struct {
        void **slot;
        usize  cap;
        usize  n;
} Live;

#define LIVE_DEAD ((void *)1)

static atomic_flag LiveLock = ATOMIC_FLAG_INIT;

inline static void
live_lock(void)
{
        while (atomic_flag_test_and_set_explicit(&LiveLock, memory_order_acquire)) {
                ;
        }
}

inline static void
live_unlock(void)
{
        atomic_flag_clear_explicit(&LiveLock, memory_order_release);
}

inline static usize
live_hash(void const *p)
{
        return ((uptr)p >> 4) * 0x9E3779B97F4A7C15ULL;
}

static void
live_add(void *p)
{
        live_lock();

        if (2 * (Live.n + 1) > Live.cap) {
                usize   cap  = (Live.cap == 0) ? (1 << 16) : 2 * Live.cap;
                void  **slot = calloc(cap, sizeof *slot);

                for (usize i = 0; i < Live.cap; ++i) {
                        void *q = Live.slot[i];
                        if (q == NULL || q == LIVE_DEAD) {
                                continue;
                        }
                        usize j = live_hash(q) & (cap - 1);
                        while (slot[j] != NULL) {
                                j = (j + 1) & (cap - 1);
                        }
                        slot[j] = q;
                }

                free(Live.slot);
                Live.slot = slot;
                Live.cap  = cap;
        }

        usize i = live_hash(p) & (Live.cap - 1);
        while (Live.slot[i] != NULL && Live.slot[i] != LIVE_DEAD) {
                i = (i + 1) & (Live.cap - 1);
        }

        Live.slot[i] = p;
        Live.n += 1;

        live_unlock();
}

bool
ChunkIsLive(void const *p);

void
ChunkSetNode(void *p)
{
        if (!LeakMode && ChunkIsLive(p)) {
                ((Chunk *)((char *)p - offsetof(Chunk, data)))->node = 1;
        }
}

bool
ChunkIsNode(void const *p)
{
        return !LeakMode
            && ChunkIsLive(p)
            && ((Chunk const *)((char const *)p - offsetof(Chunk, data)))->node;
}

bool
ChunkIsLive(void const *p)
{
        bool found = false;

        live_lock();

        for (usize i = live_hash(p) & (Live.cap - 1); Live.cap != 0 && Live.slot[i] != NULL; i = (i + 1) & (Live.cap - 1)) {
                if (Live.slot[i] == p) {
                        found = true;
                        break;
                }
        }

        live_unlock();

        return found;
}

static bool
live_del(void const *p)
{
        bool found = false;

        live_lock();

        for (usize i = live_hash(p) & (Live.cap - 1); Live.cap != 0 && Live.slot[i] != NULL; i = (i + 1) & (Live.cap - 1)) {
                if (Live.slot[i] == p) {
                        Live.slot[i] = LIVE_DEAD;
                        found = true;
                        break;
                }
        }

        live_unlock();

        return found;
}

typedef struct {
        Chunk **cs;
        usize   n;
} ChunkSet;

#define CHAIN(base) (*(Chunk **)((base) + sizeof (Arena)))

enum {
        RESERVED = sizeof (Arena) + sizeof (Chunk *)
};
#else
enum {
        RESERVED = sizeof (Arena)
};
#endif

inline static void
ExpandArena(Ty *ty)
{
        if (A.base == NULL) {
                NewArenaGC(ty, 1 << 20);
        } else {
                usize size = 2 * (A.end - (A.base + RESERVED));
                Arena old = A.gc ? NewArenaGC(ty, size) : NewArenaNoGC(ty, size);
                *NextArena(&A) = old;
                A.fmask = old.fmask;
                memcpy(A.free, old.free, sizeof A.free);
        }
}

static struct {
        char const *lo;
        char const *hi;
}                *GcArenas;
static usize      NGcArenas;
static usize      CGcArenas;
static TySpinLock GcArenaLock = TY_MUTEX_INIT;

static usize
ArenaFind(void const *p)
{
        usize lo = 0;
        usize hi = NGcArenas;

        while (lo < hi) {
                usize mid = lo + (hi - lo) / 2;
                if (GcArenas[mid].lo <= (char const *)p) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        return lo;
}

static void
ArenaNote(char const *lo, char const *hi)
{
        TySpinLockLock(&GcArenaLock);

        if (NGcArenas == CGcArenas) {
                CGcArenas = (CGcArenas == 0) ? 64 : 2 * CGcArenas;
                GcArenas  = mrealloc(GcArenas, CGcArenas * sizeof *GcArenas);
        }

        usize i = ArenaFind(lo);

        memmove(GcArenas + i + 1, GcArenas + i, (NGcArenas - i) * sizeof *GcArenas);

        GcArenas[i].lo = lo;
        GcArenas[i].hi = hi;
        NGcArenas += 1;

        TySpinLockUnlock(&GcArenaLock);
}

void
ArenaForget(void const *base)
{
        TySpinLockLock(&GcArenaLock);

        usize i = ArenaFind(base);

        if (i > 0 && GcArenas[i - 1].lo == base) {
                memmove(GcArenas + i - 1, GcArenas + i, (NGcArenas - i) * sizeof *GcArenas);
                NGcArenas -= 1;
        }

        TySpinLockUnlock(&GcArenaLock);
}

void *
ArenaOf(void const *p)
{
        void *base = NULL;

        TySpinLockLock(&GcArenaLock);

        usize i = ArenaFind(p);

        if (i > 0 && (char const *)p < GcArenas[i - 1].hi) {
                base = (void *)GcArenas[i - 1].lo;
        }

        TySpinLockUnlock(&GcArenaLock);

#if defined(TY_SYSMALLOC)
        if (base == NULL && !LeakMode && ChunkIsLive(p)) {
                base = ((Chunk const *)((char const *)p - offsetof(Chunk, data)))->arena;
        }
#endif

        return base;
}

Arena
NewArenaGC(Ty *ty, usize cap)
{
        Arena old = A;

#if defined(TY_SYSMALLOC)
        cap = 0;
#endif

        A.base = mAo(cap + RESERVED, GC_ARENA);
        A.beg = A.base + RESERVED;
        A.end = A.base + RESERVED + cap;
        A.gc = true;
        A.fmask = 0;

        ArenaNote(A.base, A.end);

        memset(A.base, 0, RESERVED);

        NOGC(A.base);

        if (A.immortal) {
                GCForgetObject(ty, A.base);
        }

        return old;
}

Arena
NewArenaNoGC(Ty *ty, usize cap)
{
        Arena old = A;

#if defined(TY_SYSMALLOC)
        cap = 0;
#endif

        A.base = xmA(cap + RESERVED);
        A.gc = false;
        A.immortal = false;
        A.fmask = 0;

        if (UNLIKELY(A.base == NULL)) {
                panic("out of memory: couldn't allocate new %zu-byte arena", cap);
        }

        A.beg = A.base + RESERVED;
        A.end = A.base + RESERVED + cap;

        memset(A.base, 0, RESERVED);

        return old;
}

void
MarkArena(Ty *ty, Arena *a)
{
        if (a == NULL || !a->gc) {
                return;
        }

        MarkArena(ty, NextArena(a));

        MARK(a->base);
}

void
FreeArena(Arena *a)
{
        if (a == NULL || a->base == NULL) {
                return;
        }

        FreeArena(NextArena(a));

        if (a->gc) {
                OKGC(a->base);
        } else {
#if defined(TY_SYSMALLOC)
                for (Chunk *c = CHAIN(a->base), *next; c != NULL; c = next) {
                        next = c->next;
                        live_del(c->data);
                        xmF(c);
                }
#endif
                xmF(a->base);
        }
}

#if defined(TY_SYSMALLOC)
static int
chunkcmp(void const *a, void const *b)
{
        uptr x = (uptr)*(Chunk * const *)a;
        uptr y = (uptr)*(Chunk * const *)b;

        return (x > y) - (x < y);
}

static bool
inchunks(void const *p, void *ctx)
{
        ChunkSet const *set = ctx;
        Chunk * const *cs = set->cs;
        usize lo = 0;
        usize hi = set->n;

        while (lo < hi) {
                usize mid = lo + (hi - lo) / 2;
                if ((uptr)cs[mid]->data <= (uptr)p) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        return (lo > 0)
            && ((uptr)p < (uptr)cs[lo - 1]->data + cs[lo - 1]->size);
}

void
FreeArenaChunks(void *base)
{
        usize n = 0;
        Chunk **cs;

        for (Chunk *c = CHAIN((char *)base); c != NULL; c = c->next) {
                n += 1;
        }

        if (n == 0) {
                return;
        }

        cs = xmA(n * sizeof *cs);
        n  = 0;

        for (Chunk *c = CHAIN((char *)base); c != NULL; c = c->next) {
                cs[n++] = c;
        }

        qsort(cs, n, sizeof *cs, chunkcmp);
        ForgetSourceNodesWhere(inchunks, &(ChunkSet){ cs, n });

        for (usize i = 0; i < n; ++i) {
                live_del(cs[i]->data);
                xmF(cs[i]);
        }

        xmF(cs);
}

void *
Allocate(Ty *ty, usize n)
{
        if (UNLIKELY(LeakMode < 0)) {
                LeakMode = (getenv("TY_ARENA_LEAKS") != NULL);
        }

        if (LeakMode) {
                void *p = malloc(n);
                live_add(p);
                return p;
        }

        if (UNLIKELY(A.base == NULL)) {
                NewArenaGC(ty, 0);
        }

        Chunk *c = ty_malloc(sizeof *c + n);
        if (UNLIKELY(c == NULL)) {
                panic("out of memory: couldn't allocate %zu-byte arena chunk", n);
        }

        c->node       = 0;
        c->size       = n;
        c->arena      = A.base;
        c->next       = CHAIN(A.base);
        c->pprev      = &CHAIN(A.base);
        CHAIN(A.base) = c;

        if (c->next != NULL) {
                c->next->pprev = &c->next;
        }

        live_add(c->data);

        return c->data;
}
void
Release(Ty *ty, void *p, usize n)
{
        if (p == NULL || !live_del(p)) {
                return;
        }

        if (LeakMode) {
                free(p);
                return;
        }

        Chunk *c = (Chunk *)((char *)p - offsetof(Chunk, data));

        *c->pprev = c->next;

        if (c->next != NULL) {
                c->next->pprev = c->pprev;
        }

        xmF(c);
}
#else
inline static int
FreeClassFloor(usize n)
{
        int k = (63 - __builtin_clzll(n)) - 4;
        return (k < ARENA_FREE_CLASSES) ? k : (ARENA_FREE_CLASSES - 1);
}

inline static int
FreeClassCeil(usize n)
{
        return (n <= 16) ? 0 : (64 - __builtin_clzll(n - 1)) - 4;
}

static bool
InArena(Ty *ty, char const *p, usize n)
{
        for (Arena const *a = &A; a != NULL && a->base != NULL; a = NextArena(a)) {
                if (p >= a->base + RESERVED && p + n <= a->end) {
                        return true;
                }
        }

        return false;
}

void
Release(Ty *ty, void *p, usize n)
{
        if (
                (p == NULL)
             || (n < 16)
             || (A.gc && !A.immortal)
             || !InArena(ty, p, n)
        ) {
                return;
        }

        if ((char *)p + n == A.beg) {
                A.beg = p;
                return;
        }

        int k = FreeClassFloor(n);

        *(void **)p = A.free[k];
        A.free[k]   = p;
        A.fmask    |= 1u << k;
}

inline static void *
AllocateFree(Ty *ty, usize n)
{
        int k = FreeClassCeil(n);

        for (int j = k; j < k + 2 && j < ARENA_FREE_CLASSES; ++j) {
                if (A.fmask & (1u << j)) {
                        void *p = A.free[j];
                        A.free[j] = *(void **)p;
                        if (A.free[j] == NULL) {
                                A.fmask &= ~(1u << j);
                        }
                        return p;
                }
        }

        return NULL;
}

void *
Allocate(Ty *ty, usize n)
{
        if (UNLIKELY(A.fmask != 0)) {
                void *p = AllocateFree(ty, n);
                if (p != NULL) {
                        return p;
                }
        }

        for (;;) {
                ptrdiff_t avail = A.end - A.beg;
                ptrdiff_t padding = -(uptr)A.beg & (align - 1);

                if (UNLIKELY(n > avail - padding)) {
                        ExpandArena(ty);
                        continue;
                }

                void *o = A.beg + padding;
                A.beg += padding + n;

                return o;
        }
}
#endif

#if defined(TY_SYSMALLOC)
static vec(void *) Tmp;

void *
AllocateTmp(usize n)
{
        void *p = malloc(n);

        if (UNLIKELY(p == NULL)) {
                panic("out of memory: couldn't allocate %zu-byte temporary", n);
        }

        if (Tmp.count == Tmp.capacity) {
                Tmp.capacity = (Tmp.capacity == 0) ? 4096 : 2 * Tmp.capacity;
                Tmp.items    = realloc(Tmp.items, Tmp.capacity * sizeof *Tmp.items);
        }

        Tmp.items[Tmp.count++] = p;

        return p;
}

TmpMark
TmpSave(void)
{
        return (TmpMark) { .beg = (char *)(uptr)Tmp.count };
}

void
TmpRestore(TmpMark m)
{
        usize n = (usize)(uptr)m.beg;

        while (Tmp.count > n) {
                free(Tmp.items[--Tmp.count]);
        }
}
#else
typedef struct tmpblk TmpBlk;

struct tmpblk {
        TmpBlk *prev;
        char   *beg;
        char   *end;
        char    data[];
};

static TmpBlk *Tmp;

void *
AllocateTmp(usize n)
{
        ptrdiff_t padding;

        for (;;) {
                if (Tmp != NULL) {
                        padding = -(uptr)Tmp->beg & (align - 1);
                        if (n + padding <= (usize)(Tmp->end - Tmp->beg)) {
                                break;
                        }
                }

                usize   cap = max(n + align, (Tmp == NULL) ? (usize)1 << 16 : 2 * (usize)(Tmp->end - Tmp->data));
                TmpBlk *blk = malloc(sizeof *blk + cap);

                if (UNLIKELY(blk == NULL)) {
                        panic("out of memory: couldn't allocate %zu-byte temporary block", cap);
                }

                blk->prev = Tmp;
                blk->beg  = blk->data;
                blk->end  = blk->data + cap;
                Tmp       = blk;
        }

        void *p = Tmp->beg + padding;
        Tmp->beg += padding + n;

        return p;
}

TmpMark
TmpSave(void)
{
        return (TmpMark) {
                .blk = Tmp,
                .beg = (Tmp == NULL) ? NULL : Tmp->beg
        };
}

void
TmpRestore(TmpMark m)
{
        while (Tmp != m.blk) {
                TmpBlk *prev = Tmp->prev;
                free(Tmp);
                Tmp = prev;
        }

        if (Tmp != NULL) {
                Tmp->beg = m.beg;
        }
}
#endif

void *
Reallocate(Ty *ty, void *p, usize old, usize n)
{
#if !defined(TY_SYSMALLOC)
        if (
                (p != NULL)
             && ((char *)p >= A.base)
             && ((char *)p + old == A.beg)
             && (n <= (usize)(A.end - (char *)p))
        ) {
                A.beg = (char *)p + n;
                return p;
        }
#endif

        return memcpy(Allocate(ty, n), p, old);
}

void *
Regrow(Ty *ty, void *p, usize old, usize n)
{
        void *q = Reallocate(ty, p, old, n);

        if (q != p) {
                Release(ty, p, old);
        }

        return q;
}

void *
GetArenaAlloc(Ty *ty)
{
        return (A.gc ? A.base : NULL);
}

static void
ImmortalizeArena(Ty *ty, Arena *a)
{
        if (a == NULL || a->immortal) {
                return;
        }

        ImmortalizeArena(ty, NextArena(a));
        GCForgetObject(ty, a->base);

        a->immortal = true;
}

void
TyImmortalizeArena(Ty *ty)
{
        if (A.gc) {
                ImmortalizeArena(ty, &A);
        }
}

void
DumpArenaStats(Ty *ty)
{
        Arena *a = &A;
        int level = 0;

        while (a->base != NULL) {
                usize used = a->beg - (a->base + RESERVED);
                usize total = a->end - (a->base + RESERVED);

                fprintf(
                        stderr,
                        "Arena Level %d: %s, used %.1f / %.1f MB (%.2f%%)\n",
                        level++,
                        a->gc ? "GC" : "Non-GC",
                        used / 1.0e6,
                        total / 1.0e6,
                        (total == 0) ? 0.0 : ((double)used * 100.0 / (double)total)
                );

                a = NextArena(a);
        }

        fprintf(stderr, "In use by GC: %.1f MB\n", ty->memory_used / 1.0e6);
        fprintf(stderr, "Current GC threshold: %.1f MB\n", ty->memory_limit / 1.0e6);
}

/* vim: set sts=8 sw=8 expandtab: */
