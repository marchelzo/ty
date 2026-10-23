#include "alloc.h"
#include "gc.h"
#include "panic.h"

#define align (_Alignof(void *))
#define A ty->arena

enum {
        RESERVED = sizeof (Arena)
};

inline static void
ExpandArena(Ty *ty)
{
        if (A.base == NULL) {
                NewArenaGC(ty, 1 << 20);
        } else {
                usize size = 2 * (A.end - (A.base + RESERVED));
                Arena old = A.gc ? NewArenaGC(ty, size) : NewArenaNoGC(ty, size);
                *NextArena(&A) = old;
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

        return base;
}

Arena
NewArenaGC(Ty *ty, usize cap)
{
        Arena old = A;

        A.base = mAo(cap + RESERVED, GC_ARENA);
        A.beg = A.base + RESERVED;
        A.end = A.base + RESERVED + cap;
        A.gc = true;

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

        A.base = xmA(cap + RESERVED);
        A.gc = false;
        A.immortal = false;

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
        if (a == NULL) {
                return;
        }

        FreeArena(NextArena(a));

        if (a->gc) {
                OKGC(a->base);
        } else {
                xmF(a->base);
        }
}

void *
Allocate(Ty *ty, usize n)
{
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

void *
ArenaResize(Ty *ty, void *p, usize n, usize m)
{
        char *q = p;

        if (q != NULL && q + m == A.beg && n <= (usize)(A.end - q)) {
                A.beg = q + n;
                return q;
        }

        return memcpy(Allocate(ty, n), p, m);
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
