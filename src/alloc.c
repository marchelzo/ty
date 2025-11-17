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

Arena
NewArenaGC(Ty *ty, usize cap)
{
        Arena old = A;

        A.base = mAo(cap + RESERVED, GC_ARENA);
        A.beg = A.base + RESERVED;
        A.end = A.base + RESERVED + cap;
        A.gc = true;

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

        A.base = malloc(cap + RESERVED);
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
MarkArena(Arena *a)
{
        if (a == NULL || !a->gc) {
                return;
        }

        MarkArena(NextArena(a));

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
                free(a->base);
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
GetArenaAlloc(Ty *ty)
{
        return (A.gc ? A.base : NULL);
}

static void
ImmortalizeArena(Ty *ty, Arena *a)
{
        if (a == NULL) {
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
