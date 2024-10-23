#include "alloc.h"
#include "gc.h"
#include "panic.h"

#define align (_Alignof(void *))
#define A ty->arena

enum {
        RESERVED = sizeof (Arena)
};

inline static Arena *
NextArena(Arena const *a)
{
        return ((Arena *)a->base);
}

inline static void
ExpandArena(Ty *ty)
{
        size_t size = 2 * (A.end - (A.base + RESERVED));
        Arena old = A.gc ? NewArenaGC(ty, size) : NewArena(ty, size);
        *NextArena(&A) = old;
}

Arena
NewArenaGC(Ty *ty, size_t cap)
{
        Arena old = A;

        A.base = mAo(cap + RESERVED, GC_ARENA);
        A.gc = true;
        A.beg = A.base + RESERVED;
        A.end = A.base + RESERVED + cap;

        memset(A.base, 0, RESERVED);

        NOGC(A.base);

        return old;
}

Arena
NewArena(Ty *ty, size_t cap)
{
        Arena old = A;

        A.base = malloc(cap + RESERVED);
        A.gc = false;

        if (UNLIKELY(A.base == NULL)) {
                raise(SIGTRAP);
                panic("out of memory: couldn't allocate new %zu-byte arena", cap);
        }

        A.beg = A.base + RESERVED;
        A.end = A.base + RESERVED + cap;

        memset(A.base, 0, RESERVED);

        return old;
}

void *
Allocate(Ty *ty, size_t n)
{
        for (;;) {
                ptrdiff_t avail = A.end - A.beg;
                ptrdiff_t padding = -(uintptr_t)A.beg & (align - 1);

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
Allocate0(Ty *ty, size_t n)
{
        return memset(amA(n), 0, n);
}

void
ReleaseArena(Ty *ty, Arena old)
{
        for (Arena *a = &A; a->base != NULL; a = NextArena(a)) {
                OKGC(a->base);
        }

        A = old;
}

void
DestroyArena(Ty *ty, Arena old)
{
        for (Arena *a = &A; a->base != NULL; a = NextArena(a)) {
                free(a->base);
        }

        A = old;
}

void *
GetArenaAlloc(Ty *ty)
{
        return A.gc ? A.base : NULL;
}

/* vim: set sts=8 sw=8 expandtab: */
