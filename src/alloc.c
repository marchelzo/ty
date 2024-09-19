#include "alloc.h"
#include "gc.h"
#include "panic.h"

#define align (_Alignof(void *))
#define A ty->arena

Arena
NewArenaGC(Ty *ty, size_t cap)
{
        Arena old = A;

        A.base = mAo(cap, GC_ARENA);
        A.gc = true;
        A.beg = A.base;
        A.end = A.base + cap;

        NOGC(A.base);

        return old;
}

Arena
NewArena(Ty *ty, size_t cap)
{
        Arena old = A;

        A.base = malloc(cap);
        A.gc = false;

        if (A.base == NULL) {
                panic("out of memory: couldn't allocate new %zu-byte arena", cap);
        }

        A.beg = A.base;
        A.end = A.base + cap;

        return old;
}

void *
Allocate(Ty *ty, size_t n)
{
        ptrdiff_t avail = A.end - A.beg;
        ptrdiff_t padding = -(uintptr_t)A.beg & (align - 1);

        if (n > avail - padding) {
                panic("out of memory: couldn't allocate %zu-byte object in %zu-byte arena. avail=%zu", n, (size_t)(A.end - A.base), (size_t)avail);
        }

        char *p = A.beg + padding;
        A.beg += padding + n;

        return p;
}

void *
Allocate0(Ty *ty, size_t n)
{
        return memset(amA(n), 0, n);
}

void
ReleaseArena(Ty *ty, Arena old)
{
        if (A.gc) {
                OKGC(A.base);
        }

        A = old;
}

void
DestroyArena(Ty *ty, Arena old)
{
        free(A.base);
        A = old;
}

void *
GetArenaAlloc(Ty *ty)
{
        return A.gc ? A.base : NULL;
}

/* vim: set sts=8 sw=8 expandtab: */
