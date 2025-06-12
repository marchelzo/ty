#ifndef ALLOC_H_INCLUDED
#define ALLOC_H_INCLUDED

#include <stdlib.h>

#include "panic.h"
#include "ty.h"

#define Resize(p, n, m) ((p) = __builtin_memcpy(amA(n), (p), (m)))
#define resize_scratch(p, n, m) ((p) = __builtin_memcpy(smA(n), (p), (m)))

#if 1
#define NewArena(n)  NewArena(ty, (n))
#define ReleaseArena(a) ReleaseArena(ty, (a))
#else
#define NewArena(n)  ((Arena){0})
#define ReleaseArena(a) 0
#endif

Arena
NewArenaNoGC(Ty *ty, size_t cap);

Arena
NewArenaGC(Ty *ty, size_t cap);

inline static Arena *
NextArena(Arena const *a)
{
        return ((Arena *)a->base);
}

static void
MarkArena(Arena *a)
{
        if (a == NULL || !a->gc) {
                return;
        }

        MarkArena(NextArena(a));

        MARK(a->base);
}

static void
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

inline static void
(ReleaseArena)(Ty *ty, Arena old)
{
        FreeArena(&ty->arena);
        ty->arena = old;
}

inline static Arena
(NewArena)(Ty *ty, size_t cap)
{
        return NewArenaGC(ty, cap);
        return TY_IS_READY
             ? NewArenaGC(ty, cap)
             : NewArenaNoGC(ty, cap);
}

void *
GetArenaAlloc(Ty *ty);

void
(ReleaseArena)(Ty *ty, Arena old);

void *
Allocate(Ty *ty, size_t n);

inline static void *
Allocate0(Ty *ty, size_t n)
{
        return memset(Allocate(ty, n), 0, n);
}

void *
AllocateScratch(Ty *ty, size_t n);

#endif
