#ifndef ALLOC_H_INCLUDED
#define ALLOC_H_INCLUDED

#include <stdlib.h>
#include "ty.h"
#include "panic.h"
#include "gc.h"

#define Resize(p, n, m) ((p) = memcpy(amA(n), (p), (m)))
#define resize_scratch(p, n, m) ((p) = memcpy(smA(n), (p), (m)))

#define NewArena(n)  NewArena(ty, (n))
#define ReleaseArena(a) ReleaseArena(ty, (a))

Arena
NewArenaNoGC(Ty *ty, size_t cap);

Arena
NewArenaGC(Ty *ty, size_t cap);

inline static Arena *
NextArena(Arena const *a)
{
        return ((Arena *)a->base);
}

inline static void
FreeArena(Arena const *a)
{
        if (a->gc) {
                OKGC(a->base);
        } else if (NextArena(a)->base != NULL) {
                free(a->base);
        }
}

inline static void
(ReleaseArena)(Ty *ty, Arena old)
{
        for (Arena *a = &ty->arena; a->base != NULL; a = NextArena(a)) {
                FreeArena(a);
        }

        ty->arena = old;
}

inline static Arena
(NewArena)(Ty *ty, size_t cap)
{
        return TY_IS_READY ? NewArenaGC(ty, cap) : NewArenaNoGC(ty, cap);
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
