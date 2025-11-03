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
NewArenaNoGC(Ty *ty, usize cap);

Arena
NewArenaGC(Ty *ty, usize cap);

inline static Arena *
NextArena(Arena const *a)
{
        return ((Arena *)a->base);
}

void
MarkArena(Arena *a);

void
FreeArena(Arena *a);

inline static void
(ReleaseArena)(Ty *ty, Arena old)
{
        FreeArena(&ty->arena);
        ty->arena = old;
}

inline static Arena
(NewArena)(Ty *ty, usize cap)
{
#if 1
        return NewArenaGC(ty, cap);
#else
        return TY_IS_READY ? NewArenaGC(ty, cap)
                           : NewArenaNoGC(ty, cap);
#endif
}

void *
GetArenaAlloc(Ty *ty);

void
TyImmortalizeArena(Ty *ty);

void *
Allocate(Ty *ty, usize n);

inline static void *
Allocate0(Ty *ty, usize n)
{
        return memset(Allocate(ty, n), 0, n);
}

void *
AllocateScratch(Ty *ty, usize n);

#endif
