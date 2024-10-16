#ifndef ALLOC_H_INCLUDED
#define ALLOC_H_INCLUDED

#include <stdlib.h>
#include "ty.h"
#include "panic.h"
#include "gc.h"

#define Resize(p, n, m) ((p) = memcpy(amA(n), (p), (m)))
#define resize_scratch(p, n, m) ((p) = memcpy(smA(n), (p), (m)))

Arena
NewArena(Ty *ty, size_t cap);

Arena
NewArenaGC(Ty *ty, size_t cap);

void *
GetArenaAlloc(Ty *ty);

void
DestroyArena(Ty *ty, Arena arena);

void
ReleaseArena(Ty *ty, Arena old);

void *
Allocate(Ty *ty, size_t n);

void *
Allocate0(Ty *ty, size_t n);

void *
AllocateScratch(Ty *ty, size_t n);

#endif
