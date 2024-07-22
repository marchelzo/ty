#ifndef ALLOC_H_INCLUDED
#define ALLOC_H_INCLUDED

#include <stdlib.h>
#include "panic.h"
#include "gc.h"

#define Resize(p, n, m) ((p) = memcpy(Allocate(n), (p), (m)))

typedef struct arena {
	char *base;
	char *beg;
	char *end;
	bool gc;
} Arena;

Arena NewArena(size_t cap);
Arena NewArenaGC(size_t cap);
void *GetArenaAlloc(void);
void DestroyArena(Arena arena);
void ReleaseArena(Arena old);

void *Allocate(size_t n);

#endif
