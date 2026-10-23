#ifndef VMEM_H_INCLUDED
#define VMEM_H_INCLUDED

#include "defs.h"
#include "vec.h"
#include "ty/thread.h"

typedef struct vpool {
        usize       slot;
        usize       span;
        bool        guard;
        TyMutex     lock;
        vec(void *) free;
        char       *next;
        char       *end;
} VPool;

#ifdef _WIN32
#define VPOOL(n, m, g) { .slot = (n), .span = (m), .guard = (g) }
#else
#define VPOOL(n, m, g) { .slot = (n), .span = (m), .guard = (g), .lock = TY_MUTEX_INIT }
#endif

usize
VPage(void);

void *
VMap(usize n);

void
VDrop(void *p, usize n);

void *
VPoolTake(VPool *p);

void
VPoolPut(VPool *p, void *slot);

void
VNoHugePages(void);

#endif
