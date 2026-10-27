#ifndef GCBLOCK_H_INCLUDED
#define GCBLOCK_H_INCLUDED

#include "defs.h"
#include "vec.h"

enum {
        GC_BLOCK_SHIFT   = 16,
        GC_BLOCK_SIZE    = 1 << GC_BLOCK_SHIFT,
        GC_BLOCK_CLASSES = 15,
        GC_BLOCK_CELL    = 512
};

typedef struct gc_block {
        u8    owner;
        u8    cls;
        u16   cell;
        u32   ncells;
        u32   used;
        u32   cursor;
        u64   magic;
        u8   *marks;
        u8   *taken;
        char *cells;
} GCBlock;

typedef vec(GCBlock *) GCBlockList;

typedef struct {
        GCBlock     *cur[GC_BLOCK_CLASSES];
        GCBlockList  partial[GC_BLOCK_CLASSES];
        GCBlockList  all;
} GCBlockCache;

extern uptr      GCBlockBase;
extern usize     GCBlockSpan;
extern u8  const GCBlockClass[GC_BLOCK_CELL / 16 + 1];

[[gnu::always_inline]]
inline static bool
InGCBlocks(void const *p)
{
        return ((uptr)p - GCBlockBase) < GCBlockSpan;
}

[[gnu::always_inline]]
inline static GCBlock *
GCBlockOf(void const *p)
{
        return (GCBlock *)((uptr)p & ~(uptr)(GC_BLOCK_SIZE - 1));
}

[[gnu::always_inline]]
inline static u32
GCCellOf(GCBlock const *b, void const *p)
{
        return (u32)((((u64)((char const *)p - b->cells)) * b->magic) >> 32);
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
