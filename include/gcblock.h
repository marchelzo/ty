#ifndef GCBLOCK_H_INCLUDED
#define GCBLOCK_H_INCLUDED

#include "defs.h"
#include "vec.h"

enum {
        GC_BLOCK_SHIFT   = 16,
        GC_BLOCK_SIZE    = 1 << GC_BLOCK_SHIFT,
        GC_BLOCK_CLASSES = 32,
        GC_BLOCK_CELL    = 32768,
        GC_BLOCK_MAPS    = 16384,
        GC_BLOCK_LARGE   = 0xFF,
        GC_BLOCK_CONT    = 0xFE
};

typedef struct gc_block {
        u8    owner;
        u8    cls;
        u8    wp;
        u8    age;
        u32   cell;
        u32   ncells;
        u32   used;
        u32   old;
        u32   cursor;
        u32   units;
        u64   magic;
        u8   *marks;
        u8   *taken;
        u8   *flags;
        u32  *refs;
        char *cells;
        void *home;
} GCBlock;

typedef vec(GCBlock *) GCBlockList;

typedef struct {
        GCBlock     *cur[GC_BLOCK_CLASSES];
        GCBlockList  partial[GC_BLOCK_CLASSES];
        GCBlockList  all;
        GCBlockList  large;
} GCBlockCache;

extern uptr     GCBlockBase;
extern usize    GCBlockSpan;
extern GCBlock *GCBlockMeta;
extern u8       GCBlockClass[GC_BLOCK_CELL / 16 + 1];
extern bool     GCGen;

[[gnu::always_inline]]
inline static bool
InGCBlocks(void const *p)
{
        return ((uptr)p - GCBlockBase) < GCBlockSpan;
}

[[gnu::always_inline]]
inline static GCBlock *
GCBlockAt(void const *p)
{
        return &GCBlockMeta[((uptr)p - GCBlockBase) >> GC_BLOCK_SHIFT];
}

[[gnu::always_inline]]
inline static GCBlock *
GCBlockOf(void const *p)
{
        GCBlock *b = GCBlockAt(p);
        return UNLIKELY(b->cls == GC_BLOCK_CONT) ? GCBlockAt(b->cells) : b;
}

[[gnu::always_inline]]
inline static u32
GCCellOf(GCBlock const *b, void const *p)
{
        return (u32)((((u64)((char const *)p - b->cells)) * b->magic) >> 32);
}

[[gnu::always_inline]]
inline static u32
GCBlockRef(void const *p)
{
        return (u32)(((uptr)p - GCBlockBase) >> 4);
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
