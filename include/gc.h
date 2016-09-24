#ifndef GC_H_INCLUDED
#define GC_H_INCLUDED

#include "vec.h"

#define NOGC(v) ((v)->mark |= GC_HARD)
#define OKGC(v) ((v)->mark &= ~GC_HARD)

enum {
        GC_NONE,
        GC_MARK,
        GC_HARD,
};

void *
gc_alloc(size_t n);

void
gc_reset(void);

void
gc_push(struct value *v);

void
gc_pop(void);

void
gc_clear_root_set(void);

#endif
