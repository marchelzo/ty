#ifndef GC_H_INCLUDED
#define GC_H_INCLUDED

enum {
        GC_NONE,
        GC_MARK,
        GC_HARD,
};

extern int gc_prevent;

void *
gc_alloc(size_t n);

void
gc_reset(void);

#endif
