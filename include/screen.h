#ifndef SCREEN_H_INCLUDED
#define SCREEN_H_INCLUDED

#include "ty.h"

enum {
        PEN_BOLD    = 1 << 0,
        PEN_DIM     = 1 << 1,
        PEN_ITALIC  = 1 << 2,
        PEN_BLINK   = 1 << 3,
        PEN_REVERSE = 1 << 4,
        PEN_HIDDEN  = 1 << 5,
        PEN_STRIKE  = 1 << 6,
        PEN_OVER    = 1 << 7
};

enum {
        PEN_C16  = 1u << 24,
        PEN_C256 = 2u << 24,
        PEN_RGB  = 3u << 24
};

enum {
        PEN_VOID = 1 << 0
};

#define PEN_SGR_MAX 192

typedef struct {
        u32 fg;
        u32 bg;
        u32 uc;
        u16 at;
        u8  ul;
        u8  fl;
} Pen;

void
pen_sgr(Pen *p, u8 const *s, isize n);

int
pen_diff(char *o, Pen const *a, Pen const *b, bool known);

bool
pen_osc8(u8 const *s, isize n, isize *off, isize *len);

void
screen_free(Ty *ty, void *p);

inline static bool
pen_plain(Pen const *p)
{
        return (p->fg | p->bg | p->uc | p->at | p->ul) == 0;
}

inline static bool
pen_eq(Pen const *a, Pen const *b)
{
        return memcmp(a, b, sizeof *a) == 0;
}

#endif

/* vim: set sw=8 sts=8 expandtab: */
