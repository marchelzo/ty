#ifndef ISTAT_H_INCLUDED
#define ISTAT_H_INCLUDED

#include <string.h>
#include <inttypes.h>

#include "vec.h"
#include "ty.h"
#include "xd.h"

enum { ISTAT_BINS = 1024 };

typedef struct {
        void const *i;
        int64_t n;
        int64_t t;
} istat_entry;

typedef vec(istat_entry) istat_bin;

typedef struct {
        istat_bin bins[ISTAT_BINS];
} istat;

inline static istat_entry *
istat_find(istat_bin const *b, void const *ip)
{
        for (int i = 0; i < b->count; ++i) {
                if (ip == b->items[i].i) {
                        return &b->items[i];
                }
        }

        return NULL;
}

static istat_entry *
istat_lookup(istat const *stat, void const *ip)
{
        int i = (uintptr_t)ip % ISTAT_BINS;
        return istat_find(&stat->bins[i], ip);
}

static void
istat_add(istat *stat, void const *ip, int64_t t)
{
        int i = (uintptr_t)ip % ISTAT_BINS;

        istat_entry *e = istat_find(&stat->bins[i], ip);

        if (e == NULL) {
                xvP(stat->bins[i], ((istat_entry) {
                        .i = ip,
                        .n = 1,
                        .t = t
                }));
        } else {
                e->t += t;
                e->n += 1;
        }
}

inline static void
istat_count(istat const *stat, int64_t *max_ticks, int64_t *total_ticks)
{
        *max_ticks = 0;
        *total_ticks = 0;

        for (int i = 0; i < ISTAT_BINS; ++i) {
                istat_bin const *b = &stat->bins[i];
                for (int i = 0; i < b->count; ++i) {
                        *total_ticks += b->items[i].t;
                        *max_ticks = max(b->items[i].t, *max_ticks);
                }
        }
}

#endif
/* vim: set sts=8 sw=8 expandtab: */
