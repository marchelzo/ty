#ifndef INTERN_H_INCLUDED
#define INTERN_H_INCLUDED

#include <string.h>
#include <inttypes.h>

#include "ty.h"

inline static void
intern_init(InternSet *set)
{
        memset(set, 0, sizeof *set);
}

InternEntry *
intern_get(InternSet *set, char const *s);

InternEntry *
intern_put(InternEntry *e, void *data);

inline static InternEntry *
intern(InternSet *set, char const *s)
{
        InternEntry *e = intern_get(set, s);
        return (e->id >= 0) ? e : intern_put(e, NULL);
}

inline static InternEntry *
intern_entry(InternSet *set, i64 id)
{
        u32 key = set->index.items[id];
        InternBucket *b = &set->set[key & 0xFF];
        return &b->items[key >> 8u];
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
