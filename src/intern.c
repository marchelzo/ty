#include <string.h>

#include "ty.h"
#include "intern.h"
#include "vec.h"
#include "util.h"

void const *InternSentinel = &InternSentinel;

inline static InternEntry *
find(InternBucket const *b, char const *name, unsigned long h)
{
        for (int i = 0; i < b->count; ++i) {
                if (b->items[i].hash != h)
                        continue;
                if (strcmp(b->items[i].name, name) == 0)
                        return &b->items[i];
        }

        return NULL;
}

InternEntry *
intern_get(InternSet *set, char const *name)
{
        unsigned long h = StrHash(name);
        InternBucket *b = &set->set[h % INTERN_TABLE_SIZE];

        InternEntry *e = find(b, name, h);

        if (e != NULL) {
                return e;
        }

        xvP(
                *b,
                ((InternEntry){
                        .name = name,
                        .hash = h,
                        .id = -(b + 1 - set->set),
                        .data = set
                })
        );

        return vvX(*b);
}

InternEntry *
intern_put(InternEntry *e, void *data)
{
        InternSet *set = e->data;
        InternBucket *b = &set->set[-e->id - 1];

        e->data = data;
        e->id = set->index.count;
        e->name = sclone_malloc(e->name);

        xvP(set->index, (b->count << 8u) | (b - set->set));

        b->count += 1;

        return e;
}

/* vim: set sts=8 sw=8 expandtab: */
