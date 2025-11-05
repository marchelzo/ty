#include <string.h>

#include "ty.h"
#include "intern.h"
#include "vec.h"
#include "util.h"

void const *InternSentinel = &InternSentinel;

inline static InternEntry *
find(InternBucket const *bucket, char const *name, u64 hash)
{
        for (usize i = 0; i < vN(*bucket); ++i) {
                InternEntry *entry = v_(*bucket, i);
                if (entry->hash != hash) {
                        continue;
                }
                if (strcmp(entry->name, name) == 0) {
                        return entry;
                }
        }

        return NULL;
}

InternEntry *
intern_get(InternSet *set, char const *name)
{
        u64 hash = StrHash(name);
        InternBucket *bucket = &set->set[hash & (INTERN_TABLE_SIZE - 1)];

        InternEntry *entry = find(bucket, name, hash);

        if (entry != NULL) {
                return entry;
        }

        xvP(
                *bucket,
                ((InternEntry) {
                        .name = name,
                        .hash = hash,
                        .id   = -(bucket + 1 - set->set),
                        .data = set
                })
        );

        return vvX(*bucket);
}

InternEntry *
intern_put(InternEntry *e, void *data)
{
        InternSet *set = e->data;
        InternBucket *b = &set->set[-e->id - 1];

        e->data = data;
        e->id   = vN(set->index);
        e->name = S2(e->name);

        xvP(set->index, (b->count << 8u) | (b - set->set));

        b->count += 1;

        return e;
}

/* vim: set sts=8 sw=8 expandtab: */
