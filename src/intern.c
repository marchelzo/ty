#include <string.h>

#include "ty.h"
#include "intern.h"
#include "vec.h"
#include "xd.h"

void const *InternSentinel = &InternSentinel;

inline static InternEntry *
find(InternBucket const *bucket, char const *name, usize length, u64 hash)
{
        for (usize i = 0; i < vN(*bucket); ++i) {
                InternEntry *entry = v_(*bucket, i);
                if (entry->hash != hash || entry->length != length) {
                        continue;
                }
                if (memcmp(entry->name, name, length) == 0) {
                        return entry;
                }
        }

        return NULL;
}

InternEntry *
intern_get_n(InternSet *set, char const *name, usize length)
{
        u64 hash = XXH3_64bits(name, length);
        InternBucket *bucket = &set->set[hash & (INTERN_TABLE_SIZE - 1)];

        InternEntry *entry = find(bucket, name, length, hash);

        if (entry != NULL) {
                return entry;
        }

        xvP(
                *bucket,
                ((InternEntry) {
                        .name   = name,
                        .length = length,
                        .hash   = hash,
                        .id     = -(bucket + 1 - set->set),
                        .data   = set
                })
        );

        return vvX(*bucket);
}

InternEntry *
intern_get(InternSet *set, char const *name)
{
        return intern_get_n(set, name, strlen(name));
}

InternEntry *
intern_put(InternEntry *e, void *data)
{
        InternSet *set = e->data;
        InternBucket *b = &set->set[-e->id - 1];

        char *owned_name = ty_malloc(e->length + 1);
        if (owned_name == NULL) {
                panic("out of memory");
        }
        memcpy(owned_name, e->name, e->length);
        owned_name[e->length] = '\0';

        e->name = owned_name;
        e->data = data;
        e->id   = vN(set->index);

        xvP(set->index, (b->count << 8u) | (b - set->set));

        b->count += 1;

        return e;
}

/* vim: set sts=8 sw=8 expandtab: */
