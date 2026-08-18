#include <string.h>

#include "ty.h"
#include "intern.h"
#include "vec.h"
#include "xd.h"

inline static InternEntry *
find(InternBucket const *bucket, char const *name, usize length, u64 hash)
{
        for (usize i = 0; i < vN(*bucket); ++i) {
                InternEntry *entry = v__(*bucket, i);
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

        TySpinLockLock(&set->lock);
        InternEntry *entry = find(bucket, name, length, hash);
        TySpinLockUnlock(&set->lock);

        if (entry != NULL) {
                return entry;
        }

        /*
         * A miss is represented in thread-local storage until intern_put().
         * The old implementation borrowed bucket->items[bucket->count], which
         * let another thread overwrite or invalidate the returned pointer.
         */
        static _Thread_local InternEntry pending;
        pending = (InternEntry) {
                .name   = name,
                .length = length,
                .hash   = hash,
                .id     = -1,
                .data   = set,
        };
        return &pending;
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
        usize length = e->length;
        u64 hash = e->hash;
        InternBucket *bucket = &set->set[hash & (INTERN_TABLE_SIZE - 1)];

        InternEntry *candidate = ty_malloc(sizeof *candidate + length + 1);
        if (candidate == NULL) {
                panic("out of memory");
        }
        char *owned_name = (char *)(candidate + 1);
        memcpy(owned_name, e->name, length);
        owned_name[length] = '\0';

        *candidate = (InternEntry) {
                .name   = owned_name,
                .length = length,
                .hash   = hash,
                .data   = data,
        };

        TySpinLockLock(&set->lock);

        /* Another thread may have committed the same miss in the meantime. */
        InternEntry *entry = find(bucket, owned_name, length, hash);
        if (entry != NULL) {
                TySpinLockUnlock(&set->lock);
                ty_free(candidate);
                return entry;
        }

        candidate->id = vN(set->index);
        xvP(*bucket, candidate);
        xvP(set->index, candidate);

        TySpinLockUnlock(&set->lock);
        return candidate;
}

/* vim: set sts=8 sw=8 expandtab: */
