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

inline static bool
hump(char const *s, usize i)
{
        return (i > 0)
            && xisupper(s[i])
            && (xislower(s[i - 1]) || xisdigit(s[i - 1]))
            && !xisupper(s[i + 1]);
}

char const *
KebabNameInto(char *out, usize cap, char const *name)
{
        usize n = strlen(name);

        if (n == 0 || !xislower(name[0]) || cap < 2 * n + 1) {
                return name;
        }

        char *p = out;

        for (usize i = 0; i < n; ++i) {
                if (hump(name, i)) {
                        *p++ = '-';
                        *p++ = xtolower(name[i]);
                } else {
                        *p++ = name[i];
                }
        }

        *p = '\0';

        return out;
}

char const *
KebabName(Ty *ty, char const *name)
{
        usize cap = 2 * strlen(name) + 1;
        return KebabNameInto(smA(cap), cap, name);
}

char const *
DashedName(Ty *ty, char const *name)
{
        if (!xislower(name[0])) {
                return name;
        }

        byte_vector out = {0};

        for (char const *p = name; *p != '\0'; ++p) {
                if (xisupper(*p)) {
                        svP(out, '-');
                        svP(out, xtolower(*p));
                } else {
                        svP(out, *p);
                }
        }

        svP(out, '\0');

        return vv(out);
}

/* vim: set sts=8 sw=8 expandtab: */
