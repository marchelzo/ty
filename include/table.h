#ifndef TABLE_H_INCLUDED
#define TABLE_H_INCLUDED

#include "vec.h"
#include "util.h"

#define TABLE_SIZE 16

struct value;

struct bucket {
        vec(uint64_t) hashes;
        vec(char const *) names;
        vec(struct value) values;
};

struct table {
        struct bucket buckets[TABLE_SIZE];
        struct value finalizer;
        int class;
};

void
table_init(Ty *ty, struct table *t);

struct value *
table_add(Ty *ty, struct table *t, char const *name, unsigned long h, struct value f);

inline static struct value *
table_put(Ty *ty, struct table *t, char const *name, struct value f)
{
        return table_add(ty, t, name, strhash(name), f);
}

void
table_copy(Ty *ty, struct table *dst, struct table const *src);

struct value *
table_lookup(Ty *ty, struct table const *t, char const *name, unsigned long h);

inline static struct value *
table_look(Ty *ty, struct table const *t, char const *name)
{
        return table_lookup(ty, t, name, strhash(name));
}

char const *
table_lookup_key(Ty *ty, struct table const *t, char const *name, unsigned long h);

inline static char const *
table_look_key(Ty *ty, struct table const *t, char const *name)
{
        return table_lookup_key(ty, t, name, strhash(name));
}

int
table_get_completions(Ty *ty, struct table const *t, char const *prefix, char **out, int max);

void
table_release(Ty *ty, struct table *t);

#endif

/* vim: set sts=8 sw=8 expandtab: */
