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
};

void
table_init(struct table *t);

struct value *
table_add(struct table *t, char const *name, unsigned long h, struct value f);

inline static struct value *
table_put(struct table *t, char const *name, struct value f)
{
        return table_add(t, name, strhash(name), f);
}

void
table_copy(struct table *dst, struct table const *src);

struct value *
table_lookup(struct table const *t, char const *name, unsigned long h);

inline static struct value *
table_look(struct table const *t, char const *name)
{
        return table_lookup(t, name, strhash(name));
}

char const *
table_lookup_key(struct table const *t, char const *name, unsigned long h);

inline static char const *
table_look_key(struct table const *t, char const *name)
{
        return table_lookup_key(t, name, strhash(name));
}

int
table_get_completions(struct table const *t, char const *prefix, char **out, int max);

void
table_release(struct table *t);

#endif
