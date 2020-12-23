#ifndef TABLE_H_INCLUDED
#define TABLE_H_INCLUDED

#include "vec.h"

#define TABLE_SIZE 8

struct value;

struct bucket {
        vec(uint64_t) hashes;
        vec(char const *) names;
        vec(struct value) values;
};

struct table {
        struct bucket buckets[TABLE_SIZE];
};

void
table_init(struct table *t);

struct value *
table_add(struct table *t, char const *name, struct value f);

void
table_copy(struct table *dst, struct table const *src);

struct value *
table_lookup(struct table const *t, char const *name);


#endif
