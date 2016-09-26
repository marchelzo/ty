#include "value.h"
#include "table.h"
#include "vec.h"
#include "util.h"

void
table_init(struct table *t)
{
        for (int i = 0; i < TABLE_SIZE; ++i) {
                vec_init(t->buckets[i].hashes);
                vec_init(t->buckets[i].names);
                vec_init(t->buckets[i].values);
        }
}

struct value *
table_add(struct table *t, char const *name, struct value f)
{
        uint64_t h = strhash(name);
        int i = h % TABLE_SIZE;

        struct value *m = table_lookup(t, name);

        if (m == NULL) {
                vec_push(t->buckets[i].hashes, h);
                vec_push(t->buckets[i].names, name);
                vec_push(t->buckets[i].values, f);
                return vec_last(t->buckets[i].values);
        } else {
                *m = f;
                return m;
        }
}

void
table_copy(struct table *dst, struct table const *src)
{
        struct bucket *dt = dst->buckets;
        struct bucket const *st = src->buckets;

        for (int i = 0; i < TABLE_SIZE; ++i) {
                if (st[i].hashes.count == 0)
                        continue;
                vec_push_n(
                        dt[i].hashes,
                        st[i].hashes.items,
                        st[i].hashes.count
                );
                vec_push_n(
                        dt[i].names,
                        st[i].names.items,
                        st[i].names.count
                );
                vec_push_n(
                        dt[i].values,
                        st[i].values.items,
                        st[i].values.count
                );
        }
}

struct value *
table_lookup(struct table const *t, char const *name)
{
        uint64_t h = strhash(name);
        int i = h % TABLE_SIZE;

        struct bucket const *b = &t->buckets[i];

        for (int i = 0; i < b->hashes.count; ++i) {
                if (b->hashes.items[i] != h)
                        continue;
                if (strcmp(b->names.items[i], name) == 0)
                        return &b->values.items[i];
        }

        return NULL;
}
