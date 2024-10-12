#include "value.h"
#include "table.h"
#include "vec.h"
#include "util.h"

void
table_init(Ty *ty, struct table *t)
{
        for (int i = 0; i < TABLE_SIZE; ++i) {
                vec_init(t->buckets[i].hashes);
                vec_init(t->buckets[i].names);
                vec_init(t->buckets[i].values);
        }

        t->finalizer = NIL;
        t->class = -1;
}

struct value *
table_add(Ty *ty, struct table *t, char const *name, unsigned long h, struct value f)
{
        int i = h % TABLE_SIZE;

        struct value *m = table_lookup(ty, t, name, h);

        if (m == NULL) {
                vvP(t->buckets[i].hashes, h);
                vvP(t->buckets[i].names, name);
                vvP(t->buckets[i].values, f);
                return vvL(t->buckets[i].values);
        } else {
                *m = f;
                return m;
        }
}

void
table_copy(Ty *ty, struct table *dst, struct table const *src)
{
        struct bucket *dt = dst->buckets;
        struct bucket const *st = src->buckets;

        for (int i = 0; i < TABLE_SIZE; ++i) {
                if (st[i].hashes.count == 0)
                        continue;
                vvPn(
                        dt[i].hashes,
                        st[i].hashes.items,
                        st[i].hashes.count
                );
                vvPn(
                        dt[i].names,
                        st[i].names.items,
                        st[i].names.count
                );
                vvPn(
                        dt[i].values,
                        st[i].values.items,
                        st[i].values.count
                );
        }
}

struct value *
table_lookup(Ty *ty, struct table const *t, char const *name, unsigned long h)
{
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

void
table_release(Ty *ty, struct table *t)
{
        for (int i = 0; i < TABLE_SIZE; ++i) {
                mF(t->buckets[i].values.items);
                mF(t->buckets[i].names.items);
                mF(t->buckets[i].hashes.items);
        }
}

int
table_get_completions(Ty *ty, struct table const *t, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        for (int i = 0; i < TABLE_SIZE; ++i) {
                for (int j = 0; j < t->buckets[i].names.count; ++j) {
                        if (n < max && strncmp(t->buckets[i].names.items[j], prefix, prefix_len) == 0) {
                                out[n++] = sclone_malloc(t->buckets[i].names.items[j]);
                        }
                }
        }

        return n;
}

/* vim: set sts=8 sw=8 expandtab: */
