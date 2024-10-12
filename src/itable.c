#include "value.h"
#include "itable.h"
#include "vec.h"
#include "util.h"

void
itable_init(Ty *ty, struct itable *t)
{
        for (int i = 0; i < ITABLE_SIZE; ++i) {
                vec_init(t->buckets[i].ids);
                vec_init(t->buckets[i].values);
        }

        t->finalizer = NIL;
        t->class = -1;
}

Value *
itable_add(Ty *ty, struct itable *t, int64_t id, Value v)
{
        int i = id % ITABLE_SIZE;

        Value *m = itable_lookup(ty, t, id);

        if (m == NULL) {
                vvP(t->buckets[i].ids, id);
                vvP(t->buckets[i].values, v);
                return vvL(t->buckets[i].values);
        } else {
                *m = v;
                return m;
        }
}

void
itable_copy(Ty *ty, struct itable *dst, struct itable const *src)
{
        struct ibucket *dt = dst->buckets;
        struct ibucket const *st = src->buckets;

        for (int i = 0; i < ITABLE_SIZE; ++i) {
                if (st[i].ids.count == 0)
                        continue;
                vvPn(
                        dt[i].ids,
                        st[i].ids.items,
                        st[i].ids.count
                );
                vvPn(
                        dt[i].values,
                        st[i].values.items,
                        st[i].values.count
                );
        }
}

Value *
itable_lookup(Ty *ty, struct itable const *t, int64_t id)
{
        int i = id % ITABLE_SIZE;

        struct ibucket const *b = &t->buckets[i];

        for (int i = 0; i < b->ids.count; ++i) {
                if (b->ids.items[i] == id)
                        return &b->values.items[i];
        }

        return NULL;
}

void
itable_release(Ty *ty, struct itable *t)
{
        for (int i = 0; i < ITABLE_SIZE; ++i) {
                mF(t->buckets[i].values.items);
                mF(t->buckets[i].ids.items);
        }
}

int
itable_get_completions(Ty *ty, struct itable const *t, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        for (int i = 0; i < ITABLE_SIZE; ++i) {
                for (int j = 0; j < t->buckets[i].ids.count; ++j) {
                        char const *name = intern_entry(&xD.members, t->buckets[i].ids.items[j])->name;
                        if (n < max && strncmp(name, prefix, prefix_len) == 0) {
                                out[n++] = sclone_malloc(name);
                        }
                }
        }

        return n;
}

/* vim: set sts=8 sw=8 expandtab: */
