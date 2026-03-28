#include "value.h"
#include "table.h"
#include "vec.h"
#include "xd.h"

void
table_init(Ty *ty, ValueTable *t)
{
        for (int i = 0; i < VALUE_TABLE_SIZE; ++i) {
                v00(t->buckets[i].hashes);
                v00(t->buckets[i].names);
                v00(t->buckets[i].values);
        }
}

Value *
table_add(Ty *ty, ValueTable *t, char const *name, u64 h, Value const *f)
{
        int i = h % VALUE_TABLE_SIZE;

        Value *m = table_lookup(ty, t, name, h);

        if (m == NULL) {
                xvP(t->buckets[i].hashes, h);
                xvP(t->buckets[i].names, name);
                xvP(t->buckets[i].values, *f);
                return vvL(t->buckets[i].values);
        } else {
                *m = *f;
                return m;
        }
}

void
table_copy(Ty *ty, ValueTable *dst, ValueTable const *src)
{
        struct bucket *dt = dst->buckets;
        struct bucket const *st = src->buckets;

        for (int i = 0; i < VALUE_TABLE_SIZE; ++i) {
                if (st[i].hashes.count == 0) {
                        continue;
                }
                xvPn(
                        dt[i].hashes,
                        st[i].hashes.items,
                        st[i].hashes.count
                );
                xvPn(
                        dt[i].names,
                        st[i].names.items,
                        st[i].names.count
                );
                xvPn(
                        dt[i].values,
                        st[i].values.items,
                        st[i].values.count
                );
        }
}

Value *
table_lookup(Ty *ty, ValueTable const *t, char const *name, u64 h)
{
        int i = h % VALUE_TABLE_SIZE;

        struct bucket const *b = &t->buckets[i];

        for (int i = 0; i < b->hashes.count; ++i) {
                if (b->hashes.items[i] != h) {
                        continue;
                }
                if (s_eq(b->names.items[i], name)) {
                        return &b->values.items[i];
                }
        }

        return NULL;
}

void
table_release(Ty *ty, ValueTable *t)
{
        for (int i = 0; i < VALUE_TABLE_SIZE; ++i) {
                mF(t->buckets[i].values.items);
                mF(t->buckets[i].names.items);
                mF(t->buckets[i].hashes.items);
        }
}

/* vim: set sts=8 sw=8 expandtab: */
