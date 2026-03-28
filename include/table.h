#ifndef TABLE_H_INCLUDED
#define TABLE_H_INCLUDED

#include "vec.h"
#include "defs.h"
#include "xd.h"

void
table_init(Ty *ty, ValueTable *t);

Value *
table_add(Ty *ty, ValueTable *t, char const *name, u64 h, Value const *f);

inline static Value *
table_put(Ty *ty, ValueTable *t, char const *name, Value const *f)
{
        return table_add(ty, t, name, hash64z(name), f);
}

void
table_copy(Ty *ty, ValueTable *dst, ValueTable const *src);

Value *
table_lookup(Ty *ty, ValueTable const *t, char const *name, u64 h);

inline static Value *
table_look(Ty *ty, ValueTable const *t, char const *name)
{
        return table_lookup(ty, t, name, hash64z(name));
}

void
table_release(Ty *ty, ValueTable *t);

#endif

/* vim: set sts=8 sw=8 expandtab: */
