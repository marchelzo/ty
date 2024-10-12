#ifndef ITABLE_H_INCLUDED
#define ITABLE_H_INCLUDED

#include "vec.h"
#include "util.h"
#include "intern.h"
#include "ty.h"

enum { ITABLE_SIZE = 16 };

typedef struct value Value;

struct ibucket {
        vec(int64_t) ids;
        vec(struct value) values;
};

struct itable {
        struct ibucket buckets[ITABLE_SIZE];
        Value finalizer;
        int class;
};

void
itable_init(Ty *ty, struct itable *t);

struct value *
itable_add(Ty *ty, struct itable *t, int64_t id, Value v);

inline static struct value *
itable_put(Ty *ty, struct itable *t, char const *name, Value v)
{
        InternEntry *e = intern(&xD.members, name);
        return itable_add(ty, t, e->id, v);
}

void
itable_copy(Ty *ty, struct itable *dst, struct itable const *src);

struct value *
itable_lookup(Ty *ty, struct itable const *t, int64_t id);

inline static struct value *
itable_look(Ty *ty, struct itable const *t, char const *name)
{
        InternEntry *e = intern(&xD.members, name);
        return itable_lookup(ty, t, e->id);
}

int
itable_get_completions(Ty *ty, struct itable const *t, char const *prefix, char **out, int max);

void
itable_release(Ty *ty, struct itable *t);

#endif

/* vim: set sts=8 sw=8 expandtab: */
