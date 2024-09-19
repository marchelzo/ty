#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "alloc.h"
#include "util.h"
#include "value.h"
#include "object.h"
#include "table.h"
#include "gc.h"

struct table *
object_new(Ty *ty, int class)
{
        struct table *t =  mAo(sizeof *t, GC_OBJECT);
        table_init(ty, t);
        t->class = class;
        return t;
}

void
object_mark(Ty *ty, struct table *o)
{
        if (MARKED(o)) return;

        MARK(o);

        for (int i = 0; i < TABLE_SIZE; ++i)
                for (int v = 0; v < o->buckets[i].values.count; ++v)
                        value_mark(ty, &o->buckets[i].values.items[v]);

        // FIXME: hmm?
        return;

        value_mark(ty, &o->finalizer);
}

/* vim: set sts=8 sw=8 expandtab: */
