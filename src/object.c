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
object_new(void)
{
        struct table *t =  gc_alloc_object(sizeof *t, GC_OBJECT);
        table_init(t);
        return t;
}

void
object_mark(struct table *o)
{
        if (MARKED(o)) return;

        MARK(o);

        for (int i = 0; i < TABLE_SIZE; ++i)
                for (int v = 0; v < o->buckets[i].values.count; ++v)
                        value_mark(&o->buckets[i].values.items[v]);
}

void
object_free(struct table *o)
{
        for (int i = 0; i < TABLE_SIZE; ++i) {
                free(o->buckets[i].values.items);
                free(o->buckets[i].names.items);
                free(o->buckets[i].hashes.items);
        }
}
