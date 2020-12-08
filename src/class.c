#include <stdbool.h>
#include <string.h>

#include "value.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "vec.h"
#include "table.h"

static int class = 0;
static vec(char const *) names;
static vec(int) supers;
static vec(struct table) tables;

int
class_new(char const *name)
{
        vec_push(names, name);
        vec_push(supers, -1);

        struct table t;
        table_init(&t);
        vec_push(tables, t);

        return class++;
}

void
class_set_super(int class, int super)
{
        supers.items[class] = super;
}

int
class_lookup(char const *name)
{
     for (int i = 0; i < names.count; ++i)
          if (strcmp(names.items[i], name) == 0)
               return i;

     return -1;
}

char const *
class_name(int class)
{
        return names.items[class];
}

void
class_add_method(int class, char const *name, struct value f)
{
        table_add(&tables.items[class], name, f);
}

void
class_copy_methods(int dst, int src)
{
        struct table *dt = &tables.items[dst];
        struct table const *st = &tables.items[src];
        table_copy(dt, st);
}

struct value *
class_lookup_method(int class, char const *name)
{
        do {
                struct table const *t = &tables.items[class];
                struct value *v = table_lookup(t, name);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}
