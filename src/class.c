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
static vec(char const *) docs;
static vec(int) supers;
static vec(struct value) finalizers;
static vec(struct table) mtables;
static vec(struct table) gtables;
static vec(struct table) stables;
static vec(struct table) ctables;

int
class_new(Ty *ty, char const *name, char const *doc)
{
        vvP(names, name);
        vvP(docs, doc);
        vvP(supers, -1);
        vvP(finalizers, NONE);

        struct table t;
        table_init(ty, &t);
        vvP(mtables, t);
        vvP(gtables, t);
        vvP(stables, t);
        vvP(ctables, t);

        return class++;
}

void
class_set_super(Ty *ty, int class, int super)
{
        /*
         * When a class is defined, its superclass defaults to 0 (Object)
         * if unspecified, but we don't want this behaviour when Object
         * itself is defined, otherwise we'd have a cyclic inheritance graph.
         */
        if (class != 0)
                supers.items[class] = super;
}

int
class_lookup(Ty *ty, char const *name)
{
     for (int i = 0; i < names.count; ++i)
          if (strcmp(names.items[i], name) == 0)
               return i;

     return -1;
}

char const *
class_name(Ty *ty, int class)
{
        return names.items[class];
}

void
class_add_static(Ty *ty, int class, char const *name, struct value f)
{
        table_put(ty, &ctables.items[class], name, f);
}

void
class_add_method(Ty *ty, int class, char const *name, struct value f)
{
        table_put(ty, &mtables.items[class], name, f);

        if (strcmp(name, "__free__") == 0) {
                finalizers.items[class] = f;
        }
}

void
class_add_getter(Ty *ty, int class, char const *name, struct value f)
{
        table_put(ty, &gtables.items[class], name, f);
}

void
class_add_setter(Ty *ty, int class, char const *name, struct value f)
{
        table_put(ty, &stables.items[class], name, f);
}

void
class_copy_methods(Ty *ty, int dst, int src)
{
        table_copy(ty, &mtables.items[dst], &mtables.items[src]);
        table_copy(ty, &gtables.items[dst], &gtables.items[src]);
        table_copy(ty, &stables.items[dst], &stables.items[src]);
}

struct value *
class_lookup_getter(Ty *ty, int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &gtables.items[class];
                struct value *v = table_lookup(ty, t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_setter(Ty *ty, int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &stables.items[class];
                struct value *v = table_lookup(ty, t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_method(Ty *ty, int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &mtables.items[class];
                struct value *v = table_lookup(ty, t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_static(Ty *ty, int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &ctables.items[class];
                struct value *v = table_lookup(ty, t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_immediate(Ty *ty, int class, char const *name, unsigned long h)
{
        struct table const *t = &mtables.items[class];
        return table_lookup(ty, t, name, h);
}

struct value
class_get_finalizer(Ty *ty, int class)
{
        while (class != -1) {
                if (finalizers.items[class].type != VALUE_NONE) {
                        return finalizers.items[class];
                }
                class = supers.items[class];
        }

        return NONE;
}

bool
class_is_subclass(Ty *ty, int sub, int super)
{
        do {
                if (sub == super) return true;
                sub = supers.items[sub];
        } while (sub != -1);

        return false;
}

int
class_get_completions(Ty *ty, int class, char const *prefix, char **out, int max)
{
        if (class == -1)
                return 0;

        int n = table_get_completions(ty, &mtables.items[class], prefix, out, max);
        return n + class_get_completions(ty, supers.items[class], prefix, out + n, max - n);
}

char const *
class_method_name(Ty *ty, int class, char const *name)
{
        do {
                struct table const *t = &mtables.items[class];
                char const *s = table_look_key(ty, t, name);
                if (s != NULL) return s;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct table *
class_methods(Ty *ty, int class)
{
        return &mtables.items[class];
}

struct table *
class_static_methods(Ty *ty, int class)
{
        return &ctables.items[class];
}

struct table *
class_getters(Ty *ty, int class)
{
        return &gtables.items[class];
}

struct table *
class_setters(Ty *ty, int class)
{
        return &stables.items[class];
}

char const *
class_doc(Ty *ty, int class)
{
        return docs.items[class];
}

/* vim: set sts=8 sw=8 expandtab: */
