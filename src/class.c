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
class_new(char const *name, char const *doc)
{
        vec_push(names, name);
        vec_push(docs, doc);
        vec_push(supers, -1);
        vec_push(finalizers, NONE);

        struct table t;
        table_init(&t);
        vec_push(mtables, t);
        vec_push(gtables, t);
        vec_push(stables, t);
        vec_push(ctables, t);

        return class++;
}

void
class_set_super(int class, int super)
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
class_add_static(int class, char const *name, struct value f)
{
        table_put(&ctables.items[class], name, f);
}

void
class_add_method(int class, char const *name, struct value f)
{
        table_put(&mtables.items[class], name, f);

        if (strcmp(name, "__free__") == 0) {
                finalizers.items[class] = f;
        }
}

void
class_add_getter(int class, char const *name, struct value f)
{
        table_put(&gtables.items[class], name, f);
}

void
class_add_setter(int class, char const *name, struct value f)
{
        table_put(&stables.items[class], name, f);
}

void
class_copy_methods(int dst, int src)
{
        table_copy(&mtables.items[dst], &mtables.items[src]);
        table_copy(&gtables.items[dst], &gtables.items[src]);
        table_copy(&stables.items[dst], &stables.items[src]);
}

struct value *
class_lookup_getter(int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &gtables.items[class];
                struct value *v = table_lookup(t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_setter(int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &stables.items[class];
                struct value *v = table_lookup(t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_method(int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &mtables.items[class];
                struct value *v = table_lookup(t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_static(int class, char const *name, unsigned long h)
{
        do {
                struct table const *t = &ctables.items[class];
                struct value *v = table_lookup(t, name, h);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct value *
class_lookup_immediate(int class, char const *name, unsigned long h)
{
        struct table const *t = &mtables.items[class];
        return table_lookup(t, name, h);
}

struct value
class_get_finalizer(int class)
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
class_is_subclass(int sub, int super)
{
        do {
                if (sub == super) return true;
                sub = supers.items[sub];
        } while (sub != -1);

        return false;
}

int
class_get_completions(int class, char const *prefix, char **out, int max)
{
        if (class == -1)
                return 0;

        int n = table_get_completions(&mtables.items[class], prefix, out, max);
        return n + class_get_completions(supers.items[class], prefix, out + n, max - n);
}

char const *
class_method_name(int class, char const *name)
{
        do {
                struct table const *t = &mtables.items[class];
                char const *s = table_look_key(t, name);
                if (s != NULL) return s;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

struct table *
class_methods(int class)
{
        return &mtables.items[class];
}

struct table *
class_static_methods(int class)
{
        return &ctables.items[class];
}

struct table *
class_getters(int class)
{
        return &gtables.items[class];
}

struct table *
class_setters(int class)
{
        return &stables.items[class];
}

char const *
class_doc(int class)
{
        return docs.items[class];
}

/* vim: set sts=8 sw=8 expandtab: */
