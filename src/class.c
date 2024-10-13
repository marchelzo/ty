#include <stdbool.h>
#include <string.h>

#include "value.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "vec.h"
#include "itable.h"
#include "class.h"

static int class = 0;
static vec(char const *) names;
static vec(char const *) docs;
static vec(int) supers;
static vec(Value) finalizers;
static vec(struct itable) mtables;
static vec(struct itable) gtables;
static vec(struct itable) stables;
static vec(struct itable) ctables;

int
class_new(Ty *ty, char const *name, char const *doc)
{
        xvP(names, name);
        xvP(docs, doc);
        xvP(supers, -1);
        xvP(finalizers, NONE);

        struct itable t;
        itable_init(ty, &t);

        xvP(mtables, t);
        xvP(gtables, t);
        xvP(stables, t);
        xvP(ctables, t);

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
        return (class == CLASS_TOP) ? "(top)" : names.items[class];
}

void
class_add_static(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &ctables.items[class], name, f);
}

void
class_add_method(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &mtables.items[class], name, f);

        if (strcmp(name, "__free__") == 0) {
                finalizers.items[class] = f;
        }
}

void
class_add_getter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &gtables.items[class], name, f);
}

void
class_add_setter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &stables.items[class], name, f);
}

void
class_copy_methods(Ty *ty, int dst, int src)
{
        itable_copy(ty, &mtables.items[dst], &mtables.items[src]);
        itable_copy(ty, &gtables.items[dst], &gtables.items[src]);
        itable_copy(ty, &stables.items[dst], &stables.items[src]);
}

Value *
class_lookup_getter_i(Ty *ty, int class, int id)
{
        do {
                struct itable const *t = &gtables.items[class];
                Value *v = itable_lookup(ty, t, id);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

Value *
class_lookup_getter(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_getter_i(ty, class, e->id);
}

Value *
class_lookup_setter_i(Ty *ty, int class, int id)
{
        do {
                struct itable const *t = &stables.items[class];
                Value *v = itable_lookup(ty, t, id);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

Value *
class_lookup_setter(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_setter_i(ty, class, e->id);
}

Value *
class_lookup_method_i(Ty *ty, int class, int id)
{
        do {
                struct itable const *t = &mtables.items[class];
                Value *v = itable_lookup(ty, t, id);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

Value *
class_lookup_method(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_method_i(ty, class, e->id);
}

Value *
class_lookup_static_i(Ty *ty, int class, int id)
{
        do {
                struct itable const *t = &ctables.items[class];
                Value *v = itable_lookup(ty, t, id);
                if (v != NULL) return v;
                class = supers.items[class];
        } while (class != -1);

        return NULL;
}

Value *
class_lookup_static(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_static_i(ty, class, e->id);
}

Value *
class_lookup_immediate_i(Ty *ty, int class, int id)
{
        struct itable const *t = &mtables.items[class];
        return itable_lookup(ty, t, id);
}

Value *
class_lookup_immediate(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_immediate_i(ty, class, e->id);
}

Value
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
        for (;;) {
                if (sub == super)
                        return true;
                if (sub == CLASS_TOP)
                        return false;
                sub = supers.items[sub];
        }
}

int
class_get_completions(Ty *ty, int class, char const *prefix, char **out, int max)
{
        if (class == -1)
                return 0;

        int n = itable_get_completions(ty, &mtables.items[class], prefix, out, max);
        return n + class_get_completions(ty, supers.items[class], prefix, out + n, max - n);
}

struct itable *
class_methods(Ty *ty, int class)
{
        return &mtables.items[class];
}

struct itable *
class_static_methods(Ty *ty, int class)
{
        return &ctables.items[class];
}

struct itable *
class_getters(Ty *ty, int class)
{
        return &gtables.items[class];
}

struct itable *
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
