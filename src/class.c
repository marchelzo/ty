#include <stdbool.h>
#include <string.h>

#include <string.h>

#include "value.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "vec.h"
#include "itable.h"
#include "class.h"
#include "types.h"

static vec(Class *) classes;
static vec(Class *) traits;

inline static Class *
C(int i)
{
        return v__(classes, i);
}

inline static Class *
T(int i)
{
        return v__(traits, i);
}

static char const *BuiltinClassNames[] = {
        [CLASS_ARRAY]     = "Array",
        [CLASS_BOOL]      = "Bool",
        [CLASS_CLASS]     = "Class",
        [CLASS_DICT]      = "Dict",
        [CLASS_FLOAT]     = "Float",
        [CLASS_FUNCTION]  = "Function",
        [CLASS_GENERATOR] = "Generator",
        [CLASS_INT]       = "Int",
        [CLASS_OBJECT]    = "Object",
        [CLASS_REGEX]     = "Regex",
        [CLASS_STRING]    = "String",
        [CLASS_TAG]       = "Tag",
        [CLASS_TUPLE]     = "Tuple"
};

void
class_init(Ty *ty)
{
        for (int i = CLASS_OBJECT; i < CLASS_PRIMITIVE; ++i) {
                Class *c = alloc0(sizeof *c);
                c->i = i;
                c->name = BuiltinClassNames[i];
                c->super = (i == CLASS_OBJECT) ? NULL : C(CLASS_OBJECT);
                c->type = type_class(ty, c);
                c->object_type = type_object(ty, c);
                xvP(classes, c);
        }

        classes.count = 0;
}

Class *
class_get_class(Ty *ty, int class)
{
        return C(class);
}

int
class_new(Ty *ty, Stmt *def)
{
        Class *c = (vN(classes) < CLASS_PRIMITIVE)
                 ? *vZ(classes)
                 : alloc0(sizeof *c);

        c->name = def->class.name;
        c->doc = def->class.doc;
        c->def = def;
        c->finalizer = NONE;
        c->i = vN(classes);
        c->super = (c->i == CLASS_OBJECT) ? NULL : C(CLASS_OBJECT);
        c->type = type_class(ty, c);
        c->object_type = type_object(ty, c);

        xvP(classes, c);

        return c->i;
}

int
trait_new(Ty *ty, Stmt *def)
{
        int class = class_new(ty, def);

        Class *c = C(class);
        c->is_trait = true;
        c->ti = vN(traits);

        xvP(traits, c);

        return class;
}

int
class_get_super(Ty *ty, int class)
{
        Class *c = C(class);
        return (c->super == NULL) ? -1 : c->super->i;
}

void
class_set_super(Ty *ty, int class, int super)
{
        C(class)->super = C(super);
}

void
class_add_field(Ty *ty, int class, char const *name, Expr *t, Expr *dflt)
{
        itable_put(
                ty,
                &C(class)->fields,
                name,
                TPTR(t, dflt)
        );
}

static void
finalize(Ty *ty, Class *c)
{
        Value *f = itable_lookup(ty, &c->methods, NAMES._free_);
        if (f != NULL) {
                c->finalizer = *f;
        }

        for (int i = 0; i < vN(c->traits); ++i) {
                Class *t = v__(c->traits, i);
                itable_copy_weak(ty, &c->methods, &t->methods);
                itable_copy_weak(ty, &c->getters, &t->getters);
        }

        c->final = true;
}

void
class_init_object(Ty *ty, int class, struct itable *o)
{
        Class *c = C(class);
        o->class = class;

        uvPn(o->ids, c->fields.ids.items, vN(c->fields.ids));
        uvR(o->values, vN(o->values) + vN(c->fields.values));
        for (int i = 0; i < vN(c->fields.values); ++i) {
                vPx(o->values, NIL);
        }

        if (!c->final) {
                finalize(ty, c);
        }
}

char const *
class_name(Ty *ty, int class)
{
        return (class == CLASS_TOP) ? "<top>" : C(class)->name;
}

void
class_add_static(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->statics, name, f);
}

void
class_add_method(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->methods, name, f);
}

void
class_add_getter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->getters, name, f);
}

void
class_add_setter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->setters, name, f);
}

void
class_copy_methods(Ty *ty, int dst, int src)
{
        itable_copy(ty, &C(dst)->methods, &C(src)->methods);
        itable_copy(ty, &C(dst)->getters, &C(src)->getters);
        itable_copy(ty, &C(dst)->setters, &C(src)->setters);
        itable_copy(ty, &C(dst)->fields, &C(src)->fields);
        C(dst)->finalizer = C(src)->finalizer;
}

Value *
class_lookup_field_i(Ty *ty, int class, int id)
{
        Class *c = C(class);
        Value *v;

        do {
                if ((v = itable_lookup(ty, &c->fields, id)) != NULL) {
                        return v;
                }
                c = c->super;
        } while (c != NULL);

        return NULL;
}

Value *
class_lookup_getter_i(Ty *ty, int class, int id)
{
        Class *c = C(class);
        Value *v;

        do {
                if ((v = itable_lookup(ty, &c->getters, id)) != NULL) {
                        return v;
                }
                c = c->super;
        } while (c != NULL);

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
        Class *c = C(class);
        Value *v;

        do {
                if ((v = itable_lookup(ty, &c->setters, id)) != NULL) {
                        return v;
                }
                c = c->super;
        } while (c != NULL);

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
        Class *c = C(class);
        Value *v;

        do {
                if ((v = itable_lookup(ty, &c->methods, id)) != NULL) {
                        return v;
                }
                c = c->super;
        } while (c != NULL);

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
        Class *c = C(class);
        Value *v;

        do {
                if ((v = itable_lookup(ty, &c->statics, id)) != NULL) {
                        return v;
                }
                c = c->super;
        } while (c != NULL);

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
        return itable_lookup(ty, &C(class)->methods, id);
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
      return C(class)->finalizer;
}

bool
class_is_trait(Ty *ty, int class)
{
        return C(class)->is_trait;
}

void
class_implement_trait(Ty *ty, int class, int trait)
{
        Class * restrict c = C(class);
        Class * restrict t = C(trait);

        xvP(c->traits, t);

        while (vN(c->impls) <= t->ti) {
                xvP(c->impls, false);
        }

        *v_(c->impls, t->ti) = true;
}

bool
class_is_subclass(Ty *ty, int sub, int super)
{
        if (sub == super || super == CLASS_TOP)
                return true;

        if (sub == CLASS_TOP)
                return false;

        Class *c = C(sub);
        Class *cc = C(super);

        if (cc->is_trait) {
                return vN(c->impls) > cc->ti && v__(c->impls, cc->ti);
        }

        do {
                if (c->super == cc) {
                        return true;
                }
                c = c->super;
        } while (c != NULL);

        return false;
}

int
class_get_completions(Ty *ty, int class, char const *prefix, char **out, int max)
{
        if (class == -1)
                return 0;

        int n, N = 0;

        n = itable_get_completions(ty, &C(class)->methods, prefix, out, max);
        max -= n;
        out += n;
        N += n;

        n = itable_get_completions(ty, &C(class)->getters, prefix, out, max);
        max -= n;
        out += n;
        N += n;

        n = itable_get_completions(ty, &C(class)->setters, prefix, out, max);
        max -= n;
        out += n;
        N += n;

        n = itable_get_completions(ty, &C(class)->statics, prefix, out, max);
        max -= n;
        out += n;
        N += n;

        if (C(class)->super != NULL) {
                N += class_get_completions(ty, C(class)->super->i, prefix, out, max);
        }

        return N;
}

struct itable *
class_methods(Ty *ty, int class)
{
        return &C(class)->methods;
}

struct itable *
class_static_methods(Ty *ty, int class)
{
        return &C(class)->statics;
}

struct itable *
class_getters(Ty *ty, int class)
{
        return &C(class)->getters;
}

struct itable *
class_setters(Ty *ty, int class)
{
        return &C(class)->setters;
}

char const *
class_doc(Ty *ty, int class)
{
        return C(class)->doc;
}

void
class_finalize_all(Ty *ty)
{
        for (int i = 0; i < vN(classes); ++i) {
                Class *c = C(i);
                if (!c->final) {
                        finalize(ty, c);
                }
        }
}

/* vim: set sts=8 sw=8 expandtab: */
