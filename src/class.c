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
#include "ty.h"

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

static void
finalize(Ty *ty, Class *c);

static void
really_finalize(Ty *ty, Class *c);

static char const *BuiltinClassNames[] = {
        [CLASS_ARRAY]        = "Array",
        [CLASS_BOOL]         = "Bool",
        [CLASS_BLOB]         = "Blob",
        [CLASS_CLASS]        = "Class",
        [CLASS_DICT]         = "Dict",
        [CLASS_FLOAT]        = "Float",
        [CLASS_FUNCTION]     = "Function",
        [CLASS_GENERATOR]    = "Generator",
        [CLASS_INT]          = "Int",
        [CLASS_INC_RANGE]    = "InclusiveRange",
        [CLASS_ITER]         = "Iter",
        [CLASS_ITERABLE]     = "Iterable",
        [CLASS_OBJECT]       = "Object",
        [CLASS_PTR]          = "Ptr",
        [CLASS_INTO_PTR]     = "IntoPtr",
        [CLASS_QUEUE]        = "Queue",
        [CLASS_RANGE]        = "Range",
        [CLASS_REGEX]        = "Regex",
        [CLASS_REGEXV]       = "RegexV",
        [CLASS_RE_MATCH]     = "RegexMatch",
        [CLASS_REV_ITER]     = "ReverseIter",
        [CLASS_SHARED_QUEUE] = "SharedQueue",
        [CLASS_STRING]       = "String",
        [CLASS_TAG]          = "Tag",
        [CLASS_TUPLE]        = "Tuple"
};

static void
init(Ty *ty, Class *c, Stmt *def)
{
        c->name = def->class.name;
        c->doc = def->class.doc;
        c->def = def;
        c->finalizer = NONE;
        c->super = (c->i == CLASS_OBJECT) ? NULL : C(CLASS_OBJECT);
        c->type = type_class(ty, c);
        c->object_type = type_object(ty, c);
}

inline static void
MakeTrait(Ty *ty, Class *c)
{
        c->is_trait = true;
        c->ti = vN(traits);
        xvP(traits, c);
}

inline static bool
ClassImplementsTrait(Class const *c, int ti)
{
        return vN(c->impls) > ti
            && v__(c->impls, ti);
}

Class *
class_get(Ty *ty, int class)
{
        return C(class);
}

Class *
class_new_empty(Ty *ty)
{
        Class *c = alloc0(sizeof *c);
        c->i = vN(classes);

        xvP(classes, c);

        if (c->i < CLASS_BUILTIN_END) {
                c->name = BuiltinClassNames[c->i];
                switch (c->i) {
                case CLASS_ITERABLE:
                case CLASS_ITER:
                case CLASS_INTO_PTR:
                        MakeTrait(ty, c);
                }
        }

        c->type = type_class(ty, c);
        c->object_type = type_object(ty, c);

        return c;
}

int
class_new(Ty *ty, Stmt *def)
{
        Class *c = class_new_empty(ty);
        init(ty, c, def);
        return c->i;
}

void
class_builtin(Ty *ty, int class, Stmt *s)
{
        Class *c = C(class);
        init(ty, c, s);
}

int
trait_new(Ty *ty, Stmt *def)
{
        int class = class_new(ty, def);
        MakeTrait(ty, C(class));
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
        Class *c0 = C(class);
        Class *c1 = C(super);

        c0->super = c1;

        if (c0->is_trait && c1->is_trait) {
                for (int i = 0; i < vN(classes); ++i) {
                        if (ClassImplementsTrait(v__(classes, i), c0->ti)) {
                                class_implement_trait(ty, v__(classes, i)->i, c1->i);
                        }
                }
        }
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
        return (class <= CLASS_TOP) ? "<top>" : C(class)->name;
}

void
class_add_static(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->statics, name, f);
}

void
class_add_static_i(Ty *ty, int class, int id, Value f)
{
        itable_add(ty, &C(class)->statics, id, f);
}

void
class_add_method(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->methods, name, f);
}

void
class_add_method_i(Ty *ty, int class, int id, Value f)
{
        itable_add(ty, &C(class)->methods, id, f);
}

void
class_add_getter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->getters, name, f);
}

void
class_add_getter_i(Ty *ty, int class, int id, Value f)
{
        itable_add(ty, &C(class)->getters, id, f);
}

void
class_add_setter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->setters, name, f);
}

void
class_add_setter_i(Ty *ty, int class, int id, Value f)
{
        itable_add(ty, &C(class)->setters, id, f);
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
class_lookup_getter(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_getter_i(ty, class, e->id);
}

Value *
class_lookup_setter(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_setter_i(ty, class, e->id);
}

static bool log = true;
//#define pp(...)  log && printf("  " __VA_ARGS__)
#define pp(...)  0

inline static void
qput(Ty *ty, ClassVector *cq, u32 i, u32 *j, Class *c)
{
        u32 n = vC(*cq);
        u32 mask = n - 1;
        u32 j0 = (*j + n) & mask;

        pp("put pre:  i=%u j=%u n=%u j0=%u\n", i, *j, n, j0);

        if (++*j == 1 || j0 + 1 == n) {
                do svP(*cq, NULL); while (vN(*cq) != vC(*cq));
        }

        pp("put post: i=%u j=%u n=%zu j0=%u\n", i, *j, vC(*cq), j0);

        *v_(*cq, j0) = c;
}

inline static Class *
qget(Ty *ty, ClassVector *cq, u32 *i, u32 j)
{
        u32 n = vC(*cq);
        u32 mask = n - 1;
        u32 i0 = (*i + n) & mask;

        pp("get pre:  i=%u j=%u n=%u i0=%u\n", *i, j, n, i0);

        if (++*i > j) {
                return NULL;
        }

        return v__(*cq, i0);
}

static void
class_resolve_all(Ty *ty, int class)
{
        Class *c0 = C(class);
        Class *c  = C(class);

        SCRATCH_SAVE();

        u32 i = 0;
        u32 j = 0;
        ClassVector sq = {0};

        do {
                if (c->super != NULL) {
                        qput(ty, &sq, i, &j, c->super);
                }
                for (u32 t = 0; t < vN(c->traits); ++t) {
                        qput(ty, &sq, i, &j, v__(c->traits, t));
                }
                if (c != c0) {
                        finalize(ty, c);
                        itable_copy_weak(ty, &c0->methods, &c->methods);
                        itable_copy_weak(ty, &c0->getters, &c->getters);
                        itable_copy_weak(ty, &c0->setters, &c->setters);
                        itable_copy_weak(ty, &c0->statics, &c->statics);
                }
        } while ((c = qget(ty, &sq, &i, j)) != NULL);

        SCRATCH_RESTORE();
}

Value *
class_lookup_method(Ty *ty, int class, char const *name, unsigned long h)
{
        InternEntry *e = intern(&xD.members, name);
        return class_lookup_method_i(ty, class, e->id);
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

        while (vN(c->impls) <= t->ti) {
                xvP(c->impls, false);
        }

        if (!v__(c->impls, t->ti)) {
                xvP(c->traits, t);
                *v_(c->impls, t->ti) = true;
                if (t->super != NULL && t->super->is_trait) {
                        class_implement_trait(ty, c->i, t->super->i);
                }
        }
}

bool
class_is_subclass(Ty *ty, int sub, int super)
{
        if (
                (sub   == super)
             || (super == CLASS_TOP)
             || (sub   == CLASS_BOTTOM)
        ) {
                return true;
        }

        if (
                (sub   == CLASS_TOP)
             || (sub   == CLASS_NIL)
             || (super == CLASS_BOTTOM)
             || (super == CLASS_NIL)
        ) {
                return false;
        }

        Class *c = C(sub);
        Class *cc = C(super);

        if (!c->is_trait && cc->is_trait) {
                return ClassImplementsTrait(c, cc->ti);
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

static int
completions(
        Ty *ty,
        int class,
        char const *prefix,
        expression_vector *out,
        int_vector *depths,
        int depth
)
{
        if (class < 0) {
                return 0;
        }

        Class *c = C(class);
        int n = vN(*out);
        int prefix_len = (prefix == NULL) ? 0 : strlen(prefix);

        for (int i = 0; i < vN(c->def->class.methods); ++i) {
                Expr *field = v__(c->def->class.methods, i);
                if (strncmp(field->name, prefix, prefix_len) == 0) {
                        xvP(*out, field);
                        xvP(*depths, depth);
                }
        }

        for (int i = 0; i < vN(c->def->class.getters); ++i) {
                Expr *field = v__(c->def->class.getters, i);
                if (strncmp(field->name, prefix, prefix_len) == 0) {
                        xvP(*out, field);
                        xvP(*depths, depth);
                }
        }

        for (int i = 0; i < vN(c->def->class.fields); ++i) {
                Expr *field = v__(c->def->class.fields, i);
                if (
                        (
                                field->type == EXPRESSION_IDENTIFIER
                             && strncmp(field->identifier, prefix, prefix_len) == 0
                        )
                     || (
                                field->type == EXPRESSION_EQ
                             && strncmp(field->target->identifier, prefix, prefix_len) == 0
                        )
                ) {
                        xvP(*out, field);
                        xvP(*depths, depth);
                }
        }

        if (c->super != NULL) {
                completions(ty, c->super->i, prefix, out, depths, depth + 1);
        }

        return (int)vN(*out) - n;
}

int
class_completions(
        Ty *ty,
        int class,
        char const *prefix,
        expression_vector *out,
        int_vector *depths
)
{
        return completions(ty, class, prefix, out, depths, 0);
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
                if  (c->final && !c->really_final) {
                        really_finalize(ty, c);
                }
                if (!c->final) {
                        finalize(ty, c);
                }
        }
}

Expr *
FieldIdentifier(Expr const *field)
{
        if (field == NULL) {
                return NULL;
        }

        if (field->type == EXPRESSION_IDENTIFIER) {
                return (Expr *)field;
        }

        if (
                field->type == EXPRESSION_EQ
             && field->target->type == EXPRESSION_IDENTIFIER
        ) {
                return field->target;
        }

        return NULL;
}

Expr *
FindMethodImmediate(expression_vector const *ms, char const *name)
{
        for (int i = 0; i < vN(*ms); ++i) {
                if (strcmp(name, v__(*ms, i)->name) == 0) {
                        return v__(*ms, i);
                }
        }

        return NULL;
}

Expr *
FindGetter(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethodImmediate(&c->def->class.getters, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindGetter(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Expr *
FindSetter(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethodImmediate(&c->def->class.setters, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindSetter(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Expr *
FindMethod(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethodImmediate(&c->def->class.methods, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindMethod(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Expr *
FindStatic(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethodImmediate(&c->def->class.statics, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindStatic(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Expr *
FindFieldImmediate(expression_vector const *fs, char const *name)
{
        for (int i = 0; i < vN(*fs); ++i) {
                Expr *field = v__(*fs, i);
                if (strcmp(FieldIdentifier(field)->identifier, name) == 0) {
                        return field;
                }
        }

        return NULL;
}

Expr *
FindField(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindFieldImmediate(&c->def->class.fields, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindField(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

inline static void
eliminate_refs(struct itable *t)
{
        for (u32 i = 0; i < vN(t->values); ++i) {
                Value *v = v_(t->values, i);
                if (v->type == VALUE_REF) {
                        *v = *v->ref;
                }
        }
}

static void
really_finalize(Ty *ty, Class *c)
{
        eliminate_refs(&c->statics);
        eliminate_refs(&c->methods);
        eliminate_refs(&c->getters);
        eliminate_refs(&c->setters);
        c->really_final = true;
}

static void
finalize(Ty *ty, Class *c)
{
        if (c->final) {
                return;
        }

        Value *f = itable_lookup(ty, &c->methods, NAMES._free_);
        if (f != NULL) {
                c->finalizer = *f;
        }

        class_resolve_all(ty, c->i);

        c->final = true;
}


/* vim: set sts=8 sw=8 expandtab: */
