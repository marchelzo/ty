#include <stdbool.h>
#include <string.h>

#include <string.h>

#include "value.h"
#include "alloc.h"
#include "log.h"
#include "xd.h"
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
        [CLASS_ARRAY]           = "Array",
        [CLASS_BOOL]            = "Bool",
        [CLASS_BLOB]            = "Blob",
        [CLASS_CLASS]           = "Class",
        [CLASS_DICT]            = "Dict",
        [CLASS_ERROR]           = "BaseException",
        [CLASS_RUNTIME_ERROR]   = "RuntimeError",
        [CLASS_COMPILE_ERROR]   = "CompileError",
        [CLASS_VALUE_ERROR]     = "ValueError",
        [CLASS_ASSERT_ERROR]    = "AssertionError",
        [CLASS_TIMEOUT_ERROR]   = "TimeoutError",
        [CLASS_CANCELED_ERROR]  = "CanceledError",
        [CLASS_FLOAT]           = "Float",
        [CLASS_FUNCTION]        = "Function",
        [CLASS_GENERATOR]       = "Generator",
        [CLASS_INT]             = "Int",
        [CLASS_INC_RANGE]       = "InclusiveRange",
        [CLASS_ITER]            = "Iter",
        [CLASS_ITERABLE]        = "Iterable",
        [CLASS_OBJECT]          = "Object",
        [CLASS_PTR]             = "Ptr",
        [CLASS_INTO_PTR]        = "IntoPtr",
        [CLASS_QUEUE]           = "Queue",
        [CLASS_RANGE]           = "Range",
        [CLASS_REGEX]           = "Regex",
        [CLASS_REGEXV]          = "RegexV",
        [CLASS_RE_MATCH]        = "RegexMatch",
        [CLASS_SHARED_QUEUE]    = "SharedQueue",
        [CLASS_STRING]          = "String",
        [CLASS_TAG]             = "Tag",
        [CLASS_TUPLE]           = "Tuple",
        [CLASS_TUPLE_SPEC]      = "TupleSpec"
};

static void
init(Ty *ty, Class *c, Stmt *def)
{
        c->name        = def->class.name;
        c->doc         = def->class.doc;
        c->def         = def;
        c->init        = NONE;
        c->finalizer   = NONE;
        c->super       = (c->i != CLASS_OBJECT) ? C(CLASS_OBJECT) : NULL;
        c->type        = type_class(ty, c);
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
        do {
                if (
                        (vN(c->impls) > ti)
                     && v__(c->impls, ti)
                ) {
                        return true;
                }
                c = c->super;
        } while (
                (c != NULL)
        );

        return false;
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

        c->type        = type_class(ty, c);
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
                                class_implement_trait(
                                        ty,
                                        v__(classes, i)->i,
                                        c1->i
                                );
                        }
                }
        }
}

void
class_add_field(Ty *ty, Class *c, i32 id, Expr *type, Expr *dflt)
{
        itable_add(ty, &c->fields, id, TPTR(type, dflt));
}

void
class_add_s_field(Ty *ty, Class *c, i32 id, Expr *type, Expr *dflt)
{
        (void)type;
        (void)dflt;
        itable_add(ty, &c->s_fields, id, REF(NewZero()));
}

TyObject *
class_new_instance(Ty *ty, int class)
{
        Class *c = C(class);

        usize const size = sizeof (TyObject)
                         + vN(c->fields.ids) * sizeof (Value);

        TyObject *obj =  mAo0(size, GC_OBJECT);
        obj->class = c;
        obj->nslot = vN(c->fields.ids);

        for (int i = 0; i < obj->nslot; ++i) {
                obj->slots[i] = NIL;
        }

        return obj;
}

Value *
class_ctor(Ty *ty, int class)
{
        Class *c = C(class);

        if (UNLIKELY(!c->really_final)) {
                if (!c->final) {
                        finalize(ty, c);
                }
                really_finalize(ty, c);
        }

        ASSERT(c->init.type == VALUE_FUNCTION);

        return &c->init;
}

void
class_mark(Ty *ty, int c)
{
        Class *class = C(c);

        for (usize i = 0; i < vN(class->s_fields.values); ++i) {
                Value *v = v_(class->s_fields.values, i);
                value_mark(ty, v);
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
        itable_put(ty, &C(class)->s_methods, name, f);
}

void
class_add_s_getter(Ty *ty, int class, char const *name, Value f)
{
        itable_put(ty, &C(class)->s_getters, name, f);
}

void
class_add_static_i(Ty *ty, int class, int id, Value f)
{
        itable_add(ty, &C(class)->s_methods, id, f);
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
class_lookup_field(Ty *ty, int class, int id)
{
        Class *c = C(class);
        Value *v = itable_lookup(ty, &c->s_fields, id);

        if (v == NULL) {
                return NULL;
        }

        if  (v->type != VALUE_REF) {
                return v;
        }

        return (v->ref->type != VALUE_ZERO) ? v->ref : NULL;
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
        Class *c  = C(class);
        Class *c0 = c;

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
                        itable_copy_weak(ty, &c0->fields,    &c->fields);
                        itable_copy_weak(ty, &c0->methods,   &c->methods);
                        itable_copy_weak(ty, &c0->getters,   &c->getters);
                        itable_copy_weak(ty, &c0->setters,   &c->setters);
                        itable_copy_weak(ty, &c0->s_methods, &c->s_methods);
                        itable_copy_weak(ty, &c0->s_getters, &c->s_getters);
                        itable_copy_weak(ty, &c0->s_setters, &c->s_setters);
                        itable_copy_weak(ty, &c0->s_fields,  &c->s_fields);
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
        return class_lookup_s_method_i(ty, class, e->id);
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

        n = itable_get_completions(ty, &C(class)->s_methods, prefix, out, max);
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
        ExprVec *out,
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
        ExprVec *out,
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
        return &C(class)->s_methods;
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
                (field->type == EXPRESSION_EQ)
             && (field->target->type == EXPRESSION_IDENTIFIER)
        ) {
                return field->target;
        }

        return NULL;
}

Expr *
FindMethodImmediate(ExprVec const *ms, char const *name)
{
        char const *dollar;

        for (int i = 0; i < vN(*ms); ++i) {
                if (s_eq(name, v__(*ms, i)->name)) {
                        return v__(*ms, i);
                } else if (
                        (v__(*ms, i)->name[0] == '_')
                     && ((dollar = strchr(name, '$')) != NULL)
                     && (memcmp(name, v__(*ms, i)->name + 1, dollar - name) == 0)
                ) {
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
                Expr *m = FindMethodImmediate(&c->def->class.s_methods, name);
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
FindStaticGetter(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethodImmediate(&c->def->class.s_getters, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindStaticGetter(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Expr *
FindStaticSetter(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindMethodImmediate(&c->def->class.s_setters, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindStaticSetter(v__(c->traits, i), name);
                        if (m != NULL) {
                                return m;
                        }
                }
                c = c->super;
        }

        return NULL;
}

Expr *
FindFieldImmediate(ExprVec const *fs, char const *name)
{
        for (int i = 0; i < vN(*fs); ++i) {
                Expr *field = v__(*fs, i);
                if (s_eq(FieldIdentifier(field)->identifier, name)) {
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

Expr *
FindStaticField(Class const *c, char const *name)
{
        while (c != NULL && c->def != NULL) {
                Expr *m = FindFieldImmediate(&c->def->class.s_fields, name);
                if (m != NULL) {
                        return m;
                }
                for (int i = 0; i < vN(c->traits); ++i) {
                        m = FindStaticField(v__(c->traits, i), name);
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
        eliminate_refs(&c->s_fields);
        eliminate_refs(&c->s_methods);
        eliminate_refs(&c->s_getters);
        eliminate_refs(&c->methods);
        eliminate_refs(&c->getters);
        eliminate_refs(&c->setters);

        if (vN(c->offsets_r) > NAMES.init) {
                u16 off = v__(c->offsets_r, NAMES.init) & OFF_MASK;
                c->init = v__(c->methods.values, off);
        }

        c->really_final = true;
}

static i16
decorated_slot(Class *c, Expr const *meth)
{
        for (int i = 0; i < vN(c->fields.values); ++i) {
                Value const *v = v_(c->fields.values, i);
                if ((v->type == VALUE_PTR) && (v->extra == meth)) {
                        return i;
                }
        }

        UNREACHABLE();
}

static void
cache_offsets(
        Ty *ty,
        Class *c,
        u16Vector *offsets,
        struct itable const *table,
        u8 type,
        Expr *(*find)(Class const *, char const *)
)
{
        for (int i = 0; i < vN(table->ids); ++i) {
                i32 id    = v__(table->ids, i);
                u16 off   = (u16)i;
                u16 flags = type;
                while (vN(*offsets) <= id) {
                        xvP(*offsets, OFF_NOT_FOUND);
                }
                if (find != NULL) {
                        Expr const *meth = (*find)(c, M_NAME(id));
                        if (vN(meth->decorators) > 0) {
                                flags |= OFF_DECORATED;
                                off = decorated_slot(c, meth);
                        }
                }
                *v_(*offsets, id) = (flags << OFF_SHIFT) | off;
        }
}

static void
finalize(Ty *ty, Class *c)
{
        if (c->final) {
                return;
        }

        Value *f = itable_lookup(ty, &c->methods, NAMES._free_);
        if (f != NULL) {
                while (f->type == VALUE_REF) {
                        f = f->ref;
                }
                c->finalizer = *f;
        }

        class_resolve_all(ty, c->i);

        cache_offsets(ty, c, &c->offsets_r, &c->fields,  OFF_FIELD,  NULL);
        cache_offsets(ty, c, &c->offsets_r, &c->methods, OFF_METHOD, FindMethod);
        cache_offsets(ty, c, &c->offsets_r, &c->getters, OFF_GETTER, FindGetter);
        cache_offsets(ty, c, &c->offsets_w, &c->fields,  OFF_FIELD,  NULL);
        cache_offsets(ty, c, &c->offsets_w, &c->setters, OFF_SETTER, FindSetter);

        c->final = true;
}


/* vim: set sts=8 sw=8 expandtab: */
