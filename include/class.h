#ifndef CLASS_H_INCLUDED
#define CLASS_H_INCLUDED

#include <stdbool.h>

#include "value.h"
#include "util.h"
#include "itable.h"

typedef struct class Class;
typedef struct type Type;

typedef vec(Class *) ClassVector;

struct class {
        int i;
        int ti;
        bool is_trait;
        bool final;
        bool really_final;
        Class *super;
        struct itable methods;
        struct itable setters;
        struct itable getters;
        struct itable statics;
        struct itable fields;
        vec(bool) impls;
        vec(Class *) traits;
        Value finalizer;
        char const *name;
        char const *doc;
        Stmt *def;
        Type *type;
        Type *object_type;
};

Class *
class_get(Ty *ty, int id);

#define LOOKUP_IMPL_FOR(what)                                 \
inline static Value *                                         \
class_lookup_##what##_i(Ty *ty, int class, int id)            \
{                                                             \
        Class *c = class_get(ty, class);                      \
        Value *v = itable_lookup(ty, &c->what##s, id);        \
        if (v == NULL) {                                      \
                return NULL;                                  \
        }                                                     \
        if (v->type != VALUE_REF) {                           \
                return v;                                     \
        }                                                     \
        return (v->ref->type != VALUE_ZERO) ? v->ref : NULL;  \
}                                                             \
inline static Value *                                         \
class_lookup_##what##_immediate_i(Ty *ty, int class, int id)  \
{                                                             \
        Value *v = class_lookup_##what##_i(ty, class, id);    \
        if (v == NULL || v->type == VALUE_REF) {              \
                return NULL;                                  \
        }                                                     \
        if (class_of(v) != class) {                           \
                return NULL;                                  \
        }                                                     \
        return v;                                             \
}
LOOKUP_IMPL_FOR(method);
LOOKUP_IMPL_FOR(static);
LOOKUP_IMPL_FOR(getter);
LOOKUP_IMPL_FOR(setter);
#undef LOOKUP_IMPL_FOR

typedef void (add_to_class_fn)(Ty *, int, char const *, Value);

void
class_init(Ty *ty);

int
class_new(Ty *ty, Stmt *s);

Class *
class_new_empty(Ty *ty);

void
class_builtin(Ty *ty, int class, Stmt *def);

int
trait_new(Ty *ty, Stmt *s);

char const *
class_name(Ty *ty, int class);

void
class_add_method(Ty *ty, int class, char const *name, Value f);

Value
class_get_finalizer(Ty *ty, int class);

void
class_add_static(Ty *ty, int class, char const *name, Value f);

void
class_add_static_i(Ty *ty, int class, int id, Value f);

void
class_add_getter(Ty *ty, int class, char const *name, Value f);

void
class_add_getter_i(Ty *ty, int class, int id, Value f);

void
class_add_method_i(Ty *ty, int class, int id, Value f);

void
class_add_setter_i(Ty *ty, int class, int id, Value f);

void
class_add_setter(Ty *ty, int class, char const *name, Value f);

void
class_copy_methods(Ty *ty, int dst, int src);

Value *
class_lookup_method(Ty *ty, int class, char const *name, unsigned long h);

Value *
class_lookup_field_i(Ty *ty, int class, int id);

Value *
class_lookup_getter(Ty *ty, int class, char const *name, unsigned long h);

Value *
class_lookup_setter(Ty *ty, int class, char const *name, unsigned long h);

Value *
class_lookup_static(Ty *ty, int class, char const *name, unsigned long h);

Value *
class_lookup_immediate(Ty *ty, int class, char const *name, unsigned long h);

Value *
class_lookup_immediate_i(Ty *ty, int class, int id);

inline static Value *
class_method(Ty *ty, int class, char const *name)
{
        return class_lookup_method_i(ty, class, M_ID(name));
}
void
class_add_field(Ty *ty, int class, char const *name, Expr *t, Expr *dflt);

void
class_init_object(Ty *ty, int class, struct itable *o);

char const *
class_method_name(Ty *ty, int class, char const *name);

char const *
class_doc(Ty *ty, int class);

void
class_set_super(Ty *ty, int class, int super);

int
class_get_super(Ty *ty, int class);

bool
class_is_subclass(Ty *ty, int sub, int super);

bool
class_is_trait(Ty *ty, int class);

void
class_implement_trait(Ty *ty, int class, int trait);

int
class_get_completions(Ty *ty, int class, char const *prefix, char **out, int max);

int
class_completions(
        Ty *ty,
        int class,
        char const *prefix,
        expression_vector *out,
        int_vector *depths
);

struct itable *
class_methods(Ty *ty, int class);

struct itable *
class_static_methods(Ty *ty, int class);

struct itable *
class_getters(Ty *ty, int class);

struct itable *
class_setters(Ty *ty, int class);

void
class_finalize_all(Ty *ty);

Expr *
FieldIdentifier(Expr const *field);

Expr *
FindGetter(Class const *c, char const *name);

Expr *
FindSetter(Class const *c, char const *name);

Expr *
FindMethod(Class const *c, char const *name);

Expr *
FindStatic(Class const *c, char const *name);

Expr *
FindMethodImmediate(expression_vector const *ms, char const *name);

Expr *
FindField(Class const *c, char const *name);

Expr *
FindFieldImmediate(expression_vector const *fs, char const *name);

inline static Expr *
ClassFindInstMember(Class const *c, char const *name)
{
        Expr const *member;

        if ((member = FindMethod(c, name)) != NULL) {
                return (Expr *)member;
        }

        if ((member = FindGetter(c, name)) != NULL) {
                return (Expr *)member;
        }

        if ((member = FindSetter(c, name)) != NULL) {
                return (Expr *)member;
        }

        if ((member = FindField(c, name)) != NULL) {
                return (Expr *)member;
        }

        return NULL;
}

inline static Expr *
ClassFindInstMemberImmediate(Class const *c, char const *name)
{
        Expr const *member;

        if (c->def == NULL) {
                return NULL;
        }

        if ((member = FindMethodImmediate(&c->def->class.methods, name)) != NULL) {
                return (Expr *)member;
        }

        if ((member = FindMethodImmediate(&c->def->class.getters, name)) != NULL) {
                return (Expr *)member;
        }

        if ((member = FindMethodImmediate(&c->def->class.setters, name)) != NULL) {
                return (Expr *)member;
        }

        return FindFieldImmediate(&c->def->class.fields, name);
}

inline static Expr *
ClassFindMember(Class const *c, char const *name)
{
        Expr const *member;

        if ((member = ClassFindInstMember(c, name)) != NULL) {
                return (Expr *)member;
        }

        return FindStatic(c, name);
}

inline static Expr *
ClassFindMemberImmediate(Class const *c, char const *name)
{
        Expr const *member;

        if ((member = ClassFindInstMemberImmediate(c, name)) != NULL) {
                return (Expr *)member;
        }

        if (c->def == NULL) {
                return NULL;
        }

        return FindMethodImmediate(&c->def->class.statics, name);
}

#endif
