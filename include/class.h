#ifndef CLASS_H_INCLUDED
#define CLASS_H_INCLUDED

#include <stdbool.h>

#include "value.h"
#include "util.h"
#include "itable.h"

typedef struct class Class;
typedef struct type Type;

struct class {
        int i;
        int ti;
        bool is_trait;
        bool final;
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
class_add_method(Ty *ty, int class, char const *name, struct value f);

struct value
class_get_finalizer(Ty *ty, int class);

void
class_add_static(Ty *ty, int class, char const *name, struct value f);

void
class_add_getter(Ty *ty, int class, char const *name, struct value f);

void
class_add_setter(Ty *ty, int class, char const *name, struct value f);

void
class_copy_methods(Ty *ty, int dst, int src);

struct value *
class_lookup_method(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_field_i(Ty *ty, int class, int id);

Class *
class_get_class(Ty *ty, int class);

struct value *
class_lookup_getter(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_setter(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_static(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_immediate(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_method_i(Ty *ty, int class, int id);

struct value *
class_lookup_getter_i(Ty *ty, int class, int id);

struct value *
class_lookup_setter_i(Ty *ty, int class, int id);

struct value *
class_lookup_static_i(Ty *ty, int class, int id);

struct value *
class_lookup_immediate_i(Ty *ty, int class, int id);

inline static struct value *
class_method(Ty *ty, int class, char const *name)
{
        return class_lookup_method(ty, class, name, 0);
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
class_completions(Ty *ty, int class, char const *prefix, expression_vector *out);

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

#endif
