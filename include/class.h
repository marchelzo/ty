#ifndef CLASS_H_INCLUDED
#define CLASS_H_INCLUDED

#include <stdbool.h>

#include "value.h"
#include "util.h"

int
class_new(Ty *ty, char const *name, char const *doc);

int
class_lookup(Ty *ty, char const *name);

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
class_lookup_getter(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_setter(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_static(Ty *ty, int class, char const *name, unsigned long h);

struct value *
class_lookup_immediate(Ty *ty, int class, char const *name, unsigned long h);

inline static struct value *
class_method(Ty *ty, int class, char const *name)
{
        return class_lookup_method(ty, class, name, strhash(name));
}

char const *
class_method_name(Ty *ty, int class, char const *name);

char const *
class_doc(Ty *ty, int class);

void
class_set_super(Ty *ty, int class, int super);

bool
class_is_subclass(Ty *ty, int sub, int super);

int
class_get_completions(Ty *ty, int class, char const *prefix, char **out, int max);

struct table *
class_methods(Ty *ty, int class);

struct table *
class_static_methods(Ty *ty, int class);

struct table *
class_getters(Ty *ty, int class);

struct table *
class_setters(Ty *ty, int class);

#endif
