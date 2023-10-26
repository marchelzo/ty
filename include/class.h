#ifndef CLASS_H_INCLUDED
#define CLASS_H_INCLUDED

#include <stdbool.h>

#include "value.h"
#include "util.h"

int
class_new(char const *name);

int
class_lookup(char const *name);

char const *
class_name(int class);

void
class_add_method(int class, char const *name, struct value f);

struct value
class_get_finalizer(int class);

void
class_add_static(int class, char const *name, struct value f);

void
class_add_getter(int class, char const *name, struct value f);

void
class_add_setter(int class, char const *name, struct value f);

void
class_copy_methods(int dst, int src);

struct value *
class_lookup_method(int class, char const *name, unsigned long h);

struct value *
class_lookup_getter(int class, char const *name, unsigned long h);

struct value *
class_lookup_setter(int class, char const *name, unsigned long h);

struct value *
class_lookup_static(int class, char const *name, unsigned long h);

struct value *
class_lookup_immediate(int class, char const *name, unsigned long h);

inline static struct value *
class_method(int class, char const *name)
{
        return class_lookup_method(class, name, strhash(name));
}

char const *
class_method_name(int class, char const *name);

void
class_set_super(int class, int super);

bool
class_is_subclass(int sub, int super);

int
class_get_completions(int class, char const *prefix, char **out, int max);

#endif
