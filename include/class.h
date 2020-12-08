#ifndef CLASS_H_INCLUDED
#define CLASS_H_INCLUDED

#include <stdbool.h>

#include "value.h"

int
class_new(char const *name);

int
class_lookup(char const *name);

char const *
class_name(int class);

void
class_add_method(int class, char const *name, struct value f);

void
class_copy_methods(int dst, int src);

struct value *
class_lookup_method(int class, char const *name);

void
class_set_super(int class, int super);

#endif
