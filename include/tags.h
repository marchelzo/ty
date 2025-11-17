#ifndef TAGS_H_INCLUDED
#define TAGS_H_INCLUDED

#include <stdbool.h>

#include "ty.h"

typedef struct class Class;

void
tags_init(Ty *ty);

int
tags_new(Ty *ty, char const *);

int
tags_new(Ty *ty, char const *);

void
tags_set_class(Ty *ty, int tag, Class *c);

Class *
tags_get_class(Ty *ty, int tag);

bool
tags_same(Ty *ty, int t1, int t2);

int
tags_push(Ty *ty, int n, int tag);

int
tags_pop(Ty *ty, int n);

bool
tags_try_pop(Ty *ty, u16 *tags, int tag);

int
tags_first(Ty *ty, int tags);

char *
tags_wrap(Ty *ty, char const *s, int tags, bool color);

char const *
tags_name(Ty *ty, int tag);

int
tags_lookup(Ty *ty, char const *name);

void
tags_add_method(Ty *ty, int tag, char const *name, struct value f);

void
tags_add_static(Ty *ty, int tag, char const *name, Value f);

Value *
tags_lookup_method_i(Ty *ty, int tag, int i);

Value *
tags_lookup_static(Ty *ty, int tag, int i);

void
tags_copy_methods(Ty *ty, int dst, int src);

#endif
