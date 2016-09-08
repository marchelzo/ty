#ifndef TAGS_H_INCLUDED
#define TAGS_H_INCLUDED

#include <stdbool.h>

void
tags_init(void);

int
tags_new(char const *);

bool
tags_same(int t1, int t2);

int
tags_push(int n, int tag);

int
tags_pop(int n);

int
tags_first(int tags);

char const *
tags_wrap(char const *s, int tags);

char const *
tags_name(int tag);

#endif
