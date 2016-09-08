#ifndef ALLOC_H_INCLUDED
#define ALLOC_H_INCLUDED

#include <stdlib.h>

#define resize(ptr, n) (((ptr) = realloc((ptr), (n))) || (panic("out of memory"), false))

void *
alloc(size_t n);

#endif
