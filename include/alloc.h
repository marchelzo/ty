#ifndef ALLOC_H_INCLUDED
#define ALLOC_H_INCLUDED

#include <stdlib.h>
#include "panic.h"

#define resize(ptr, n) (((ptr) = realloc((ptr), (n))) || (panic("out of memory"), false))

inline static void *
alloc(size_t n)
{
        void *mem = malloc(n);
        if (mem == NULL) {
                panic("out of memory");
        }

        return mem;
}

#endif
