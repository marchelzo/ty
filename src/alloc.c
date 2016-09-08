#include "alloc.h"
#include "panic.h"

#include <string.h>

void *
alloc(size_t n)
{
        void *mem = malloc(n);
        if (mem == NULL) {
                panic("out of memory");
        }
#ifndef PLUM_RELEASE
        memset(mem, 0, n);
#endif
        return mem;
}
