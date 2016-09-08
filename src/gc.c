#include <string.h>

#include "value.h"
#include "object.h"
#include "vm.h"
#include "log.h"

enum {
        GC_ALLOC_THRESHOLD = (1 << 22) // ~ 4 MB
};

static size_t allocated = 0;
int gc_prevent = 0;

void *
gc_alloc(size_t n)
{
        void *mem = alloc(n);

        allocated += n;

        if (allocated <= GC_ALLOC_THRESHOLD || gc_prevent != 0)
                return mem;

        vm_mark();        

        object_sweep();
        value_array_sweep();
        value_ref_vector_sweep();
        value_string_sweep();
        vm_sweep_variables();

        allocated = 0;

        return mem;
}

void
gc_reset(void)
{
        gc_prevent = 0;
        allocated = 0;
        value_gc_reset();
        object_gc_reset();
}
