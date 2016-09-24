#include <string.h>

#include "value.h"
#include "gc.h"
#include "object.h"
#include "vm.h"
#include "log.h"

#define GC_ALLOC_THRESHOLD (1ULL << 22)

static size_t allocated = 0;
static vec(struct value *) root_set;

void *
gc_alloc(size_t n)
{
        void *mem = alloc(n);

        allocated += n;

        if (allocated <= GC_ALLOC_THRESHOLD)
                return mem;

        vm_mark();
        for (int i = 0; i < root_set.count; ++i)
                value_mark(root_set.items[i]);

        object_sweep();
        value_array_sweep();
        value_ref_vector_sweep();
        value_string_sweep();
        value_blob_sweep();
        vm_sweep_variables();

        allocated = 0;

        return mem;
}

void
gc_reset(void)
{
        allocated = 0;
        value_gc_reset();
        object_gc_reset();
}

void
gc_push(struct value *v)
{
        vec_push(root_set, v);
}

void
gc_pop(void)
{
        --root_set.count;
}

void
gc_clear_root_set(void)
{
        root_set.count = 0;
}
