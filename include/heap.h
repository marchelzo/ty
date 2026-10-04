#ifndef HEAP_H_INCLUDED
#define HEAP_H_INCLUDED

#include "ty.h"
#include "gc.h"

inline static Heap *
heap_new(Ty *ty)
{
        Heap *h = mAo0(sizeof (Heap), GC_HEAP);
        h->order.by  = NONE;
        h->order.cmp = NONE;
        return h;
}

void
heap_mark(Ty *ty, Heap *h);

void
heap_free(Ty *ty, Heap *h);

void
heap_push(Ty *ty, Heap *h, Value x);

Value
builtin_heap(Ty *ty, int argc, Value *kwargs);

void
build_heap_method_table(void);

BuiltinMethod *
get_heap_method_i(int);

BuiltinMethod *
get_heap_view_method_i(int);

#endif
