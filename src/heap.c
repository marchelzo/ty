#include "ty.h"
#include "value.h"
#include "array.h"
#include "heap.h"
#include "vm.h"
#include "gc.h"
#include "xd.h"

static char const *ViewMethods[] = {
        "all?",      "any?",      "choice",    "compact",   "contains?",
        "count",     "countBy",   "drop",      "dropWhile", "enumerate",
        "filter",    "find",      "findr",     "flat",      "fold",
        "foldr",     "group",     "groupBy",   "groupsOf",  "intersperse",
        "join",      "map",       "max",       "maxBy",     "min",
        "minBy",     "nub",       "partition", "remove",    "reverse",
        "rotate",    "sample",    "scan",      "scanr",     "search",
        "searchBy",  "searchr",   "searchrBy", "set",       "shuffle",
        "slice",     "sortBy",    "sortOn",    "split",     "sum",
        "take",      "takeWhile", "tally",     "tuple",     "uniq",
        "window",    "zip",
};

static vec(BuiltinMethod *) view_table;

inline static bool
above(Ty *ty, Heap const *h, usize i, usize j)
{
        return sort_order_cmp(ty, &h->order, v_(h->xs, i), v_(h->xs, j)) < 0;
}

static void
sift_up(Ty *ty, Heap *h, usize i)
{
        while (i > 0) {
                usize p = (i - 1) / 2;
                if (!above(ty, h, i, p)) {
                        break;
                }
                SWAP(Value, *v_(h->xs, i), *v_(h->xs, p));
                i = p;
        }
}

static void
sift_down(Ty *ty, Heap *h, usize i, usize n)
{
        for (usize l; (l = 2 * i + 1) < n; ) {
                usize c = ((l + 1 < n) && above(ty, h, l + 1, l)) ? l + 1 : l;
                if (!above(ty, h, c, i)) {
                        break;
                }
                SWAP(Value, *v_(h->xs, i), *v_(h->xs, c));
                i = c;
        }
}

static void
heapify(Ty *ty, Heap *h)
{
        for (usize i = vN(h->xs) / 2; i --> 0;) {
                sift_down(ty, h, i, vN(h->xs));
        }
}

inline static Value
take_top(Ty *ty, Heap *h)
{
        Value top = v__(h->xs, 0);

        *v_(h->xs, 0) = *vvL(h->xs);
        vN(h->xs) -= 1;
        sift_down(ty, h, 0, vN(h->xs));

        return top;
}

void
heap_push(Ty *ty, Heap *h, Value x)
{
        uvP(h->xs, x);
        sift_up(ty, h, vN(h->xs) - 1);
}

void
heap_mark(Ty *ty, Heap *h)
{
        if (MARKED(h)) return;

        MARK(h);

        for (usize i = 0; i < vN(h->xs); ++i) {
                xvP(ty->marking, v_(h->xs, i));
        }

        if (!IsNone(h->order.by)) {
                xvP(ty->marking, &h->order.by);
        }

        if (!IsNone(h->order.cmp)) {
                xvP(ty->marking, &h->order.cmp);
        }
}

void
heap_free(Ty *ty, Heap *h)
{
        mF(h->xs.items);
}

Value
builtin_heap(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap()", 0, 1);

        Value h = HEAP(heap_new(ty));

        gP(&h);

        h.heap->order = sort_order(ty, kwargs, "Heap()");

        if (argc == 1) {
                Value xs = ARG(0);
                Value x;
                if (xs.type == VALUE_ARRAY) {
                        for (usize i = 0; i < vN(*xs.array); ++i) {
                                uvP(h.heap->xs, v__(*xs.array, i));
                        }
                } else {
                        vm_iter_begin(ty, xs);
                        while (vm_iter_next(ty, &x)) {
                                uvP(h.heap->xs, x);
                        }
                }
                heapify(ty, h.heap);
        }

        gX();

        return h;
}

static Value
heap_push_m(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Heap.push()", 1);

        for (int i = 0; i < argc; ++i) {
                heap_push(ty, self->heap, ARG(i));
        }

        return *self;
}

static Value
heap_pop(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.pop()", 0);

        if (vN(self->heap->xs) == 0) {
                bP("empty heap");
        }

        return take_top(ty, self->heap);
}

static Value
heap_try_pop(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.try-pop()", 0);
        return (vN(self->heap->xs) == 0) ? None : Some(take_top(ty, self->heap));
}

static Value
heap_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.peek()", 0);

        if (vN(self->heap->xs) == 0) {
                bP("empty heap");
        }

        return v__(self->heap->xs, 0);
}

static Value
heap_try_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.try-peek()", 0);
        return (vN(self->heap->xs) == 0) ? None : Some(v__(self->heap->xs, 0));
}

static Value
heap_push_pop(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.push-pop()", 1);

        Heap *h = self->heap;
        Value x = ARG(0);

        if (
                (vN(h->xs) == 0)
             || (sort_order_cmp(ty, &h->order, v_(h->xs, 0), &x) >= 0)
        ) {
                return x;
        }

        SWAP(Value, x, *v_(h->xs, 0));
        sift_down(ty, h, 0, vN(h->xs));

        return x;
}

static Value
heap_replace(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.replace()", 1);

        Heap *h = self->heap;

        if (vN(h->xs) == 0) {
                bP("empty heap");
        }

        Value top = v__(h->xs, 0);
        *v_(h->xs, 0) = ARG(0);
        sift_down(ty, h, 0, vN(h->xs));

        return top;
}

static Value
heap_len(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.len()", 0);
        return INTEGER(vN(self->heap->xs));
}

static Value
heap_empty(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.empty?()", 0);
        return BOOLEAN(vN(self->heap->xs) == 0);
}

static Value
heap_clear(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.clear()", 0);
        vN(self->heap->xs) = 0;
        return *self;
}

static Value
heap_clone(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.clone()", 0);

        Value h = HEAP(heap_new(ty));

        gP(&h);
        h.heap->order = self->heap->order;
        uvPn(h.heap->xs, vv(self->heap->xs), vN(self->heap->xs));
        gX();

        return h;
}

static Value
heap_to_array(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.to-array()", 0);
        return ARRAY(ArrayClone(ty, &self->heap->xs));
}

static Value
heap_sort(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Heap.sort()", 0);

        SortOrder order = sort_order(ty, kwargs, "Heap.sort()");

        if (IsNone(order.by) && IsNone(order.cmp)) {
                order.by   = self->heap->order.by;
                order.cmp  = self->heap->order.cmp;
                order.desc = self->heap->order.desc != order.desc;
        }

        Value out = ARRAY(ArrayClone(ty, &self->heap->xs));

        gP(&out);

        Heap tmp = { .xs = *out.array, .order = order };

        heapify(ty, &tmp);

        for (usize n = vN(tmp.xs); n > 1; --n) {
                SWAP(Value, *v_(tmp.xs, 0), *v_(tmp.xs, n - 1));
                sift_down(ty, &tmp, 0, n - 1);
        }

        for (usize i = 0, j = vN(tmp.xs); i + 1 < j; ++i, --j) {
                SWAP(Value, *v_(tmp.xs, i), *v_(tmp.xs, j - 1));
        }

        gX();

        return out;
}

DEFINE_METHOD_TABLE(
        heap,
        { .name = "clear",   .func = heap_clear    },
        { .name = "clone",   .func = heap_clone    },
        { .name = "empty?",  .func = heap_empty    },
        { .name = "len",     .func = heap_len      },
        { .name = "peek",    .func = heap_peek     },
        { .name = "pop",     .func = heap_pop      },
        { .name = "push",    .func = heap_push_m   },
        { .name = "pushPop", .func = heap_push_pop },
        { .name = "replace", .func = heap_replace  },
        { .name = "sort",    .func = heap_sort     },
        { .name = "toArray", .func = heap_to_array },
        { .name = "tryPeek", .func = heap_try_peek },
        { .name = "tryPop",  .func = heap_try_pop  },
);

DEFINE_METHOD_LOOKUP(heap);

void
build_heap_method_table(void)
{
        for (int i = 0; i < countof(heap_funcs); ++i) {
                InternEntry *e = intern(&xD.members, heap_funcs[i].name);
                while (heap_table.count <= e->id) {
                        xvP(heap_table, NULL);
                }
                heap_table.items[e->id] = heap_funcs[i].func;
        }

        for (int i = 0; i < countof(ViewMethods); ++i) {
                InternEntry *e = intern(&xD.members, ViewMethods[i]);
                while (view_table.count <= e->id) {
                        xvP(view_table, NULL);
                }
                view_table.items[e->id] = get_array_method(ViewMethods[i]);
        }
}

BuiltinMethod *
get_heap_view_method_i(int i)
{
        return (i < view_table.count) ? view_table.items[i] : NULL;
}
