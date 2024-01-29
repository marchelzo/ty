#include <stdlib.h>

inline static void *
gc_resize(void *p, size_t n);

#include "panic.h"
#include "gc.h"
#include "alloc.h"

#define vec(T) \
        struct { \
                T *items; \
                size_t count; \
                size_t capacity; \
        }

#define vec_get(v, idx) \
        ((v).items + idx)

#define vec_push(v, item) \
          (((v).count == (v).capacity) \
        ? ((resize((v).items, ((v).capacity = ((v).capacity == 0 ? 4 : ((v).capacity * 2))) * (sizeof (*(v).items)))), \
                        ((v).items[(v).count] = (item)), \
						(v).count += 1, \
                        ((v).items + (v).count - 1)) \
        : (((v).items[(v).count] = (item)), \
				(v).count += 1, \
                ((v).items + (v).count - 1)))

#define vec_push_unchecked(v, item) \
          (((v).count == (v).capacity) \
        ? ((resize_unchecked((v).items, ((v).capacity = ((v).capacity == 0 ? 4 : ((v).capacity * 2))) * (sizeof (*(v).items)))), \
                        ((v).items[(v).count] = (item)), \
						(v).count += 1, \
                        ((v).items + (v).count - 1)) \
        : (((v).items[(v).count] = (item)), \
				(v).count += 1, \
                ((v).items + (v).count - 1)))

#define vec_push_n(v, elements, n) \
          (((v).count + (n) >= (v).capacity) \
        ? ((resize((v).items, (((v).capacity = ((v).capacity + ((n) + 16))) * (sizeof (*(v).items)))), \
                        (memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                        ((v).count += (n)))) \
        : ((memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                ((v).count += (n))))

#define vec_push_n_unchecked(v, elements, n) \
          (((v).count + (n) >= (v).capacity) \
        ? ((resize_unchecked((v).items, (((v).capacity = ((v).capacity + ((n) + 16))) * (sizeof (*(v).items)))), \
                        (memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                        ((v).count += (n)))) \
        : ((memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                ((v).count += (n))))

#define vec_pop(v) \
    ((v).count == 0 ? NULL : (v).items + --(v).count)

#define vec_pop_ith(v, i) \
    ((((v).items)[(i)]), (memmove((v).items + (i), (v).items + (i) + 1, (--(v).count - (i)) * sizeof (*((v).items)))))

#define vec_init(v) \
    (((v).capacity = 0), ((v).count = 0), ((v).items = NULL))

#define vec_empty(v) \
    (((v).capacity = 0), ((v).count = 0), gc_free((v).items), ((v).items = NULL))

#define vec_insert(v, item, i) \
        ((vec_reserve((v), (v).count + 1)), memmove((v).items + (i) + 1, (v).items + (i), ((v).count - (i)) * (sizeof (*(v).items))), ((v).items[(i)] = (item)), ++(v).count)

#define vec_insert_n(v, elems, n, i) \
        ((vec_reserve((v), (v).count + (n))), memmove((v).items + (i) + (n), (v).items + (i), ((v).count - (i)) * (sizeof (*(v).items))), memcpy((v).items + (i), (elems), (n) * (sizeof (*(v).items))), (v).count += (n))

#define vec_len(v) ((v).count)

#define vec_last(v) ((v).items + (v).count - 1)

#define vec_reserve(v, n) \
        (((v).capacity < (n)) && (((v).capacity = (n)), resize((v).items, (v).capacity * (sizeof (*(v).items)))))

#define vec_for_each(v, idx, name) for (size_t idx = 0; ((name) = vec_get((v), idx)), idx < (v).count; ++idx)

#define vec_nogc_push(v, item) \
          (((v).count == (v).capacity) \
        ? ((resize_nogc((v).items, ((v).capacity = ((v).capacity == 0 ? 4 : ((v).capacity * 2))) * (sizeof (*(v).items)))), \
                        ((v).items[(v).count] = (item)), \
						(v).count += 1, \
                        ((v).items + (v).count - 1)) \
        : (((v).items[(v).count] = (item)), \
				(v).count += 1, \
                ((v).items + (v).count - 1)))

#define vec_nogc_push_n(v, elements, n) \
          (((v).count + (n) >= (v).capacity) \
        ? ((resize_nogc((v).items, (((v).capacity = ((v).capacity + ((n) + 16))) * (sizeof (*(v).items)))), \
                        (memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                        ((v).count += (n)))) \
        : ((memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                ((v).count += (n))))

#define VPush(v, item) \
          (((v).count == (v).capacity) \
        ? ((Resize((v).items, (((v).capacity == 0 ? 4 : ((v).capacity * 2)) * (sizeof (*(v).items))), ((v).capacity * sizeof (*(v).items))), \
                        ((v).capacity = ((v).capacity == 0 ? 4 : ((v).capacity * 2))), \
                        ((v).items[(v).count] = (item)), \
						(v).count += 1, \
                        ((v).items + (v).count - 1))) \
        : (((v).items[(v).count] = (item)), \
				(v).count += 1, \
                ((v).items + (v).count - 1)))

#define VPushN(v, elements, n) \
          (((v).count + (n) >= (v).capacity) \
        ? ((Resize((v).items, (((v).capacity + ((n) + 16)) * (sizeof (*(v).items))), ((v).capacity * sizeof (*(v).items))), \
                        (((v).capacity = (v).capacity + (n) + 16)), \
                        (memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                        ((v).count += (n)))) \
        : ((memcpy((v).items + (v).count, (elements), ((n) * (sizeof (*(v).items))))), \
                ((v).count += (n))))

#define VReserve(v, n) \
        (((v).capacity < (n)) && (Resize((v).items, ((v).capacity + (n)) * (sizeof (*(v).items)), ((v).capacity * sizeof (*(v).items))), ((v).capacity += (n))))

#define VInsert(v, item, i) \
        ((VReserve((v), (v).count + 1)), memmove((v).items + (i) + 1, (v).items + (i), ((v).count - (i)) * (sizeof (*(v).items))), ((v).items[(i)] = (item)), ++(v).count)

#define VInsertN(v, elems, n, i) \
        ((VReserve((v), (v).count + (n))), memmove((v).items + (i) + (n), (v).items + (i), ((v).count - (i)) * (sizeof (*(v).items))), memcpy((v).items + (i), (elems), (n) * (sizeof (*(v).items))), (v).count += (n))
