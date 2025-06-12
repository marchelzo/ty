#ifndef VEC_H_INCLUDED
#define VEC_H_INCLUDED

#include <stddef.h>

typedef size_t vec_z;

inline static vec_z
fit2(vec_z cap, vec_z min)
{
        while (cap < min) {
                cap <<= 1;
        }

        return cap;
}

#define intrusive_vec(T) \
        T *items;        \
        vec_z count;     \
        vec_z capacity

#define vec(T) struct { intrusive_vec(T); }

#define vec_init(v, ...) (                      \
        ((v).items    = NULL),                  \
        ((v).count    = 0),                     \
        ((v).capacity = -(__VA_ARGS__ + 0))     \
)

#define vec_get(v, idx) ((v).items + idx)
#define vec_len(v) ((v).count)
#define vec_last(v) ((v).items + (v).count - 1)

#define vec_full(v) (vec_capacity(v) <= (v).count)
#define vec_capacity(v) (((v).capacity <= 0) ? 0 : (v).capacity)

#define vec_new_capacity(v) (                     \
          ((v).capacity > 0) ? (2 * (v).capacity) \
        : ((v).capacity < 0) ? (-(v).capacity)    \
        : 4L                                      \
)

#define vec_pop(v) (                    \
        UNLIKELY((v).count == 0)        \
      ? NULL                            \
      : ((v).items + --(v).count)       \
)

#define vec_pop_ith(v, i) __builtin_memmove(            \
        (v).items + (i),                                \
        (v).items + (i) + 1,                            \
        (--(v).count - (i)) * sizeof (*((v).items))     \
)

#define vec_empty(v) do {       \
        (v).capacity = 0;       \
        (v).count = 0;          \
        gc_free(ty, (v).items); \
        (v).items = NULL;       \
} while (0)

#define vec_push_(v, item, rsz) (                                                       \
          UNLIKELY(vec_full(v))                                                         \
        ? (                                                                             \
                rsz(                                                                    \
                        (v).items,                                                      \
                        ((v).capacity = vec_new_capacity(v)) * (sizeof (*(v).items)),   \
                        ((v).count * (sizeof (*(v).items)))                             \
                ),                                                                      \
                ((v).items[(v).count] = (item)),                                        \
                ((v).count += 1),                                                       \
                ((v).items + (v).count - 1)                                             \
        ) : (                                                                           \
                ((v).items[(v).count] = (item)),                                        \
                ((v).count += 1),                                                       \
                ((v).items + (v).count - 1)                                             \
        )                                                                               \
)

#define vec_push_n_(v, elements, n, rsz) (                              \
          ((v).count + (n) > (v).capacity)                              \
        ? (                                                             \
                rsz(                                                    \
                        (v).items,                                      \
                        (sizeof *((v).items)) * ((v).capacity = fit2(   \
                                vec_new_capacity(v),                    \
                                ((v).count + (n))                       \
                        )),                                             \
                        ((v).count * (sizeof (*(v).items)))             \
                ),                                                      \
                __builtin_memcpy(                                       \
                        (v).items + (v).count,                          \
                        (elements),                                     \
                        (n) * (sizeof (*(v).items))                     \
                ),                                                      \
                ((v).count += (n))                                      \
        ) : (                                                           \
                __builtin_memcpy(                                       \
                        (v).items + (v).count,                          \
                        (elements),                                     \
                        (n) * (sizeof (*(v).items))                     \
                ),                                                      \
                ((v).count += (n))                                      \
        )                                                               \
)

#define vec_insert_(v, item, i, rsz) (                          \
        vec_reserve_((v), (v).count + 1, rsz),                  \
        __builtin_memmove(                                      \
                (v).items + (i) + 1,                            \
                (v).items + (i),                                \
                ((v).count - (i)) * (sizeof (*(v).items))       \
        ),                                                      \
        ((v).items[(i)] = (item)),                              \
        ((v).count += 1)                                        \
)

#define vec_insert_n_(v, elems, n, i, rsz) (                    \
        vec_reserve_((v), (v).count + (n), rsz),                \
        __builtin_memmove(                                      \
                (v).items + (i) + (n),                          \
                (v).items + (i),                                \
                ((v).count - (i)) * (sizeof (*(v).items))       \
        ),                                                      \
        __builtin_memcpy(                                       \
                (v).items + (i),                                \
                (elems),                                        \
                (n) * (sizeof (*(v).items))                     \
        ),                                                      \
        ((v).count += (n))                                      \
)

#define vec_reserve_(v, n, rsz) (                               \
        ((v).capacity < (n)) &&                                 \
        (                                                       \
                ((v).capacity = (n)),                           \
                rsz(                                            \
                        (v).items,                              \
                        (v).capacity * (sizeof (*(v).items)),   \
                        (v).count    * (sizeof (*(v).items))    \
                )                                               \
        )                                                       \
)

#define vec_resize(p, n, m) resize((p), (n))
#define vec_reserve(v, n) vec_reserve_((v), (n), vec_resize)
#define vec_push(v, x) vec_push_((v), (x), vec_resize)
#define vec_push_n(v, xs, n) vec_push_n_((v), (xs), (n), vec_resize)
#define vec_insert(v, x, i) vec_insert_((v), (x), (i), vec_resize)
#define vec_insert_n(v, xs, n, i) vec_insert_n_((v), (xs), (n), (i), vec_resize)

#define vec_resize_unchecked(p, n, m) resize_unchecked((p), (n))
#define vec_reserve_unchecked(v, n) vec_reserve_((v), (n), vec_resize_unchecked)
#define vec_push_unchecked(v, x) vec_push_((v), (x), vec_resize_unchecked)
#define vec_push_n_unchecked(v, xs, n) vec_push_n_((v), (xs), (n), vec_resize_unchecked)
#define vec_insert_unchecked(v, x, i) vec_insert_((v), (x), (i), vec_resize_unchecked)
#define vec_insert_n_unchecked(v, xs, n, i) vec_insert_n_((v), (xs), (n), (i), vec_resize_unchecked)

#define vec_resize_nogc(p, n, m) mresize((p), (n))
#define vec_nogc_reserve(v, n) vec_reserve_((v), (n), vec_resize_nogc)
#define vec_nogc_push(v, x) vec_push_((v), (x), vec_resize_nogc)
#define vec_nogc_push_n(v, xs, n) vec_push_n_((v), (xs), (n), vec_resize_nogc)
#define vec_nogc_insert(v, x, i) vec_insert_((v), (x), (i), vec_resize_nogc)
#define vec_nogc_insert_n(v, xs, n, i) vec_insert_n_((v), (xs), (n), (i), vec_resize_nogc)

#define vec_resize_scratch(p, n, m) resize_scratch((p), (n), (m))
#define vec_reserve_scratch(v, n) vec_reserve_((v), (n), vec_resize_scratch)
#define vec_push_scratch(v, x) vec_push_((v), (x), vec_resize_scratch)
#define vec_push_n_scratch(v, xs, n) vec_push_n_((v), (xs), (n), vec_resize_scratch)
#define vec_insert_scratch(v, x, i) vec_insert_((v), (x), (i), vec_resize_scratch)
#define vec_insert_n_scratch(v, xs, n, i) vec_insert_n_((v), (xs), (n), (i), vec_resize_scratch)

#define vec_resize_arena(p, n, m) Resize((p), (n), (m))
#define VReserve(v, n) vec_reserve_((v), (n), vec_resize_arena)
#define VPush(v, x) vec_push_((v), (x), vec_resize_arena)
#define VPushN(v, xs, n) vec_push_n_((v), (xs), (n), vec_resize_arena)
#define VInsert(v, x, i) vec_insert_((v), (x), (i), vec_resize_arena)
#define VInsertN(v, xs, n, i) vec_insert_n_((v), (xs), (n), (i), vec_resize_arena)

#endif
