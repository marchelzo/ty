#include "value.h"
#include "itable.h"
#include "vec.h"
#include "util.h"

inline static void
xsort7(struct itable *t)
{
        int * restrict const ids = t->ids.items;
        Value * restrict const vals = t->values.items;
        /*
         * [(0,6),(2,3),(4,5)]
         * [(0,2),(1,4),(3,6)]
         * [(0,1),(2,5),(3,4)]
         * [(1,2),(4,6)]
         * [(2,3),(4,5)]
         * [(1,2),(3,4),(5,6)]
         */
#define ORDER(i, j)                              \
        if (ids[i] > ids[j]) {                   \
                SWAP(int, ids[i], ids[j]);       \
                SWAP(Value, vals[i], vals[j]);   \
        }

        ORDER(0, 6);
        ORDER(2, 3);
        ORDER(4, 5);

        ORDER(0, 2);
        ORDER(1, 4);
        ORDER(3, 6);

        ORDER(0, 1);
        ORDER(2, 5);
        ORDER(3, 4);

        ORDER(1, 2);
        ORDER(4, 6);

        ORDER(2, 3);
        ORDER(4, 5);

        ORDER(1, 2);
        ORDER(3, 4);
        ORDER(5, 6);

#undef ORDER
}

inline static Value *
xfind(struct itable const *t, int64_t id)
{
        for (int i = 0; i < vN(t->ids); ++i) {
                if (v__(t->ids, i) == id) {
                        return v_(t->values, i);
                }
        }

        return NULL;
}

static bool
bfind(struct itable const *t, int64_t id, int * restrict i)
{
        int const * restrict ids = t->ids.items;
        int n = vN(t->ids);

        int i_ = 0;
        int lo = 0;
        int hi = n - 1;

        while (lo <= hi) {
                int m = (lo / 2) + (hi / 2) + (hi & lo & 1);
                if      (id < ids[m]) { hi = m - 1; i_ = m;   }
                else if (id > ids[m]) { lo = m + 1; i_ = lo;  }
                else                  { *i = m; return true; }
        }

        *i = i_;

        return false;
}

void
itable_init(Ty *ty, struct itable *t)
{
        v00(t->ids);
        v00(t->values);
        uvR(t->ids, 2);
        uvR(t->values, 2);
        t->class = -1;
}

Value *
itable_get(Ty *ty, struct itable *t, int64_t id)
{
        Value *m;
        int i;

        if (false && vN(t->ids) < 8) {
                m = xfind(t, id);
                if (m == NULL) {
                        if (vN(t->ids) == 7) {
                                xsort7(t);
                                goto Big;
                        } else {
                                uvP(t->ids, id);
                                m = vvP(t->values, NIL);
                        }
                }
        } else {
Big:
                if (bfind(t, id, &i)) {
                        m = v_(t->values, i);
                } else {
                        vvI(t->ids, id, i);
                        vvI(t->values, NIL, i);
                        m = v_(t->values, i);
                }
        }

        return m;
}

Value *
itable_add(Ty *ty, struct itable *t, int64_t id, Value v)
{
        Value *m;
        int i;

        if (false && vN(t->ids) < 8) {
                m = xfind(t, id);

                if (m == NULL) {
                        if (vN(t->ids) == 7) {
                                xsort7(t);
                                goto Big;
                        } else {
                                uvP(t->ids, id);
                                m = vvP(t->values, v);
                        }
                } else {
                        *m = v;
                }
        } else {
Big:
                if (bfind(t, id, &i)) {
                        m = v_(t->values, i);
                        *m = v;
                } else {
                        vvI(t->ids, id, i);
                        vvI(t->values, v, i);
                        m = v_(t->values, i);
                }
        }

        return m;
}

inline static void
bubble(struct itable *t, int64_t i, int64_t j)
{
        for (; j > i && v__(t->ids, j) < v__(t->ids, j - 1); --j) {
                SWAP(int, *v_(t->ids, j), *v_(t->ids, j - 1));
                SWAP(Value, *v_(t->values, j), *v_(t->values, j - 1));
        }
}

inline static void
xsort(struct itable *t, int64_t i, int64_t n)
{
        for (int64_t j = i + n - 1; j > i; --j) {
                bubble(t, i, j);
        }
}

inline static void
xmerge(struct itable * restrict t, int n0, int * restrict ids, Value * restrict vals)
{
        int i = 0;
        int j = n0;

        for (int n = 0; n < vN(t->ids); ++n) {
                if (i == n0) {
                        ids[n] = v__(t->ids, j);
                        vals[n] = v__(t->values, j);
                        j += 1;
                } else if (j == vN(t->ids)) {
                        ids[n] = v__(t->ids, i);
                        vals[n] = v__(t->values, i);
                        i += 1;
                } else if (v__(t->ids, i) < v__(t->ids, j)) {
                        ids[n] = v__(t->ids, i);
                        vals[n] = v__(t->values, i);
                        i += 1;
                } else {
                        ids[n] = v__(t->ids, j);
                        vals[n] = v__(t->values, j);
                        j += 1;
                }
        }
}

void
itable_copy_weak(Ty *ty, struct itable * restrict dst, struct itable const * restrict src)
{
        for (int i = 0; i < vN(src->ids); ++i) {
                Value *v = itable_get(ty, dst, v__(src->ids, i));
                if (v->type == VALUE_NIL) {
                        *v = v__(src->values, i);
                }
        }
}

void
itable_copy(Ty *ty, struct itable * restrict dst, struct itable const * restrict src)
{
        size_t n0 = vN(dst->ids);
        size_t n1 = vN(src->ids);

        vvPn(dst->ids, src->ids.items, n1);
        vvPn(dst->values, src->values.items, n1);

        vec(int) ids = {0};
        vec(Value) vals = {0};

        vec_reserve(ids, vN(dst->ids));
        vec_reserve(vals, vN(dst->values));
#if 0
        if (n0 < 8) {
                xsort(dst, 0, n0);
        }

        if (vN(src->ids) < 8) {
                xsort(dst, n0, n1);
        }
#endif
        xmerge(dst, n0, ids.items, vals.items);

        mF(dst->ids.items);
        mF(dst->values.items);

        dst->ids.items = ids.items;
        dst->values.items = vals.items;
}

Value *
itable_lookup(Ty *ty, struct itable const *t, int64_t id)
{
        if (false && vN(t->ids) < 8) {
                return xfind(t, id);
        } else {
                int i;
                if (bfind(t, id, &i)) {
                        return v_(t->values, i);
                }
        }

        return NULL;
}

void
itable_release(Ty *ty, struct itable *t)
{
        mF(t->ids.items);
        mF(t->values.items);
}

int
itable_get_completions(Ty *ty, struct itable const *t, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        for (int i = 0; n < max && i < vN(t->ids); ++i) {
                char const *name = M_NAME(v__(t->ids, i));
                if (strncmp(name, prefix, prefix_len) == 0) {
                        out[n++] = sclone_malloc(name);
                }
        }

        return n;
}

int
itable_completions(Ty *ty, struct itable const *t, char const *prefix, ValueVector *out)
{
        int n = 0;
        int prefix_len = (prefix == NULL) ? 0 : strlen(prefix);

        for (int i = 0; i < vN(t->ids); ++i) {
                char const *name = M_NAME(v__(t->ids, i));
                if (strncmp(name, prefix, prefix_len) == 0) {
                        xvP(*out, v__(t->values, i));
                }
        }

        return n;
}

void
itable_dump(Ty *ty, struct itable *t)
{
        int w = 0;
        for (int i = 0; i < vN(t->ids); ++i) {
                char const *name = M_NAME(v__(t->ids, i));
                w = max(w, strlen(name));
        }

        for (int i = 0; i < vN(t->ids); ++i) {
                char const *name = M_NAME(v__(t->ids, i));
                Value const *val = v_(t->values, i);
                printf("%-*s : %s\n", w, name, VSC(val));
        }
}

/* vim: set sts=8 sw=8 expandtab: */
