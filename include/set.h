#ifndef SET_H_INCLUDED
#define SET_H_INCLUDED

#include "ty.h"
#include "gc.h"

enum {
        SET_SUBSET     = -1,
        SET_EQUAL      =  0,
        SET_SUPERSET   =  1,
        SET_UNRELATED  =  2
};

inline static Set *
set_new(Ty *ty)
{
        return mAo0(sizeof (Set), GC_SET);
}

inline static Set *
set_xnew(Ty *ty)
{
        return uAo0(sizeof (Set), GC_SET);
}

bool
set_add(Ty *ty, Set *s, Value x);

void
set_add_all(Ty *ty, Set *s, Value xs);

bool
set_has(Ty *ty, Set const *s, Value const *x);

bool
set_has_hashed(Ty *ty, Set const *s, u64 h, Value const *x);

bool
set_remove(Ty *ty, Set *s, Value const *x);

Set *
SetClone(Ty *ty, Set const *s);

Set *
SetUnion(Ty *ty, Set const *s, Set const *t);

Set *
SetIntersect(Ty *ty, Set const *s, Set const *t);

Set *
SetSubtract(Ty *ty, Set const *s, Set const *t);

Set *
SetSymDiff(Ty *ty, Set const *s, Set const *t);

Set *
SetAbsorb(Ty *ty, Set *s, Set const *t);

Set *
SetRetain(Ty *ty, Set *s, Set const *t);

Set *
SetDiscard(Ty *ty, Set *s, Set const *t);

Set *
SetToggle(Ty *ty, Set *s, Set const *t);

bool
set_equal(Ty *ty, Set const *s, Set const *t);

bool
set_equal_x(Ty *ty, Set const *s, Set const *t, ValueEqFn *eq, void *ctx);

int
set_order(Ty *ty, Set const *s, Set const *t);

u64
set_hash(Set const *s);

void
set_mark(Ty *ty, Set *s);

void
set_free(Ty *ty, Set *s);

Value
builtin_set(Ty *ty, int argc, Value *kwargs);

void
build_set_method_table(void);

BuiltinMethod *
get_set_method(char const *);

BuiltinMethod *
get_set_method_i(int);

int
set_get_completions(Ty *ty, char const *prefix, char **out, int max);

#endif
