#ifndef SCOPE_H_INCLUDED
#define SCOPE_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>

#include "vec.h"
#include "location.h"
#include "gc.h"
#include "ty.h"

#if defined(TY_DEBUG_NAMES) || !defined(TY_RELEASE) || defined(TY_LS)
 #define TY_NAMED_SCOPES 1
#else
 #define TY_NAMED_SCOPES 0
#endif

#define TY_SCOPE_FLAGS                 \
        X(LOCAL_ONLY,  LocalOnly,  0)  \
        X(EXPLICIT,    Explicit,   1)  \
        X(PERMISSIVE,  Permissive, 2)  \
        X(LOCAL,       Local,      3)


#define X(f, _, i) SCOPE_##f = (1 << i),
enum { TY_SCOPE_FLAGS };
#undef X


#define TY_SYM_FLAGS                      \
        X(PUBLIC,       Public,       0)  \
        X(THREAD_LOCAL, ThreadLocal,  1)  \
        X(MACRO,        Macro,        2)  \
        X(FUN_MACRO,    FunMacro,     3)  \
        X(PROPERTY,     Property,     4)  \
        X(CONST,        Const,        5)  \
        X(BUILTIN,      Builtin,      6)  \
        X(TYPE_VAR,     TypeVar,      7)  \
        X(VARIADIC,     Variadic,     8)  \
        X(IMMORTAL,     Immortal,     9)  \
        X(TRANSIENT,    Transient,   10)  \
        X(RECYCLED,     Recycled,    11)  \
        X(CLASS_MEMBER, Member,      12)  \
        X(GLOBAL,       Global,      13)  \
        X(CAPTURED,     Captured,    14)  \
        X(FIXED,        FixedType,   15)  \
        X(NAMESPACE,    Namespace,   16)


#define X(f, _, i) SYM_##f = (1 << i),
enum { TY_SYM_FLAGS };
#undef X


typedef struct type Type;

typedef struct symbol {
        char const *identifier;
        char const *doc;

        u32 flags;

        i32 symbol;
        i32 tag;
        i32 class;
        i32 member;

        i32 i;
        i32 ci;

        Location loc;
        Module *mod;

        Type *type;
        Expr *expr;
        Scope *scope;

        u64 hash;
        Symbol *next;
} Symbol;

typedef struct scope {
#if TY_NAMED_SCOPES
        char const *name;
#endif
        symbol_vector owned;
        symbol_vector captured;
        int_vector cap_indices;

        RefinementVector refinements;

        bool external;
        bool namespace;
        bool shared;
        bool active;
        bool is_function;
        bool reloading;

        Scope *function;

        u32 size;
        u32 mask;

        Scope *parent;

        Symbol *table[];
} Scope;

Scope *
NewSubscope(
        Ty *ty,
#if TY_NAMED_SCOPES
        char const *name,
#endif
        u32 size,
        Scope *parent,
        bool function
);

#if TY_NAMED_SCOPES
  #define scope_new(ty, n, p, f) NewSubscope(ty, n, 0, p, f)
#else
  #define scope_new(ty, n, p, f) NewSubscope(ty, 0, p, f)
#endif

Symbol *
scope_add(Ty *ty, Scope *s, char const *id);

Symbol *
scope_add_type_var(Ty *ty, Scope *s, char const *id);

Symbol *
scope_add_type(Ty *ty, Scope *s, char const *id);

Symbol *
scope_add_i(Ty *ty, Scope *s, char const *id, int i);

Symbol *
scope_add_namespace(Ty *ty, Scope *s, char const *id, Scope *ns);

Symbol *
scope_new_namespace(Ty *ty, char const *name, Scope *parent);

int
scope_capture(Ty *ty, Scope *s, Symbol *sym, int parent_index);

bool
scope_locally_defined(Ty *ty, Scope const *s, char const *id);

Symbol *
scope_find_symbol(Scope const *s, Symbol const *needle);

Symbol *
scope_lookup(Ty *ty, Scope const *s, char const *id);

Symbol *
scope_xlookup(
        Ty *ty,
        Scope const *s,
        char const *id,
        u32 flags
);

Symbol *
scope_local_lookup(
        Ty *ty,
        Scope const *s,
        char const *id
);

Symbol *
scope_local_xlookup(
        Ty *ty,
        Scope const *s,
        char const *id,
        u32 flags
);

Symbol *
scope_insert(Ty *ty, Scope *s, Symbol *sym);

Symbol *
scope_insert_as(Ty *ty, Scope *s, Symbol *sym, char const *id);

bool
scope_is_subscope(Scope const *sub, Scope const *scope);

char const *
scope_copy_public(
        Ty *ty,
        Scope *dst,
        Scope const *src,
        bool reexport
);

char const *
scope_copy_public_except(
        Ty *ty,
        Scope *dst,
        Scope const *src,
        char const **skip,
        int n,
        bool reexport
);

char const *
scope_copy(Ty *ty, Scope *dst, Scope const *src);

i64
scope_get_symbol(Ty *ty);

void
scope_set_symbol(Ty *ty, i64 s);

void
scope_capture_all(Ty *ty, Scope *scope, Scope const *stop);

Symbol *
NewSymbol(Ty *ty, char const *name);

Symbol *
NewTypeVar(Ty *ty, char const *name);

Symbol *
NewScopedTypeVar(Ty *ty, Scope *s, char const *name);


#define X(f, n, _)                              \
        inline static bool                      \
        SymbolIs##n(Symbol const *var)          \
        {                                       \
                return (var != NULL)            \
                    && (var->flags & SYM_##f);  \
        }
TY_SYM_FLAGS
#undef X

inline static bool
ScopeIsShared(Scope const *scope)
{
        while (scope != NULL) {
                if (scope->shared) {
                        return true;
                }
                scope = scope->parent;
        }

        return false;
}

inline static Refinement *
ScopeFindRefinement(Scope *scope, Symbol *var)
{
        for (int i = 0; i < vN(scope->refinements); ++i) {
                if (v_(scope->refinements, i)->var == var) {
                        return v_(scope->refinements, i);
                }
        }

        return NULL;
}

inline static Refinement *
ScopeRefineVar(Ty *ty, Scope *scope, Symbol *var, Type *t0)
{
        Refinement *ref = ScopeFindRefinement(scope, var);

        if (ref != NULL) {
                Type *type_both(Ty *, Type *, Type *);
                if (ref->mut) {
                        ref->t0 = t0;
                } else {
                        ref->t0 = type_both(ty, ref->t0, t0);
                }
        } else {
                avP(
                        scope->refinements,
                        ((Refinement){
                                .var = var,
                                .t0 = t0,
                                .active = false
                        })
                );
                ref = vvL(scope->refinements);
        }

        return ref;
}

inline static bool
ScopeIsTop(Scope const *scope)
{
        while (scope != NULL) {
                if (scope->is_function) {
                        return false;
                }
                scope = scope->parent;
        }

        return true;
}


inline static bool
ScopeIsContainedBy(Scope const *sub, Scope const *scope)
{
        return (sub == scope) || scope_is_subscope(sub, scope);
}

int
scope_get_completions(
        Ty *ty,
        Scope *scope,
        char const *prefix,
        char **out,
        int max,
        bool recursive
);

i32
ScopeCompletions(
        Ty *ty,
        Scope *scope,
        char const *prefix,
        symbol_vector *out,
        i32Vector *depths,
        i32 max,
        bool recursive
);

void
ScopeReset(Scope *scope);

Symbol *
ScopeFindRecycled(Scope const *scope, char const *id);

#if TY_NAMED_SCOPES
char const *
scope_name(Ty *ty, Scope const *s);
#else
#define scope_name(...) "<>"
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
