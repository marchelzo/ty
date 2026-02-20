#ifndef SCOPE_H_INCLUDED
#define SCOPE_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>

#include "vec.h"
#include "gc.h"
#include "ty.h"

#if defined(TY_DEBUG_NAMES) || !defined(TY_RELEASE) || defined(TY_LS) || 1
 #define TY_NAMED_SCOPES 1
 char const *
 scope_name(Ty *ty, Scope const *s);
#else
 #define TY_NAMED_SCOPES 0
 #define scope_name(...) "<>"
#endif


#define TY_SCOPE_FLAGS                 \
        X(LOCAL_ONLY,  LocalOnly,  0)  \
        X(EXPLICIT,    Explicit,   1)  \
        X(PERMISSIVE,  Permissive, 2)  \
        X(LOCAL,       Local,      3)  \
        X(EXTERNAL,    External,   4)  \
        X(NAMESPACE,   Namespace,  5)  \
        X(ACTIVE,      Active,     6)  \
        X(FUNCTION,    Function,   7)  \
        X(RELOADING,   Reloading,  8)


#define X(f, _, i) SCOPE_##f = (1 << i),
enum { TY_SCOPE_FLAGS };
#undef X


#define TY_SYM_FLAGS                      \
        X(PUBLIC,       Public,       0)  \
        X(THREAD_LOCAL, ThreadLocal,  1)  \
        X(CLASS,        Class,        2)  \
        X(TAG,          Tag,          3)  \
        X(FUNCTION,     Function,     4)  \
        X(MACRO,        Macro,        5)  \
        X(FUN_MACRO,    FunMacro,     6)  \
        X(PATTERN,      Pattern,      7)  \
        X(PROPERTY,     Property,     8)  \
        X(CONST,        Const,        9)  \
        X(BUILTIN,      Builtin,     10)  \
        X(TYPE_VAR,     TypeVar,     11)  \
        X(VARIADIC,     Variadic,    12)  \
        X(IMMORTAL,     Immortal,    13)  \
        X(TRANSIENT,    Transient,   14)  \
        X(RECYCLED,     Recycled,    15)  \
        X(MEMBER,       Member,      16)  \
        X(STATIC,       Static,      17)  \
        X(GLOBAL,       Global,      18)  \
        X(CAPTURED,     Captured,    19)  \
        X(FIXED,        FixedType,   20)  \
        X(NAMESPACE,    Namespace,   21)  \
        X(PARAM_PACK,   ParamPack,   22)  \
        X(TYPE_ALIAS,   TypeAlias,   23)  \


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

        Scope *function;

        u32 size;
        u32 count;
        u32 flags;
        i32 eval;

        Scope *parent;

        Symbol **table;
} Scope;

Scope *
NewSubscope(
        Ty *ty,
#if TY_NAMED_SCOPES
        char const *name,
#endif
        Scope *parent,
        bool function
);

#if TY_NAMED_SCOPES
  #define scope_new(ty, n, p, f) NewSubscope(ty, n, p, f)
#else
  #define scope_new(ty, n, p, f) NewSubscope(ty, p, f)
#endif

Symbol *
scope_add(Ty *ty, Scope *s, char const *id);

Symbol *
scope_add_type_var(Ty *ty, Scope *s, char const *id, u32 flags);

Symbol *
scope_add_type_alias(Ty *ty, Scope *s, char const *id, Expr const *src);

Symbol *
scope_add_type(Ty *ty, Scope *s, char const *id);

Symbol *
scope_add_i(Ty *ty, Scope *s, char const *id, int i);

Symbol *
scope_add_namespace(Ty *ty, Scope *s, char const *id, Scope *ns);

Symbol *
scope_new_namespace(Ty *ty, char const *name, Scope *parent);

void
scope_capture(Ty *ty, Scope *scope, Symbol *sym);

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

void
scope_copy_weak(Ty *ty, Scope *dst, Scope const *src);

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

#define X(f, n, _)                                 \
        inline static bool                         \
        ScopeIs##n(Scope const *scope)             \
        {                                          \
                return (scope != NULL)             \
                    && (scope->flags & SCOPE_##f); \
        }
TY_SCOPE_FLAGS
#undef X

inline static Refinement *
ScopeFindRefinement(Scope *scope, Symbol *var)
{
        if (scope == NULL) {
                return NULL;
        }

        for (int i = 0; i < vN(scope->refinements); ++i) {
                Refinement *ref = v_(scope->refinements, i);
                if (ref->var == var) {
                        return ref;
                }
        }

        return NULL;
}

inline static Refinement *
ScopeRefineVar(Ty *ty, Scope *scope, Symbol *var, Type *t0)
{
        Refinement *ref = ScopeFindRefinement(scope, var);

        char *type_show(Ty *ty, Type const *t0);

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
                        ((Refinement) {
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
                if (ScopeIsFunction(scope)) {
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

inline static bool
IsPrivateMember(char const *name)
{
        usize n = strlen(name);
        return (n >= 2)
            && (name[0] == '_')
            && (
                        (name[n - 1] != '_')
                     || (name[n - 2] != '_')
               )
            ;
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

#endif

/* vim: set sts=8 sw=8 expandtab: */
