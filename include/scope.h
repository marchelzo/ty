#ifndef SCOPE_H_INCLUDED
#define SCOPE_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>

#include "vec.h"
#include "location.h"
#include "gc.h"
#include "ty.h"

enum {
        SYMBOL_TABLE_SIZE = 16
};

enum {
        SYM_PUBLIC       = 1 << 0,
        SYM_THREAD_LOCAL = 1 << 1,
        SYM_MACRO        = 1 << 2,
        SYM_FUN_MACRO    = 1 << 3,
        SYM_CONST        = 1 << 4,
        SYM_TYPE_VAR     = 1 << 5,
        SYM_VARIADIC     = 1 << 6,
        SYM_IMMORTAL     = 1 << 7,
        SYM_OMNIPRESENT  = 1 << 8,
};

typedef struct type Type;

typedef struct symbol {
        char const *identifier;
        char const *doc;
        int symbol;
        int tag;
        int class;
        u32 flags;
        bool captured;
        bool global;
        bool namespace;
        bool fixed;
        int i;
        int ci;

        Location loc;
        Module *mod;

        Type *type;
        Expr *expr;

        Scope *scope;

        uint64_t hash;
        Symbol *next;
} Symbol;

typedef struct scope {
        bool external;
        bool namespace;
        bool shared;
        bool active;
        bool is_function;

        Symbol *table[SYMBOL_TABLE_SIZE];

        vec(Symbol *) owned;
        vec(Symbol *) captured;
        vec(int) cap_indices;

        Scope *parent;
        Scope *function;

        RefinementVector refinements;

#if !defined(TY_RELEASE) || defined(TY_DEBUG_NAMES)
        char const *name;
#endif
} Scope;

typedef void *SymbolTransform(Ty *ty, Symbol *);

struct scope *
_scope_new(Ty *ty,
#if !defined(TY_RELEASE) || defined(TY_DEBUG_NAMES)
        char const *name,
#endif
        Scope *parent,
        bool function
);

#if !defined(TY_RELEASE) || defined(TY_DEBUG_NAMES)
  #define scope_new(ty, n, p, f) _scope_new(ty, n, p, f)
#else
  #define scope_new(ty, n, p, f) _scope_new(ty, p, f)
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
scope_xlookup(Ty *ty, Scope const *s, char const *id, i64 stop, i64 start);

Symbol *
scope_local_lookup(Ty *ty, Scope const *s, char const *id);

Symbol *
scope_local_xlookup(Ty *ty, Scope const *s, char const *id, i64 stop, i64 start);

Symbol *
scope_insert(Ty *ty, Scope *s, Symbol *sym);

Symbol *
scope_insert_as(Ty *ty, Scope *s, Symbol *sym, char const *id);

bool
scope_is_subscope(Scope const *sub, Scope const *scope);

char const *
scope_copy_public(Ty *ty, Scope *dst, Scope const *src, bool reexport);

char const *
scope_copy_public_except(Ty *ty, Scope *dst, Scope const *src, char const **skip, int n, bool reexport);

char const *
scope_copy(Ty *ty, Scope *dst, Scope const *src);

inline static void
scope_apply(Ty *ty, Scope *scope, SymbolTransform *f)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *s = scope->table[i]; s != NULL; s = s->next) {
                        f(ty, s);
                }
        }
}

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

inline static bool
SymbolIsTypeVar(Symbol const *var)
{
        return var->flags & SYM_TYPE_VAR;
}

inline static bool
SymbolIsImmortal(Symbol const *var)
{
        return var->flags & SYM_IMMORTAL;
}

inline static bool
SymbolIsOmnipresent(Symbol const *var)
{
        return var->flags & SYM_OMNIPRESENT;
}

inline static bool
SymbolIsThreadLocal(Symbol const *var)
{
        return var->flags & SYM_THREAD_LOCAL;
}

inline static bool
SymbolIsPublic(Symbol const *var)
{
        return var->flags & SYM_PUBLIC;
}

inline static bool
SymbolIsConst(Symbol const *var)
{
        return var->flags & SYM_CONST;
}

inline static bool
SymbolIsMacro(Symbol const *var)
{
        return var->flags & SYM_MACRO;
}

inline static bool
SymbolIsFunMacro(Symbol const *var)
{
        return var->flags & SYM_FUN_MACRO;
}

inline static bool
SymbolIsVariadic(Symbol const *var)
{
        return var->flags & SYM_VARIADIC;
}

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
ScopeIsTop(Ty *ty, Scope const *scope)
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

#if !defined(TY_RELEASE) || defined(TY_DEBUG_NAMES)
char const *
scope_name(Ty *ty, Scope const *s);
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
