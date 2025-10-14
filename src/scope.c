#include <stdint.h>
#include <string.h>

#include "compiler.h"
#include "scope.h"
#include "alloc.h"
#include "log.h"
#include "ty.h"
#include "util.h"
#include "types.h"

static i64 SYMBOL;

#if TY_NAMED_SCOPES
char const *
scope_name(Ty *ty, Scope const *s)
{
        _Thread_local static char b[4096];

        vec(Scope *) stack = {0};

        while (s != NULL) {
                vec_nogc_push(stack, s);
                s = s->parent;
        }

        b[0] = '\0';

        int remaining = sizeof b - 1;

        for (int i = vN(stack) - 1; i >= 0; --i) {
                s = v__(stack, i);
                int n = strlen(s->name) + (i != 0);
                if (n + 3 > remaining)
                        break;
                if (s->function == s) { strcat(b, "#"); }
                strcat(b, s->name);
                if (s->function == s) { strcat(b, "#"); }
                strcat(b, "." + (i == 0));
                remaining -= n;
        }

        return sclone(ty, b);
}
#endif

inline static void
initsym(Symbol *s)
{
        memset(s, 0, sizeof *s);
        s->tag   = -1;
        s->class = -1;
        s->ci    = -1;
}

inline static Symbol *
local_xlookup(Scope const *scope, char const *id, u32 flags)
{
        u64 h = strhash(id);
        u32 i = h & scope->mask;

        bool    member_ok = !(flags & SCOPE_EXPLICIT);
        bool transient_ok =  (flags & SCOPE_PERMISSIVE);

        for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                if (
                        (sym->hash == h)
                     && (member_ok    || !SymbolIsMember(sym))
                     && (transient_ok || !SymbolIsTransient(sym))
                     && (strcmp(sym->identifier, id) == 0)
                     && !SymbolIsRecycled(sym)
                ) {
                                return sym;
                }
        }

        return NULL;
}

inline static Symbol *
local_lookup(Scope const *scope, char const *id)
{
        return local_xlookup(scope, id, SCOPE_LOCAL);
}

Symbol *
scope_find_symbol(Scope const *scope, Symbol const *needle)
{
        if (scope == NULL) {
                return NULL;
        }

        for (int i = 0; i < scope->size; ++i) {
                for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                        if (sym->symbol == needle->symbol) {
                                return sym;
                        }
                }
        }

        return scope_find_symbol(scope->parent, needle);
}

Symbol *
scope_new_namespace(Ty *ty, char const *name, Scope *parent)
{
        Scope *ns = NewSubscope(
                ty,
#if TY_NAMED_SCOPES
                name,
#endif
                0,
                parent,
                false
        );

        ns->namespace = true;

        return scope_add_namespace(ty, parent, name, ns);
}

Scope *
NewSubscope(
        Ty *ty,
#if TY_NAMED_SCOPES
        char const *name,
#endif
        u32 size,
        Scope *parent,
        bool is_function
)
{
        if (size == 0) {
                size = (parent != NULL)
                     ? zmaxu(8, parent->size >> 2)
                     : 256;
        }

        Scope *scope = amA0(sizeof (Scope) + (size * sizeof (Symbol *)));

        scope->parent = parent;
        scope->is_function = is_function;
        scope->function = (is_function || parent == NULL)
                        ? scope
                        : parent->function;

        scope->size = size;
        scope->mask = (size - 1);

#if TY_NAMED_SCOPES
        scope->name = name;
#endif

        return scope;
}

inline static bool
ScopeCapturesVar(Scope const *scope, Symbol const *var)
{
        for (int i = 0; i < vN(scope->captured); ++i) {
                if (v__(scope->captured, i) == var) {
                        return true;
                }
        }

        return false;
}

int
scope_capture(Ty *ty, Scope *s, Symbol *sym, int parent_index)
{
                for (int i = 0; i < vN(s->captured); ++i) {
                        if (v__(s->captured, i) == sym) {
                                return i;
                        }
                }

                sym->flags |= SYM_CAPTURED;

                avP(s->captured, sym);
                avP(s->cap_indices, parent_index);

                LOG(
                        "scope_capture(ty, sym=%s, scope=%s (%p), cap_index=%d)",
                        sym->identifier,
                        scope_name(ty, s),
                        s,
                        parent_index
                );

                return vN(s->captured) - 1;
}

inline static Symbol *
lookup(
        Ty *ty,
        Scope const *s,
        char const *id,
        u32 flags
)
{
        if (s == NULL) {
                return NULL;
        }

        Symbol *sym = local_xlookup(s, id, flags);

        if (
                (sym != NULL)
             || (flags & SCOPE_LOCAL_ONLY)
        ) {
                return sym;
        }

        sym = lookup(ty, s->parent, id, flags & ~SCOPE_LOCAL);

        if (sym == NULL) {
                return NULL;
        }

        u32 const dont_capture = SYM_GLOBAL
                               | SYM_NAMESPACE
                               | SYM_CLASS_MEMBER
                               | SYM_TYPE_VAR
                               | SYM_THREAD_LOCAL;

        if (
                (sym->scope->function != s->function)
             && !(sym->flags & dont_capture)
        ) {
                if (
                        (EVAL_DEPTH > 0)
                     && !ScopeCapturesVar(s->function, sym)
                     && !SymbolIsImmortal(sym)
                ) {
                        CompileError(
                                ty,
                                "attempted runtime access of non-captured variable `%s%s%s`",
                                TERM(93;1),
                                sym->identifier,
                                TERM(0)
                        );
                }

                SCRATCH_SAVE();

                Scope *scope = s->function;
                vec(Scope *) scopes = {0};

                while (scope->parent->function != sym->scope->function) {
                        svP(scopes, scope);
                        scope = scope->parent->function;
                }

                int parent_index = scope_capture(ty, scope, sym, -1);

                for (int i = vN(scopes) - 1; i >= 0; --i) {
                        parent_index = scope_capture(ty, v__(scopes, i), sym, parent_index);
                }

                SCRATCH_RESTORE();
        }

        return sym;
}

Symbol *
scope_xlookup(
        Ty *ty,
        Scope const *scope,
        char const *id,
        u32 flags
)
{
        return lookup(ty, scope, id, flags | SCOPE_LOCAL);
}

Symbol *
scope_lookup(Ty *ty, Scope const *s, char const *id)
{
        return scope_xlookup(ty, s, id, 0);
}

bool
scope_locally_defined(Ty *ty, Scope const *s, char const *id)
{
        return local_lookup(s, id) != NULL;
}

Symbol *
scope_local_xlookup(
        Ty *ty,
        Scope const *s,
        char const *id,
        u32 flags
)
{
        return local_xlookup(s, id, flags);
}

Symbol *
scope_local_lookup(Ty *ty, Scope const *s, char const *id)
{
        return local_lookup(s, id);
}

static Symbol *
xnew(Ty *ty, char const *id)
{
        u64 h = strhash(id);
        Symbol *sym = amA(sizeof *sym);

        initsym(sym);
        sym->symbol = SYMBOL++;
        sym->identifier = id;
        sym->hash = h;
        sym->mod = CompilerCurrentModule(ty);

        return sym;
}

Symbol *
ScopeFindRecycled(Scope const *scope, char const *id)
{
        u64 h = strhash(id);
        u32 i = h & scope->mask;

        Symbol *old = NULL;

        for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                if (
                        SymbolIsRecycled(sym)
                     && (sym->hash == h)
                     && (strcmp(sym->identifier, id) == 0)
                ) {
                        old = sym;
                }
        }

        return old;
}

static Symbol *
xadd(Ty *ty, Scope *scope, char const *id)
{
        if (scope->reloading) {
                Symbol *old = ScopeFindRecycled(scope, id);
                if (old != NULL) {
                        old->flags = SYM_GLOBAL;
                        old->type  = NULL;
                        old->expr  = NULL;
                        old->class = -1;
                        old->tag   = -1;
                        return old;
                }
        }

        Symbol *sym = xnew(ty, id);
        u32 i = sym->hash & scope->mask;

        sym->scope = scope;

        sym->next = scope->table[i];
        scope->table[i] = sym;

        return sym;
}

Symbol *
NewSymbol(Ty *ty, char const *name)
{
        return xnew(ty, name);
}

Symbol *
NewTypeVar(Ty *ty, char const *name)
{
        Symbol *sym = xnew(ty, name);

        sym->flags |= SYM_TYPE_VAR;
        sym->type = type_variable(ty, sym);

        return sym;
}

Symbol *
NewScopedTypeVar(Ty *ty, Scope *s, char const *name)
{
        Symbol *sym = xadd(ty, s, name);

        sym->flags |= SYM_TYPE_VAR;
        sym->type = type_variable(ty, sym);

        return sym;
}

Symbol *
scope_add_namespace(Ty *ty, Scope *s, char const *id, Scope *ns)
{
        Symbol *sym = xadd(ty, s, id);

        sym->flags |= SYM_NAMESPACE;
        sym->scope = ns;

        return sym;
}

Symbol *
scope_add_type(Ty *ty, Scope *s, char const *id)
{
        Symbol *sym = xadd(ty, s, id);

        sym->scope = s;
        sym->flags |= SYM_TYPE_VAR;

        return sym;
}

Symbol *
scope_add_type_var(Ty *ty, Scope *s, char const *id)
{
        Symbol *sym = xadd(ty, s, id);

        sym->scope = s;
        sym->flags |= SYM_TYPE_VAR;
        sym->type = type_variable(ty, sym);

        return sym;
}

Symbol *
scope_add_i(Ty *ty, Scope *scope, char const *id, int idx)
{
        Symbol *sym = xadd(ty, scope, id);

        if (
                (scope->function->parent == NULL)
            || (scope->function->parent->parent == NULL && scope->function != scope)
        ) {
                sym->flags |= SYM_GLOBAL;
        }

        Scope *owner = scope;
        while (owner->function != owner && owner->parent != NULL) {
                owner = owner->parent;
        }

        while (vN(owner->owned) <= idx) {
                avP(owner->owned, NULL);
        }

        while (idx < vN(owner->owned) && v__(owner->owned, idx) != NULL) {
                idx += 1;
        }

        if (idx == vN(owner->owned)) {
                avP(owner->owned, sym);
        } else {
                v__(owner->owned, idx) = sym;
        }

        sym->i = idx;

        return sym;
}

Symbol *
scope_add(Ty *ty, Scope *s, char const *id)
{
        return scope_add_i(ty, s, id, 0);
}

Symbol *
scope_insert_as(Ty *ty, Scope *scope, Symbol *sym, char const *id)
{
        Symbol *new = amA(sizeof *new);

        *new = *sym;
        new->identifier = id;
        new->hash = strhash(id);
        new->scope = scope;
        new->flags &= ~SYM_PUBLIC;

        u32 i = new->hash & scope->mask;
        new->next = scope->table[i];
        scope->table[i] = new;

        return new;
}

Symbol *
scope_insert(Ty *ty, Scope *scope, Symbol *sym)
{
        Symbol *new = amA(sizeof *new);
        *new = *sym;

        if (!SymbolIsNamespace(sym)) {
                new->scope = scope;
                new->flags &= ~SYM_PUBLIC;
        }

        u32 i = sym->hash & scope->mask;
        new->next = scope->table[i];
        scope->table[i] = new;

        return new;
}

char const *
scope_copy(Ty *ty, Scope *dst, Scope const *src)
{
        for (int i = 0; i < src->size; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        Symbol *conflict = scope_lookup(ty, dst, s->identifier);
                        if (
                                (conflict != NULL)
                             && (conflict->scope != src)
                             && SymbolIsPublic(conflict)
                        ) {
                                return conflict->identifier;
                        }
                }
        }

        for (int i = 0; i < src->size; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        scope_insert(ty, dst, s);
                }
        }

        return NULL;
}

inline static bool
should_skip(char const *id, char const **skip, int n)
{
        for (int i = 0; i < n; ++i) {
                if (strcmp(id, skip[i]) == 0) {
                        return true;
                }
        }

        return false;
}

char const *
scope_copy_public_except(
        Ty *ty,
        Scope *dst,
        Scope const *src,
        char const **skip,
        int n,
        bool reexport
)
{
        for (int i = 0; i < src->size; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (should_skip(s->identifier, skip, n)) {
                                continue;
                        }
                        Symbol *conflict = scope_lookup(ty, dst, s->identifier);
                        if (
                                conflict != NULL
                             && conflict->scope != src
                             && SymbolIsPublic(conflict)
                        ) {
                                return conflict->identifier;
                        }
                }
        }

        for (int i = 0; i < src->size; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (should_skip(s->identifier, skip, n)) {
                                continue;
                        }
                        if (SymbolIsPublic(s)) {
                                scope_insert(ty, dst, s)->flags |= SYM_PUBLIC * reexport;
                        }
                }
        }

        return NULL;
}

char const *
scope_copy_public(Ty *ty, Scope *dst, Scope const *src, bool reexport)
{
        for (int i = 0; i < src->size; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        Symbol *conflict = scope_lookup(ty, dst, s->identifier);
                        if (
                                conflict != NULL
                             && conflict->scope != src
                             && SymbolIsPublic(conflict)
                        ) {
                                return conflict->identifier;
                        }
                }
        }

        for (int i = 0; i < src->size; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (SymbolIsPublic(s)) {
                                scope_insert(ty, dst, s)->flags |= SYM_PUBLIC * reexport;
                        }
                }
        }

        return NULL;
}

bool
scope_is_subscope(Scope const *sub, Scope const *scope)
{
        while (sub != NULL) {
                if (sub->parent == scope) {
                        return true;
                }
                sub = sub->parent;
        }

        return false;
}

void
scope_capture_all(Ty *ty, Scope *scope, Scope const *stop)
{
        if (scope->function->parent == NULL)
                return;

        for (Scope *s = scope; s->function != stop->function; s = s->parent) {
                for (int i = 0; i < s->size; ++i) {
                        for (Symbol *sym = s->table[i]; sym != NULL; sym = sym->next) {
                                sym->flags |= SYM_IMMORTAL;
                                LOG(
                                        "scope_capture_all(ty, scope=%s (%p)): capturing %s",
                                        scope_name(ty, scope),
                                        scope,
                                        sym->identifier
                                );

                                Scope *fscope = scope->function;
                                vec(Scope *) scopes = {0};

                                while (
                                                          fscope != stop->function
                                     && fscope->parent->function != stop->function
                                     &&         fscope->function != sym->scope->function
                                     && fscope->parent->function != sym->scope->function
                                ) {
                                        avP(scopes, fscope);
                                        fscope = fscope->parent->function;
                                }

                                int parent_index = scope_capture(ty, fscope, sym, -1);

                                for (int i = vN(scopes) - 1; i >= 0; --i) {
                                        parent_index = scope_capture(ty, v__(scopes, i), sym, parent_index);
                                }

                                LOG("scope_capture_all: done capturing %s", sym->identifier);
                        }
                }
        }
}

i64
scope_get_symbol(Ty *ty)
{
        return SYMBOL;
}

void
scope_set_symbol(Ty *ty, i64 s)
{
        SYMBOL = s;
}

int
scope_get_completions(
        Ty *ty,
        Scope *scope,
        char const *prefix,
        char **out,
        int max,
        bool recursive
)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        if (scope == NULL || max == 0) return 0;

        for (int i = 0; i < scope->size; ++i) {
                for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                        if (
                                n < max
                             && SymbolIsPublic(sym)
                             && strncmp(sym->identifier, prefix, prefix_len) == 0
                        ) {
                                out[n++] = S2(sym->identifier);
                        }
                }
        }

        if (recursive) n += scope_get_completions(
                ty,
                scope->parent,
                prefix,
                out + n,
                max - n,
                true
        );

        return n;
}

i32
ScopeCompletionsGo(
        Ty *ty,
        Scope *scope,
        char const *prefix,
        symbol_vector *out,
        i32Vector *depths,
        i32 max,
        bool recursive,
        i32 depth
)
{
        i32 n = 0;
        u32 prefix_len = strlen(prefix);

        if (scope == NULL || max == 0) return 0;

        for (int i = 0; i < scope->size; ++i) {
                for (Symbol *sym = scope->table[i]; sym != NULL && n < (u32)max; sym = sym->next) {
                        if (
                                SymbolIsPublic(sym)
                             && strncmp(sym->identifier, prefix, prefix_len) == 0
                        ) {
                                xvP(*out, sym);
                                xvP(*depths, depth);
                                n += 1;
                        }
                }
        }

        if (recursive) n += ScopeCompletionsGo(
                ty,
                scope->parent,
                prefix,
                out,
                depths,
                (max == -1) ? -1 : (max - n),
                true,
                depth + 1
        );

        return n;
}

i32
ScopeCompletions(
        Ty *ty,
        Scope *scope,
        char const *prefix,
        symbol_vector *out,
        i32Vector *depths,
        i32 max,
        bool recursive
)
{
        return ScopeCompletionsGo(ty, scope, prefix, out, depths, max, recursive, 0);
}

void
ScopeReset(Scope *scope)
{
        scope->active = false;
        v0(scope->refinements);

        for (i32 i = 0; i < scope->size; ++i) {
                Symbol *last = NULL;
                for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                        if (sym->mod->scope != scope) {
                                if (last == NULL) {
                                        scope->table[i] = sym->next;
                                } else {
                                        last->next = sym->next;
                                }
                        } else {
                                sym->flags |= SYM_RECYCLED;
                                last = sym;
                        }
                }
        }
}

/* vim: set sw=8 sts=8 expandtab: */
