#include <stdint.h>
#include <string.h>

#include "scope.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "types.h"

static int SYMBOL;

#ifndef TY_RELEASE
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

        for (int i = stack.count - 1; i >= 0; --i) {
                s = stack.items[i];
                int n = strlen(s->name) + (i != 0);
                if (n > remaining)
                        break;
                strcat(b, s->name);
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
local_lookup(Scope const *s, char const *id)
{
        uint64_t h = strhash(id);
        int i = h % SYMBOL_TABLE_SIZE;

        for (Symbol *sym = s->table[i]; sym != NULL; sym = sym->next)
                if (sym->hash == h && strcmp(sym->identifier, id) == 0)
                        return sym;

        return NULL;
}

Symbol *
scope_find_symbol(Scope const *s, Symbol const *needle)
{
        if (s == NULL) {
                return NULL;
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *sym = s->table[i]; sym != NULL; sym = sym->next) {
                        if (sym->symbol == needle->symbol) {
                                return sym;
                        }
                }
        }

        return scope_find_symbol(s->parent, needle);
}

Symbol *
scope_new_namespace(Ty *ty, char const *name, Scope *parent)
{
        Scope *s = amA0(sizeof *s);

        s->parent = parent;
        s->function = parent->function;
        s->namespace = true;

#ifndef TY_RELEASE
        s->name = name;
#endif

        return scope_add_namespace(ty, parent, name, s);
}

Scope *
_scope_new(Ty *ty,
#ifndef TY_RELEASE
        char const *name,
#endif
        Scope *parent,
        bool is_function
)
{
        Scope *s = amA0(sizeof *s);

        s->parent = parent;
        s->function = (is_function || parent == NULL) ? s : parent->function;

#ifndef TY_RELEASE
        s->name = name;
#endif

        return s;
}

int
scope_capture(Ty *ty, Scope *s, Symbol *sym, int parent_index)
{
                for (int i = 0; i < s->captured.count; ++i) {
                        if (s->captured.items[i] == sym) {
                                return i;
                        }
                }

                sym->captured = true;

                avP(s->captured, sym);
                avP(s->cap_indices, parent_index);

                LOG(
                        "scope_capture(ty, sym=%s, scope=%s (%p), cap_index=%d)",
                        sym->identifier,
                        scope_name(ty, s),
                        s,
                        parent_index
                );

                return s->captured.count - 1;
}

Symbol *
scope_lookup(Ty *ty, Scope const *s, char const *id)
{
        if (s == NULL) {
                return NULL;
        }

        Symbol *sym = local_lookup(s, id);

        if (sym != NULL) {
                return sym;
        }

        sym = scope_lookup(ty, s->parent, id);

        if (sym == NULL) {
                return NULL;
        }

        if (
                sym->scope->function != s->function
             && !sym->global
             && !sym->namespace
        ) {
                vec(Scope *) scopes = {0};

                Scope *scope = s->function;

                while (scope->parent->function != sym->scope->function) {
                        avP(scopes, scope);
                        scope = scope->parent->function;
                }

                int parent_index = scope_capture(ty, scope, sym, -1);

                for (int i = scopes.count - 1; i >= 0; --i) {
                        parent_index = scope_capture(ty, scopes.items[i], sym, parent_index);
                }
        }

        return sym;
}

bool
scope_locally_defined(Ty *ty, Scope const *s, char const *id)
{
        return local_lookup(s, id) != NULL;
}

Symbol *
scope_local_lookup(Ty *ty, Scope const *s, char const *id)
{
        return local_lookup(s, id);
}

static Symbol *
xadd(Ty *ty, Scope *s, char const *id)
{
        uint64_t h = strhash(id);
        int i = h % SYMBOL_TABLE_SIZE;

        Symbol *sym = amA(sizeof *sym);

        initsym(sym);
        sym->symbol = SYMBOL++;
        sym->identifier = id;
        sym->hash = h;
        sym->next = s->table[i];
        s->table[i] = sym;

        return sym;
}

Symbol *
scope_add_namespace(Ty *ty, Scope *s, char const *id, Scope *ns)
{
        Symbol *sym = xadd(ty, s, id);

        sym->namespace = true;
        sym->scope = ns;

        return sym;
}

Symbol *
scope_add_type_var(Ty *ty, Scope *s, char const *id)
{
        Symbol *sym = xadd(ty, s, id);

        sym->scope = s;
        sym->type_var = true;
        sym->type = type_variable(ty, sym);

        return sym;
}

Symbol *
scope_add_i(Ty *ty, Scope *s, char const *id, int idx)
{
        uint64_t h = strhash(id);
        int i = h % SYMBOL_TABLE_SIZE;

        Symbol *sym = amA(sizeof *sym);

        initsym(sym);
        sym->identifier = id;
        sym->symbol = SYMBOL++;
        sym->scope = s;

                      // s->function == global, or
        sym->global = s->function->parent == NULL ||
                      // s->function == state.global
                      (s->function->parent->parent == NULL && s->function != s);

        sym->hash = h;
        sym->next = s->table[i];

        sym->file = NULL;

        Scope *owner = s;
        while (owner->function != owner && owner->parent != NULL) {
                owner = owner->parent;
        }

        while (owner->owned.count <= idx) {
                avP(owner->owned, NULL);
        }

        LOG("Symbol %d (%s) is getting i = %d in scope %p", sym->symbol, id, sym->i, s);

        while (idx < owner->owned.count && owner->owned.items[idx] != NULL) {
                idx += 1;
        }

        if (idx == owner->owned.count) {
                avP(owner->owned, sym);
        } else {
                owner->owned.items[idx] = sym;
        }

        sym->i = idx;

        s->table[i] = sym;

        return sym;
}

Symbol *
scope_add(Ty *ty, Scope *s, char const *id)
{
        return scope_add_i(ty, s, id, 0);
}

Symbol *
scope_insert_as(Ty *ty, Scope *s, Symbol *sym, char const *id)
{
        Symbol *new = amA(sizeof *new);

        *new = *sym;
        new->identifier = id;
        new->hash = strhash(id);
        new->scope = s;
        new->public = false;

        int i = new->hash % SYMBOL_TABLE_SIZE;
        new->next = s->table[i];
        s->table[i] = new;

        return new;
}

Symbol *
scope_insert(Ty *ty, Scope *s, Symbol *sym)
{
        Symbol *new = amA(sizeof *new);
        *new = *sym;

        if (!sym->namespace) {
                new->scope = s;
                new->public = false;
        }

        int i = sym->hash % SYMBOL_TABLE_SIZE;
        new->next = s->table[i];
        s->table[i] = new;

        return new;
}

char const *
scope_copy(Ty *ty, Scope *dst, Scope const *src)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        Symbol *conflict = scope_lookup(ty, dst, s->identifier);
                        if (conflict != NULL && conflict->scope != src && conflict->public)
                                return conflict->identifier;
                }
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
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
scope_copy_public_except(Ty *ty, Scope *dst, Scope const *src, char const **skip, int n, bool reexport)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (should_skip(s->identifier, skip, n)) {
                                continue;
                        }
                        Symbol *conflict = scope_lookup(ty, dst, s->identifier);
                        if (conflict != NULL && conflict->scope != src && conflict->public) {
                                return conflict->identifier;
                        }
                }
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (should_skip(s->identifier, skip, n)) {
                                continue;
                        }
                        if (s->public) {
                                scope_insert(ty, dst, s)->public |= reexport;
                        }
                }
        }

        return NULL;
}

char const *
scope_copy_public(Ty *ty, Scope *dst, Scope const *src, bool reexport)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        Symbol *conflict = scope_lookup(ty, dst, s->identifier);
                        if (conflict != NULL && conflict->scope != src && conflict->public) {
                                return conflict->identifier;
                        }
                }
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (s->public) {
                                scope_insert(ty, dst, s)->public |= reexport;
                        }
                }
        }

        return NULL;
}

bool
scope_is_subscope(Ty *ty, Scope const *sub, Scope const *scope)
{
        while (sub != NULL) {
                if (sub->parent == scope)
                        return true;
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
                for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                        for (Symbol *sym = s->table[i]; sym != NULL; sym = sym->next) {
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

                                for (int i = scopes.count - 1; i >= 0; --i) {
                                        parent_index = scope_capture(ty, scopes.items[i], sym, parent_index);
                                }

                                LOG("scope_capture_all: done capturing %s", sym->identifier);
                        }
                }
        }
}

int
scope_get_symbol(Ty *ty)
{
        return SYMBOL;
}

void
scope_set_symbol(Ty *ty, int s)
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

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                        if (n < max && sym->public && strncmp(sym->identifier, prefix, prefix_len) == 0) {
                                out[n++] = sclone_malloc(sym->identifier);
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

/* vim: set sts=8 sw=8 expandtab: */
