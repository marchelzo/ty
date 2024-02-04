#include <stdint.h>
#include <string.h>

#include "scope.h"
#include "alloc.h"
#include "log.h"
#include "util.h"

static int GLOBAL;
static int SYMBOL;

#ifndef TY_RELEASE
char const *
scope_name(struct scope const *s)
{
        _Thread_local static char b[4096];

        vec(struct scope *) stack = {0};

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

        return b;
}
#endif

inline static struct symbol *
local_lookup(struct scope const *s, char const *id)
{
        uint64_t h = strhash(id);
        int i = h % SYMBOL_TABLE_SIZE;

        for (struct symbol *sym = s->table[i]; sym != NULL; sym = sym->next)
                if (sym->hash == h && strcmp(sym->identifier, id) == 0)
                        return sym;

        return NULL;
}

struct scope *
_scope_new(
#ifndef TY_RELEASE
        char const *name,
#endif
        struct scope *parent,
        bool is_function
)
{
        struct scope *s = Allocate(sizeof *s);

        s->parent = parent;
        s->function = (is_function || parent == NULL) ? s : parent->function;
        s->external = false;

        vec_init(s->owned);
        vec_init(s->captured);
        vec_init(s->cap_indices);

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i)
                s->table[i] = NULL;

#ifndef TY_RELEASE
        s->name = name;
#endif

        return s;
}

int
scope_capture(struct scope *s, struct symbol *sym, int parent_index)
{
                for (int i = 0; i < s->captured.count; ++i) {
                        if (s->captured.items[i] == sym) {
                                return i;
                        }
                }

                sym->captured = true;

                VPush(s->captured, sym);
                VPush(s->cap_indices, parent_index);

                LOG("scope_capture(sym=%s, scope=%p, scope->function=%p, sym->function=%p, sym->function->parent=%p, cap_index = %d)", sym->identifier, s, s->function, sym->scope->function, sym->scope->function->parent, parent_index);

                return s->captured.count - 1;
}

struct symbol *
scope_lookup(struct scope const *s, char const *id)
{
        if (s == NULL) {
                return NULL;
        }

        struct symbol *sym = local_lookup(s, id);

        if (sym != NULL) {
                return sym;
        }

        sym = scope_lookup(s->parent, id);

        if (sym == NULL) {
                return NULL;
        }

        if (sym->scope->function != s->function && !sym->global) {
                vec(struct scope *) scopes = {0};

                struct scope *scope = s->function;

                while (scope->parent->function != sym->scope->function) {
                        VPush(scopes, scope);
                        scope = scope->parent->function;
                }

                int parent_index = scope_capture(scope, sym, -1);

                for (int i = scopes.count - 1; i >= 0; --i) {
                        parent_index = scope_capture(scopes.items[i], sym, parent_index);
                }
        }

        return sym;
}

bool
scope_locally_defined(struct scope const *s, char const *id)
{
        return local_lookup(s, id) != NULL;
}

struct symbol *
scope_local_lookup(struct scope const *s, char const *id)
{
        return local_lookup(s, id);
}

struct symbol *
scope_add(struct scope *s, char const *id)
{
        uint64_t h = strhash(id);
        int i = h % SYMBOL_TABLE_SIZE;

        struct symbol *sym = Allocate(sizeof *sym);

        sym->identifier = id;
        sym->doc = NULL;
        sym->symbol = SYMBOL++;
        sym->public = false;
        sym->cnst = false;
        sym->macro = false;
        sym->fun_macro = false;
        sym->tag = -1;
        sym->class = -1;
        sym->scope = s;
        sym->captured = false;
        sym->ci = -1;

                      // s->function == global, or
        sym->global = s->function->parent == NULL ||
                      // s->function == state.global
                      (s->function->parent->parent == NULL && s->function != s);

        sym->hash = h;
        sym->next = s->table[i];

        sym->file = NULL;

        struct scope *owner = s;
        while (owner->function != owner && owner->parent != NULL) {
                owner = owner->parent;
        }

        if (sym->global) {
                sym->i = GLOBAL++;
        } else {
                sym->i = owner->owned.count;
        }

        LOG("Symbol %d (%s) is getting i = %d in scope %p", sym->symbol, id, sym->i, s);

        VPush(owner->owned, sym);

        s->table[i] = sym;

        return sym;
}

struct symbol *
scope_insert(struct scope *s, struct symbol *sym)
{
        struct symbol *newsym = Allocate(sizeof *newsym);
        *newsym = *sym;

        newsym->scope = s;
        newsym->public = false;

        int i = sym->hash % SYMBOL_TABLE_SIZE;
        newsym->next = s->table[i];
        s->table[i] = newsym;

        return newsym;
}

char const *
scope_copy(struct scope *dst, struct scope const *src)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (struct symbol *s = src->table[i]; s != NULL; s = s->next) {
                        struct symbol *conflict = scope_lookup(dst, s->identifier);
                        if (conflict != NULL && conflict->scope != src && conflict->public)
                                return conflict->identifier;
                }
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (struct symbol *s = src->table[i]; s != NULL; s = s->next) {
                        scope_insert(dst, s);
                }
        }

        return NULL;
}

char const *
scope_copy_public(struct scope *dst, struct scope const *src, bool reexport)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (struct symbol *s = src->table[i]; s != NULL; s = s->next) {
                        struct symbol *conflict = scope_lookup(dst, s->identifier);
                        if (conflict != NULL && conflict->scope != src && conflict->public)
                                return conflict->identifier;
                }
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (struct symbol *s = src->table[i]; s != NULL; s = s->next) {
                        if (s->public) {
                                scope_insert(dst, s)->public = reexport;
                        }
                }
        }

        return NULL;
}

bool
scope_is_subscope(struct scope const *sub, struct scope const *scope)
{
        while (sub != NULL) {
                if (sub->parent == scope)
                        return true;
                sub = sub->parent;
        }

        return false;
}

void
scope_capture_all(struct scope *scope, struct scope const *stop)
{
        if (scope->function->parent == NULL)
                return;

        for (struct scope *s = scope; s->function != stop->function; s = s->parent) {
                for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                        for (struct symbol *sym = s->table[i]; sym != NULL; sym = sym->next) {
                                LOG("scope_capture_all(scope=%p, scope->function=%p): capturing %s", scope, scope->function, sym->identifier);

                                struct scope *fscope = scope->function;
                                vec(struct scope *) scopes = {0};

                                while (fscope != stop->function && fscope->parent->function != stop->function && fscope->parent->function != sym->scope->function) {
                                        VPush(scopes, fscope);
                                        fscope = fscope->parent->function;
                                }

                                int parent_index = scope_capture(fscope, sym, -1);

                                for (int i = scopes.count - 1; i >= 0; --i) {
                                        parent_index = scope_capture(scopes.items[i], sym, parent_index);
                                }

                                LOG("scope_capture_all: DONE capturing %s", sym->identifier);
                        }
                }
        }
}

int
scope_get_symbol(void)
{
        return SYMBOL;
}

void
scope_set_symbol(int s)
{
        SYMBOL = s;
}

int
scope_get_completions(struct scope *scope, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (struct symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                        if (n < max && sym->public && strncmp(sym->identifier, prefix, prefix_len) == 0) {
                                out[n++] = sclone_malloc(sym->identifier);
                        }
                }
        }

        return n;
}

/* vim: set sts=8 sw=8 expandtab: */
