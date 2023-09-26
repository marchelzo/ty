#include <stdint.h>
#include <string.h>

#include "scope.h"
#include "alloc.h"
#include "log.h"
#include "util.h"

static int GLOBAL;
static int SYMBOL;

static vec(char const *) names;

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
scope_new(struct scope *parent, bool is_function)
{
        struct scope *s = gc_alloc(sizeof *s);

        s->parent = parent;
        s->function = (is_function || parent == NULL) ? s : parent->function;
        s->external = false;

        vec_init(s->owned);
        vec_init(s->captured);
        vec_init(s->cap_indices);

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i)
                s->table[i] = NULL;

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

                vec_push(s->captured, sym);
                vec_push(s->cap_indices, parent_index);

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
                        vec_push(scopes, scope);
                        scope = scope->parent->function;
                }

                int parent_index = scope_capture(scope, sym, -1);

                for (int i = scopes.count - 1; i >= 0; --i) {
                        parent_index = scope_capture(scopes.items[i], sym, parent_index);
                }

                vec_empty(scopes);
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

        vec_push(names, id);

        struct symbol *sym = gc_alloc(sizeof *sym);

        sym->identifier = id;
        sym->symbol = SYMBOL++;
        sym->public = false;
        sym->cnst = false;
        sym->macro = false;
        sym->tag = -1;
        sym->class = -1;
        sym->scope = s;
        sym->captured = false;
        sym->ci = -1;

        sym->global = (s->function->parent == NULL || s->function->parent->parent == NULL);

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

        LOG("Symbol %d (%s) is getting i = %d", sym->symbol, id, sym->i);

        vec_push(owner->owned, sym);

        s->table[i] = sym;

        return sym;
}

struct symbol *
scope_insert(struct scope *s, struct symbol *sym)
{
        struct symbol *newsym = gc_alloc(sizeof *newsym);
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
scope_capture_all(struct scope *scope)
{
        if (scope->function->parent == NULL)
                return;

        for (struct scope *s = scope->function->parent; s->function->parent != NULL && s->function->parent->parent != NULL; s = s->parent) {
                for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                        for (struct symbol *sym = s->table[i]; sym != NULL; sym = sym->next) {
                                vec(struct scope *) scopes = {0};

                                struct scope *fscope = scope->function;

                                while (fscope->parent->function != sym->scope->function) {
                                        vec_push(scopes, fscope);
                                        fscope = fscope->parent->function;
                                }

                                int parent_index = scope_capture(fscope, sym, -1);

                                for (int i = scopes.count - 1; i >= 0; --i) {
                                        parent_index = scope_capture(scopes.items[i], sym, parent_index);
                                }

                                vec_empty(scopes);
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

char const *
scope_symbol_name(int s)
{
        return names.items[s];
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
