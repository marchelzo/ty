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

        s->is_function = is_function;
        s->parent = parent;
        s->function = (is_function || parent == NULL) ? s : parent->function;
        s->external = false;

        vec_init(s->owned);
        vec_init(s->captured);

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i)
                s->table[i] = NULL;

        return s;
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
                sym->captured = true;
                for (int i = 0; i < s->function->captured.count; ++i) {
                        if (s->function->captured.items[i] == sym) {
                                return sym;
                        }
                }
                vec_push(s->function->captured, sym);
        }

        return sym;
}

bool
scope_locally_defined(struct scope const *s, char const *id)
{
        return local_lookup(s, id) != NULL;
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
        sym->tag = -1;
        sym->class = -1;
        sym->scope = s;
        sym->captured = false;
        sym->ci = -1;

        sym->global = (s->function->parent == NULL || s->function->parent->parent == NULL);

        sym->hash = h;
        sym->next = s->table[i];

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

void
scope_insert(struct scope *s, struct symbol *sym)
{
        struct symbol *newsym = gc_alloc(sizeof *newsym);
        *newsym = *sym;

        newsym->scope = s;
        newsym->public = false;

        int i = sym->hash % SYMBOL_TABLE_SIZE;
        newsym->next = s->table[i];
        s->table[i] = newsym;
}

char const *
scope_copy_public(struct scope *dst, struct scope const *src)
{
        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i) {
                for (struct symbol *s = src->table[i]; s != NULL; s = s->next) {
                        struct symbol *conflict = scope_lookup(dst, s->identifier);
                        if (conflict != NULL && conflict->public)
                                return conflict->identifier;
                }
        }

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i)
                for (struct symbol *s = src->table[i]; s != NULL; s = s->next)
                        if (s->public)
                                scope_insert(dst, s);

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
