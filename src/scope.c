#include <stdint.h>
#include <string.h>

#include "scope.h"
#include "alloc.h"
#include "util.h"

static int SYMBOL;

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
        struct scope *s = alloc(sizeof *s);

        s->is_function = is_function;
        s->parent = parent;
        s->function = (is_function || parent == NULL) ? s : parent->function;
        s->external = false;

        vec_init(s->function_symbols);

        for (int i = 0; i < SYMBOL_TABLE_SIZE; ++i)
                s->table[i] = NULL;

        return s;
}

struct symbol *
scope_lookup(struct scope const *s, char const *id)
{
        while (s != NULL) {
                struct symbol *sym = local_lookup(s, id);
                if (sym != NULL)
                        return sym;
                s = s->parent;
        }

        return NULL;
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

        struct symbol *sym = alloc(sizeof *sym);

        sym->identifier = id;
        sym->symbol = SYMBOL++;
        sym->public = false;
        sym->tag = -1;
        sym->scope = s;

        sym->hash = h;
        sym->next = s->table[i];

        vec_push(s->function->function_symbols, sym);

        s->table[i] = sym;
        
        return sym;
}

void
scope_insert(struct scope *s, struct symbol *sym)
{
        struct symbol *newsym = alloc(sizeof *newsym);
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
