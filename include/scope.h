#ifndef SCOPE_H_INCLUDED
#define SCOPE_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>

#include "vec.h"

enum {
        SYMBOL_TABLE_SIZE = 16
};

struct symbol {
        char const *identifier;
        int symbol;
        int tag;
        int class;
        bool public;
        bool cnst;
        bool macro;
        bool captured;
        int i;
        int ci;
        bool global;

        struct location loc;
        char const *file;

        struct scope *scope;

        uint64_t hash;
        struct symbol *next;
};

struct scope {
        bool external;

        struct symbol *table[SYMBOL_TABLE_SIZE];

        vec(struct symbol *) owned;
        vec(struct symbol *) captured;
        vec(int) cap_indices;

        struct scope *parent;
        struct scope *function;
};

struct scope *
scope_new(struct scope *parent, bool function);

struct symbol *
scope_add(struct scope *s, char const *id);

int
scope_capture(struct scope *s, struct symbol *sym, int parent_index);

bool
scope_locally_defined(struct scope const *s, char const *id);

struct symbol *
scope_lookup(struct scope const *s, char const *id);

struct symbol *
scope_insert(struct scope *s, struct symbol *sym);

bool
scope_is_subscope(struct scope const *sub, struct scope const *scope);

char const *
scope_copy_public(struct scope *dst, struct scope const *src, bool reexport);

int
scope_get_symbol(void);

void
scope_set_symbol(int s);

char const *
scope_symbol_name(int s);

void
scope_capture_all(struct scope *scope);

int
scope_get_completions(struct scope *scope, char const *prefix, char **out, int max);

#endif
