#ifndef SCOPE_H_INCLUDED
#define SCOPE_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>

#include "vec.h"

enum {
        SYMBOL_TABLE_SIZE = 16
};

typedef struct symbol {
        char const *identifier;
        char const *doc;
        int symbol;
        int tag;
        int class;
        bool public;
        bool cnst;
        bool macro;
        bool fun_macro;
        bool captured;
        bool init;
        int i;
        int ci;
        bool global;
        bool namespace;

        struct location loc;
        char const *file;

        struct scope *scope;

        uint64_t hash;
        struct symbol *next;
} Symbol;

typedef struct scope {
        bool external;

        struct symbol *table[SYMBOL_TABLE_SIZE];

        vec(struct symbol *) owned;
        vec(struct symbol *) captured;
        vec(int) cap_indices;

        struct scope *parent;
        struct scope *function;

#ifndef TY_RELEASE
        char const *name;
#endif
} Scope;

struct scope *
_scope_new(
#ifndef TY_RELEASE
        char const *name,
#endif
        struct scope *parent,
        bool function
);

#ifdef TY_RELEASE
  #define scope_new(n, p, f) _scope_new(p, f)
#else
  #define scope_new(n, p, f) _scope_new(n, p, f)
#endif

struct symbol *
scope_add(struct scope *s, char const *id);

Symbol *
scope_add_namespace(Scope *s, char const *id, Scope *ns);

int
scope_capture(struct scope *s, struct symbol *sym, int parent_index);

bool
scope_locally_defined(struct scope const *s, char const *id);

struct symbol *
scope_lookup(struct scope const *s, char const *id);

struct symbol *
scope_local_lookup(struct scope const *s, char const *id);

struct symbol *
scope_insert(struct scope *s, struct symbol *sym);

struct symbol *
scope_insert_as(struct scope *s, struct symbol *sym, char const *id);

bool
scope_is_subscope(struct scope const *sub, struct scope const *scope);

char const *
scope_copy_public(struct scope *dst, struct scope const *src, bool reexport);

char const *
scope_copy_public_except(struct scope *dst, struct scope const *src, char const **skip, int n, bool reexport);

char const *
scope_copy(struct scope *dst, struct scope const *src);

int
scope_get_symbol(void);

void
scope_set_symbol(int s);

char const *
scope_symbol_name(int s);

void
scope_capture_all(struct scope *scope, struct scope const *stop);

int
scope_get_completions(struct scope *scope, char const *prefix, char **out, int max);

#ifndef TY_RELEASE
char const *
scope_name(struct scope const *s);
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
