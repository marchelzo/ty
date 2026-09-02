#ifndef TYPES2_H_INCLUDED
#define TYPES2_H_INCLUDED

#include <stdbool.h>
#include <stddef.h>

typedef struct ty Ty;
typedef struct statement Stmt;
typedef struct types2_shadow Types2Shadow;

typedef enum types2_shadow_checkpoint {
        TYPES2_SHADOW_DECLARATION,
        TYPES2_SHADOW_CLASS_OPERATOR_DECLARATION,
        TYPES2_SHADOW_STATEMENT,
        TYPES2_SHADOW_CLASS_OPERATOR,
        TYPES2_SHADOW_CHECKPOINT_COUNT
} Types2ShadowCheckpoint;

/*
 * The types2 shadow API deliberately accepts syntax, source identity, and no
 * legacy Type objects.  Shadow state is owned by this interface and cannot
 * affect compilation results.
 */
extern bool Types2Authoritative;

void
types2_startup_finished(void);

Types2Shadow *
types2_shadow_begin(char const *unit, char const *path, char const *source);

void
types2_shadow_observe_statement(
        Ty *ty,
        Types2Shadow *shadow,
        Stmt const *stmt,
        Types2ShadowCheckpoint checkpoint,
        size_t index
);

size_t
types2_shadow_finish(Types2Shadow *shadow);

void
types2_shadow_abort(Types2Shadow *shadow);

#endif

/* vim: set sts=8 sw=8 expandtab: */
