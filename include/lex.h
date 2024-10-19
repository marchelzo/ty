#ifndef LEX_H_INCLUDED
#define LEX_H_INCLUDED

#include <stdbool.h>

#include "ty.h"
#include "location.h"

typedef enum LexContext {
        LEX_PREFIX  = 1,
        LEX_INFIX   = 2,
        LEX_FMT     = 3,
        LEX_FAKE    = 4,
        LEX_HIDDEN  = 5,
} LexContext;

typedef struct LexState {
        Location loc;

        int ctx;

        char const *start;
        char const *end;

        bool need_nl;
        bool keep_comments;
        bool blank_line;
} LexState;

extern LexState *lxst;

#define OperatorCharset "/=<~|!@%^&*-+>?.$"

char const *
lex_error(Ty *ty);

void
lex_init(Ty *ty, char const *file, char const *src);

void
lex_start(Ty *ty, LexState const *state);

void
lex_rewind(Ty *ty, struct location const *where);

void
lex_end(Ty *ty);

struct token
lex_token(Ty *ty, LexContext ctx);

int
lex_peek_char(Ty *ty, char *out);

bool
lex_next_char(Ty *ty, char *out);

void
lex_save(Ty *ty, LexState *state);

void
lex_need_nl(Ty *ty, bool);

bool
lex_keep_comments(Ty *ty, bool b);

struct location
lex_pos(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
