#ifndef LEX_H_INCLUDED
#define LEX_H_INCLUDED

#include <stdbool.h>

#include "location.h"

typedef enum LexContext {
        LEX_PREFIX = 1,
        LEX_INFIX  = 2,
        LEX_FAKE   = 4
} LexContext;

typedef struct LexState {
        struct location loc;
        char const *end;
        bool need_nl;
        int ctx;
} LexState;

char const *
lex_error(void);

void
lex_init(char const *file, char const *src);

void
lex_start(LexState const *state);

void
lex_rewind(struct location const *where);

void
lex_end(void);

struct token
lex_token(LexContext ctx);

void
lex_save(LexState *state);

void
lex_need_nl(void);

#endif
