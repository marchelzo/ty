#ifndef LEX_H_INCLUDED
#define LEX_H_INCLUDED

#include "location.h"

typedef enum LexContext {
        LEX_PREFIX,
        LEX_INFIX
} LexContext;

typedef struct LexState {
        struct location loc;
        char const *end;
} LexState;

char const *
lex_error(void);

void
lex_init(char const *file, char const *src);

void
lex_start(LexState const *state);

void
lex_rewind(LexState const *s);

void
lex_end(void);

struct token
lex_token(LexContext ctx);

void
lex_save(LexState *state);

#endif
