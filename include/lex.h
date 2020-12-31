#ifndef LEX_H_INCLUDED
#define LEX_H_INCLUDED

#include "location.h"

enum lex_context {
        LEX_PREFIX,
        LEX_INFIX
};

struct lex_state {
        char const *s;
        struct location loc;
};

char const *
lex_error(void);

void
lex_init(char const *file);

void
lex_start(char const *s);

void
lex_end(void);

struct token
lex_token(enum lex_context ctx);

void
lex_save(struct lex_state *state);

void
lex_rewind(struct lex_state const *state);

#endif
