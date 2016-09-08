#ifndef LEX_H_INCLUDED
#define LEX_H_INCLUDED

enum lex_context {
        LEX_PREFIX,
        LEX_INFIX
};

char const *
lex_error(void);

void
lex_init(void);

void
lex_start(char const *s);

void
lex_end(void);

struct token
lex_token(enum lex_context ctx);

#endif
