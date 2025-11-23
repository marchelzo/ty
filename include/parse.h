#ifndef PARSE_H_INCLUDED
#define PARSE_H_INCLUDED

#include "token.h"
#include "table.h"
#include "ast.h"

extern Expr *LastParsedExpr;

struct statement **
parse(Ty *ty, char const *source, char const *file);

bool
parse_ex(
        Ty *,
        char const *source,
        char const *file,
        struct statement ***prog_out,
        Location *err_loc,
        TokenVector *tok_out
);

Token
parse_get_token(Ty *ty, int i);

Value
parse_get_type(Ty *ty, int prec, bool resolve, bool want_raw);

Value
parse_get_expr(Ty *ty, int prec, bool resolve, bool want_raw);

Value
parse_get_stmt(Ty *ty, int prec, bool want_raw);

void
parse_next(Ty *ty);

void
parse_push_comment(Ty *ty, Token const *tok);

TokenVector const *
parse_get_comments(Ty *ty);

noreturn void
ParseError(Ty *ty, char const *fmt, ...);

void
parse_sync_lex(Ty *ty);

void
make_with(Ty *ty, struct expression *e, statement_vector defs, struct statement *body);

char *
gensym(Ty *ty);

bool
tokenize(Ty *ty, char const *source, TokenVector *tokens_out);

#endif
