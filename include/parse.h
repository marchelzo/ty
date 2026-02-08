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
        TokenVector *tokens_out
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

noreturn void
ParseError(Ty *ty, char const *fmt, ...);

void
parse_sync_lex(Ty *ty);

void
make_with(Ty *ty, struct expression *e, StmtVec defs, struct statement *body);

char *
gensym(Ty *ty);

bool
tokenize(Ty *ty, char const *source, TokenVector *tokens_out);

#endif
