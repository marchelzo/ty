#ifndef PARSE_H_INCLUDED
#define PARSE_H_INCLUDED

#include "token.h"
#include "table.h"
#include "ast.h"

struct statement **
parse(Ty *ty, char const *source, char const *file);

bool
parse_module(Ty *ty, Module *mod);

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

Module *
TyParserModule(Ty *ty);

TokenVector const *
TyParserTokens(Ty *ty);

noreturn void
ParseError(Ty *ty, char const *fmt, ...);

void
parse_sync_lex(Ty *ty);

void
make_with(Ty *ty, struct expression *e, StmtVec defs, struct statement *body);

char *
gensym(Ty *ty);

void
parse_reset(Ty *ty);

#endif
