#ifndef PARSE_H_INCLUDED
#define PARSE_H_INCLUDED

#include "token.h"
#include "table.h"
#include "ast.h"

char const *
parse_error(void);

struct statement **
parse(char const *source, char const *file);

struct value
parse_get_token(int i);

struct value
parse_get_expr(int prec);

void
parse_next(void);

#endif
