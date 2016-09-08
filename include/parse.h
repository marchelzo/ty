#ifndef PARSE_H_INCLUDED
#define PARSE_H_INCLUDED

#include "token.h"
#include "ast.h"

char const *
parse_error(void);

struct statement **
parse(char const *source);

#endif
