#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "token.h"
#include "alloc.h"
#include "util.h"

static char token_show_buffer[512];

static struct {
        char const *string;
        int kw_num;
} keywords[] = {
        { "break",    KEYWORD_BREAK    },
        { "continue", KEYWORD_CONTINUE },
        { "else",     KEYWORD_ELSE     },
        { "for",      KEYWORD_FOR      },
        { "function", KEYWORD_FUNCTION },
        { "if",       KEYWORD_IF       },
        { "in",       KEYWORD_IN       },
        { "let",      KEYWORD_LET      },
        { "return",   KEYWORD_RETURN   },
        { "while",    KEYWORD_WHILE    },
        { "true",     KEYWORD_TRUE     },
        { "false",    KEYWORD_FALSE    },
        { "nil",      KEYWORD_NIL      },
        { "import",   KEYWORD_IMPORT   },
        { "export",   KEYWORD_EXPORT   },
        { "tag",      KEYWORD_TAG      },
        { "match",    KEYWORD_MATCH    },
};

static struct {
        char const *op;
        int toktype;
} operators[] = {
        { "+",  TOKEN_PLUS           },
        { "-",  TOKEN_MINUS          },
        { "*",  TOKEN_STAR           },
        { "/",  TOKEN_DIV            },
        { "%",  TOKEN_PERCENT        },
        { "!=", TOKEN_NOT_EQ         },
        { "!",  TOKEN_BANG           },
        { "==", TOKEN_DBL_EQ         },
        { "=",  TOKEN_EQ             },
        { "->", TOKEN_ARROW          },
        { "=>", TOKEN_FAT_ARROW      },
        { "~>", TOKEN_SQUIGGLY_ARROW },
        { "&&", TOKEN_AND            },
        { "||", TOKEN_OR             },
        { "|",  TOKEN_BIT_OR         },
        { "<=", TOKEN_LEQ            },
        { ">=", TOKEN_GEQ            },
        { "<",  TOKEN_LT             },
        { ">",  TOKEN_GT             },
        { "@",  TOKEN_AT             },
        { "++", TOKEN_INC            },
        { "--", TOKEN_DEC            },
        { "+=", TOKEN_PLUS_EQ        },
        { "*=", TOKEN_STAR_EQ        },
        { "/=", TOKEN_DIV_EQ         },
        { "-=", TOKEN_MINUS_EQ       },
};

int
operator_get_token_type(char const *s)
{
        for (size_t i = 0; i < sizeof operators / sizeof operators[0]; ++i) {
                if (strcmp(s, operators[i].op) == 0) {
                        return operators[i].toktype;
                }
        }

        return -1;
}

int
keyword_get_number(char const *s)
{
        for (size_t i = 0; i < sizeof keywords / sizeof keywords[0]; ++i) {
                if (strcmp(s, keywords[i].string) == 0) {
                        return keywords[i].kw_num;
                }
        }

        return -1;
}

char const *
keyword_show(int kw)
{
        for (size_t i = 0; i < sizeof keywords / sizeof keywords[0]; ++i) {
                if (keywords[i].kw_num == kw) {
                        return keywords[i].string;
                }
        }

        return NULL;
}

char const *
token_show_type(int type)
{
        switch (type) {
        case TOKEN_PLUS:           return "operator '+'";
        case TOKEN_MINUS:          return "operator '-'";
        case TOKEN_STAR:           return "operator '*'";
        case TOKEN_DIV:            return "operator '/'";
        case TOKEN_PERCENT:        return "operator '%'";
        case TOKEN_NOT_EQ:         return "operator '!='";
        case TOKEN_BANG:           return "operator '!'";
        case TOKEN_DBL_EQ:         return "operator '=='";
        case TOKEN_PLUS_EQ:        return "operator '+='";
        case TOKEN_STAR_EQ:        return "operator '*='";
        case TOKEN_DIV_EQ:         return "operator '/='";
        case TOKEN_MINUS_EQ:       return "operator '-='";
        case TOKEN_PERCENT_EQ:     return "operator '%='";
        case TOKEN_EQ:             return "token '='";
        case TOKEN_ARROW:          return "token '->'";
        case TOKEN_FAT_ARROW:      return "token '=>'";
        case TOKEN_SQUIGGLY_ARROW: return "token '~>'";
        case TOKEN_DOT_DOT:        return "token '..'";
        case TOKEN_AND:            return "operator '&&'";
        case TOKEN_OR:             return "operator '||'";
        case TOKEN_BIT_OR:         return "token '|'";
        case TOKEN_LEQ:            return "operator '<='";
        case TOKEN_GEQ:            return "operator '>='";
        case TOKEN_LT:             return "operator '<'";
        case TOKEN_GT:             return "operator '>'";
        case TOKEN_AT:             return "operator '@'";
        case TOKEN_INC:            return "operator '++'";
        case TOKEN_DEC:            return "operator '--'";
        case TOKEN_IDENTIFIER:     return "identifier";
        case TOKEN_TAG:            return "tag";
        case TOKEN_STRING:         return "string";
        case TOKEN_INTEGER:        return "integer";
        case TOKEN_REAL:           return "real";
        case TOKEN_NEWLINE:        return "newline";
        case TOKEN_KEYWORD:        return "keyword";
        case TOKEN_END:            return "end of input";
        default:                   snprintf(token_show_buffer, 512, "token '%c'", type); return sclone(token_show_buffer);
        }
}

char const *
token_show(struct token const *t)
{
        switch (t->type) {
        case TOKEN_IDENTIFIER: snprintf(token_show_buffer, 512, "identifier '%s'", t->identifier);         break;
        case TOKEN_TAG:        snprintf(token_show_buffer, 512, "tag '%s'", t->tag);                       break;
        case TOKEN_STRING:     snprintf(token_show_buffer, 512, "string '%s'", t->string);                 break;
        case TOKEN_INTEGER:    snprintf(token_show_buffer, 512, "integer '%"PRIiMAX"'", t->integer);       break;
        case TOKEN_REAL:       snprintf(token_show_buffer, 512, "real '%f'", t->real);                     break;
        case TOKEN_KEYWORD:    snprintf(token_show_buffer, 512, "keyword '%s'", keyword_show(t->keyword)); break;
        default:               return token_show_type(t->type);
        }

        return sclone(token_show_buffer);
}
