#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

#include "token.h"
#include "alloc.h"
#include "util.h"
#include "ty.h"

static char token_show_buffer[512];

static struct {
        char const *string;
        int kw_num;
} keywords[] = {
        { "Next",        KEYWORD_NEXT      },
        { "SeLf",        KEYWORD_SELF      },
        { "__defined__", KEYWORD_DEFINED   },
        { "__eval__",    KEYWORD_EVAL      },
        { "and",         KEYWORD_AND       },
        { "as",          KEYWORD_AS        },
        { "break",       KEYWORD_BREAK     },
        { "catch",       KEYWORD_CATCH     },
        { "class",       KEYWORD_CLASS     },
        { "const",       KEYWORD_CONST     },
        { "continue",    KEYWORD_CONTINUE  },
        { "defer",       KEYWORD_DEFER     },
        { "do",          KEYWORD_DO        },
        { "else",        KEYWORD_ELSE      },
        { "false",       KEYWORD_FALSE     },
        { "finally",     KEYWORD_FINALLY   },
        { "fn",          KEYWORD_FUNCTION  },
        { "for",         KEYWORD_FOR       },
        { "function",    KEYWORD_FUNCTION  },
        { "generator",   KEYWORD_GENERATOR },
        { "if",          KEYWORD_IF        },
        { "import",      KEYWORD_IMPORT    },
        { "in",          KEYWORD_IN        },
        { "let",         KEYWORD_LET       },
        { "macro",       KEYWORD_MACRO     },
        { "match",       KEYWORD_MATCH     },
        { "namespace",   KEYWORD_NAMESPACE },
        { "nil",         KEYWORD_NIL       },
        { "not",         KEYWORD_NOT       },
        { "ns",          KEYWORD_NAMESPACE },
        { "operator",    KEYWORD_OPERATOR  },
        { "or",          KEYWORD_OR        },
        { "pub",         KEYWORD_PUB       },
        { "return",      KEYWORD_RETURN    },
        { "static",      KEYWORD_STATIC    },
        { "super",       KEYWORD_SUPER     },
        { "tag",         KEYWORD_TAG       },
        { "throw",       KEYWORD_THROW     },
        { "trait",       KEYWORD_TRAIT     },
        { "true",        KEYWORD_TRUE      },
        { "try",         KEYWORD_TRY       },
        { "use",         KEYWORD_USE       },
        { "where",       KEYWORD_WHERE     },
        { "while",       KEYWORD_WHILE     },
        { "with",        KEYWORD_WITH      },
        { "yield",       KEYWORD_YIELD     },
};

static struct {
        char const *op;
        int toktype;
} operators[] = {
        { "+",   TOKEN_PLUS           },
        { "-",   TOKEN_MINUS          },
        { "*",   TOKEN_STAR           },
        { "/",   TOKEN_DIV            },
        { "%",   TOKEN_PERCENT        },
        { "^",   '^'                  },
        { "~",   '~'                  },
        { "!=",  TOKEN_NOT_EQ         },
        { "!",   TOKEN_BANG           },
        { "==",  TOKEN_DBL_EQ         },
        { "=",   TOKEN_EQ             },
        { "?=",  TOKEN_MAYBE_EQ       },
        { "->",  TOKEN_ARROW          },
        { "=>",  TOKEN_FAT_ARROW      },
        { "~>",  TOKEN_SQUIGGLY_ARROW },
        { "$~>", '$~>'                },
        { "&&",  TOKEN_AND            },
        { "||",  TOKEN_OR             },
        { "??",  TOKEN_WTF            },
        { "<=>", TOKEN_CMP            },
        { "<=",  TOKEN_LEQ            },
        { ">=",  TOKEN_GEQ            },
        { "<",   TOKEN_LT             },
        { ">",   TOKEN_GT             },
        { "@",   TOKEN_AT             },
        { "?",   TOKEN_QUESTION       },
        { "++",  TOKEN_INC            },
        { "--",  TOKEN_DEC            },
        { "+=",  TOKEN_PLUS_EQ        },
        { "*=",  TOKEN_STAR_EQ        },
        { "/=",  TOKEN_DIV_EQ         },
        { "%=",  TOKEN_MOD_EQ         },
        { "-=",  TOKEN_MINUS_EQ       },

        { "|=",   TOKEN_OR_EQ         },
        { "&=",   TOKEN_AND_EQ        },
        { "^=",   TOKEN_XOR_EQ        },
        { ">>=",  TOKEN_SHR_EQ        },
        { "<<=",  TOKEN_SHL_EQ        },

        { ":",   ':'                  },
        { "|",   '|'                  },
        { "&",   '&'                  },
        { "<<",  TOKEN_SHL            },
        { ">>",  TOKEN_SHR            },
        { "~",   '~'                  },
        { "::",  TOKEN_CHECK_MATCH    },
        { ".",   '.'                  },
        { ".?",  TOKEN_DOT_MAYBE      },
        { "..",  TOKEN_DOT_DOT        },
        { "...", TOKEN_DOT_DOT_DOT    },
        { "$",   '$'                  },
        { "\\",  '\\'                 },
};

int
operator_get_token_type(char const *s)
{
        for (size_t i = 0; i < sizeof operators / sizeof operators[0]; ++i)
                if (strcmp(s, operators[i].op) == 0)
                        return operators[i].toktype;

        return -1;
}

int
keyword_get_number(char const *s)
{
        for (size_t i = 0; i < sizeof keywords / sizeof keywords[0]; ++i)
                if (strcmp(s, keywords[i].string) == 0)
                        return keywords[i].kw_num;

        return -1;
}

char const *
keyword_show(int kw)
{
        for (size_t i = 0; i < sizeof keywords / sizeof keywords[0]; ++i)
                if (keywords[i].kw_num == kw)
                        return keywords[i].string;

        return NULL;
}

char const *
token_show_type(Ty *ty, int type)
{
        switch (type) {
        case TOKEN_PLUS:               return "operator '+'";
        case TOKEN_MINUS:              return "operator '-'";
        case TOKEN_STAR:               return "operator '*'";
        case TOKEN_DIV:                return "operator '/'";
        case TOKEN_PERCENT:            return "operator '%'";
        case TOKEN_NOT_EQ:             return "operator '!='";
        case TOKEN_BANG:               return "operator '!'";
        case TOKEN_QUESTION:           return "operator '?'";
        case TOKEN_DBL_EQ:             return "operator '=='";
        case TOKEN_PLUS_EQ:            return "operator '+='";
        case TOKEN_STAR_EQ:            return "operator '*='";
        case TOKEN_DIV_EQ:             return "operator '/='";
        case TOKEN_MINUS_EQ:           return "operator '-='";
        case TOKEN_MOD_EQ:             return "operator '%='";
        case TOKEN_EQ:                 return "token '='";
        case TOKEN_MAYBE_EQ:           return "token '?='";
        case TOKEN_WTF:                return "token '??'";
        case TOKEN_CHECK_MATCH:        return "token '::'";
        case TOKEN_ARROW:              return "token '->'";
        case TOKEN_FAT_ARROW:          return "token '=>'";
        case TOKEN_SQUIGGLY_ARROW:     return "token '~>'";
        case TOKEN_DOT_DOT:            return "token '..'";
        case TOKEN_DOT_DOT_DOT:        return "token '...'";
        case TOKEN_AND:                return "operator '&&'";
        case TOKEN_OR:                 return "operator '||'";
        case TOKEN_CMP:                return "operator '<=>'";
        case TOKEN_LEQ:                return "operator '<='";
        case TOKEN_GEQ:                return "operator '>='";
        case TOKEN_LT:                 return "operator '<'";
        case TOKEN_GT:                 return "operator '>'";
        case TOKEN_AT:                 return "operator '@'";
        case TOKEN_INC:                return "operator '++'";
        case TOKEN_DEC:                return "operator '--'";
        case TOKEN_IDENTIFIER:         return "identifier";
        case TOKEN_USER_OP:            return "user-defined operator";
        case TOKEN_STRING:             return "string";
        case TOKEN_SPECIAL_STRING:     return "interpolated string";
        case TOKEN_FUN_SPECIAL_STRING: return "interpolated string function";
        case TOKEN_INTEGER:            return "integer";
        case TOKEN_REAL:               return "real";
        case TOKEN_NEWLINE:            return "newline";
        case TOKEN_KEYWORD:            return "keyword";
        case TOKEN_DIRECTIVE:          return "compile-time directive";
        case TOKEN_END:                return "end of input";
        case TOKEN_COMMENT:            return "comment";
        case TOKEN_REGEX:              return "regex";
        case TOKEN_ERROR:              return "ERROR";
        default:                       snprintf(token_show_buffer, 512, "token '%c'", type); return sclone(ty, token_show_buffer);
        }
}

char const *
token_showx(Ty *ty, struct token const *t, char const *c)
{
        switch (t->type) {
        case TOKEN_IDENTIFIER: snprintf(token_show_buffer, 512, "identifier '%s'", t->identifier);         break;
        case TOKEN_STRING:     snprintf(token_show_buffer, 512, "string '%s'", t->string);                 break;
        case TOKEN_REGEX:      snprintf(token_show_buffer, 512, "regex /%s/", t->regex->pattern);          break;
        case TOKEN_INTEGER:    snprintf(token_show_buffer, 512, "integer '%"PRIiMAX"'", t->integer);       break;
        case TOKEN_REAL:       snprintf(token_show_buffer, 512, "real '%f'", t->real);                     break;
        case TOKEN_KEYWORD:    snprintf(token_show_buffer, 512, "keyword '%s'", keyword_show(t->keyword)); break;
        case TOKEN_USER_OP:    snprintf(token_show_buffer, 512, "operator '%s'", t->identifier);           break;
        default:               snprintf(token_show_buffer, 512, "%s", token_show_type(ty, t->type));       break;
        }

        byte_vector out = {0};

        if (t->pp) {
                dump(&out, "%sp/%s", TERM(31), TERM(0));
        }

        int ctx = ((int []) {
                [0]          = '?',
                [LEX_HIDDEN] = 'h',
                [LEX_FMT]    = 'f',
                [LEX_FAKE]   = '_',
                [LEX_PREFIX] = 'p',
                [LEX_INFIX]  = 'i'
        })[t->ctx];

        char const *ctxc = ((char const *[]) {
                [0]          = TERM(92),
                [LEX_HIDDEN] = TERM(34;1),
                [LEX_FMT]    = TERM(92),
                [LEX_FAKE]   = TERM(92;1),
                [LEX_PREFIX] = TERM(95;1),
                [LEX_INFIX]  = TERM(93;1)
        })[t->ctx];

        if (!*c) c = TERM(36);

        dump(&out, "%s%c%s %s%s%s", ctxc, ctx, TERM(0), c, token_show_buffer, TERM(0));

        if (t->nl) {
                dump(&out, " %s\\n%s", TERM(94), TERM(0));
        }

        xvP(out, '\0');

        return out.items;
}

char const *
token_show(Ty *ty, struct token const *t)
{
        return token_showx(ty, t, "");
}
