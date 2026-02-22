#ifndef TOKEN_H_INCLUDED
#define TOKEN_H_INCLUDED

#include <limits.h>
#include <stdint.h>
#include <stdbool.h>

#include "vec.h"
#include "lex.h"
#include "ast.h"
#include "ty.h"

enum {
        TOKEN_NEWLINE = '\n',
        TOKEN_AT = '@',
        TOKEN_BANG = '!',
        TOKEN_QUESTION = '?',
        TOKEN_EQ = '=',
        TOKEN_LT = '<',
        TOKEN_GT = '>',
        TOKEN_PLUS = '+',
        TOKEN_MINUS = '-',
        TOKEN_STAR = '*',
        TOKEN_PERCENT = '%',
        TOKEN_DIV = '/',

        /*
         * We start the enumeration constants slightly below INT_MAX so that they
         * don't collide with any codepoints. This way, the type of an open parenthesis
         * can literally be '(', which is a nice way to avoid verbose names like
         * TOKEN_OPEN_PAREN.
         */
        TOKEN_KEYWORD = INT_MAX - 4096,
        TOKEN_IDENTIFIER,
        TOKEN_STRING,
        TOKEN_SPECIAL_STRING,
        TOKEN_FUN_SPECIAL_STRING,
        TOKEN_REGEX,
        TOKEN_INTEGER,
        TOKEN_REAL,
        TOKEN_END,
        TOKEN_SHL,
        TOKEN_SHR,
        TOKEN_NOT_EQ,
        TOKEN_DBL_EQ,
        TOKEN_PLUS_EQ,
        TOKEN_STAR_EQ,
        TOKEN_DIV_EQ,
        TOKEN_MINUS_EQ,
        TOKEN_MOD_EQ,
        TOKEN_AND_EQ,
        TOKEN_OR_EQ,
        TOKEN_XOR_EQ,
        TOKEN_SHL_EQ,
        TOKEN_SHR_EQ,
        TOKEN_ARROW,
        TOKEN_FAT_ARROW,
        TOKEN_SQUIGGLY_ARROW,
        TOKEN_AND,
        TOKEN_OR,
        TOKEN_CMP,
        TOKEN_LEQ,
        TOKEN_GEQ,
        TOKEN_INC,
        TOKEN_DEC,
        TOKEN_DOT_MAYBE,
        TOKEN_DOT_DOT,
        TOKEN_DOT_DOT_DOT,
        TOKEN_USER_OP,
        TOKEN_MAYBE_EQ,
        TOKEN_WTF,
        TOKEN_ELVIS,
        TOKEN_CHECK_MATCH,
        TOKEN_TEMPLATE_BEGIN,
        TOKEN_TEMPLATE_END,
        TOKEN_EXPRESSION,
        TOKEN_COMMENT,
        TOKEN_DIRECTIVE,
        TOKEN_ERROR,
        TOKEN_TYPE_MAX
};

enum {
        TT_NONE,
        TT_FIELD,
        TT_MEMBER,
        TT_FUNC,
        TT_MACRO,
        TT_TYPE,
        TT_MODULE,
        TT_KEYWORD,
        TT_PARAM,
        TT_PUNCT,
        TT_OPERATOR,
        TT_CALL
};

typedef struct token {

        i32 type;
        i8 pp;
        i8 nl;
        i8 ctx;
        i8 tag;

        Location start;
        Location end;

        union {
                enum {
                        KEYWORD_TYPE_MIN = INT_MAX - 512,
                        KEYWORD_RETURN,
                        KEYWORD_BREAK,
                        KEYWORD_LET,
                        KEYWORD_CONTINUE,
                        KEYWORD_IF,
                        KEYWORD_DO,
                        KEYWORD_OR,
                        KEYWORD_AND,
                        KEYWORD_NOT,
                        KEYWORD_FUNCTION,
                        KEYWORD_MACRO,
                        KEYWORD_ELSE,
                        KEYWORD_FOR,
                        KEYWORD_IN,
                        KEYWORD_WHILE,
                        KEYWORD_USE,
                        KEYWORD_WHERE,
                        KEYWORD_TRUE,
                        KEYWORD_FALSE,
                        KEYWORD_CONST,
                        KEYWORD_SELF,
                        KEYWORD_NIL,
                        KEYWORD_IMPORT,
                        KEYWORD_AS,
                        KEYWORD_TAG,
                        KEYWORD_CLASS,
                        KEYWORD_TRAIT,
                        KEYWORD_MATCH,
                        KEYWORD_TRY,
                        KEYWORD_CATCH,
                        KEYWORD_FINALLY,
                        KEYWORD_THROW,
                        KEYWORD_OPERATOR,
                        KEYWORD_YIELD,
                        KEYWORD_NEXT,
                        KEYWORD_GENERATOR,
                        KEYWORD_PUB,
                        KEYWORD_DEFER,
                        KEYWORD_WITH,
                        KEYWORD_STATIC,
                        KEYWORD_SUPER,
                        KEYWORD_EVAL,
                        KEYWORD_TYPEOF,
                        KEYWORD_SET_TYPE,
                        KEYWORD_DEFINED,
                        KEYWORD_NAMESPACE,
                        KEYWORD_DBG,
                        KEYWORD_JIT
                } keyword;

                struct {
                        char *module;
                        union {
                                char *identifier;
                                char *operator;
                                char *string;
                                char *comment;
                        };
                        bool raw;
                };

                Expr *e;
                Regex const *regex;
                double real;
                imax integer;
        };
} Token;

char const *
token_show(Ty *ty, struct token const *t);

char const *
token_showx(Ty *ty, struct token const *t, char const *c);

char const *
token_show_type(Ty *ty, int type);

char const *
keyword_show(int t);

int
keyword_get_number(char const *s);

int
operator_get_token_type(char const *s);

#endif

/* vim: set sw=8 sts=8 expandtab: */
