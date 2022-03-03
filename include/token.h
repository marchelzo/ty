#ifndef TOKEN_H_INCLUDED
#define TOKEN_H_INCLUDED

#include <limits.h>
#include <stdint.h>
#include <pcre.h>
#include <stdbool.h>

#include "vec.h"
#include "location.h"
#include "lex.h"

struct regex {
        pcre *pcre;
        pcre_extra *extra;
        char const *pattern;
};

struct token {
        enum {
                /*
                 * We start the enumeration constants slightly below INT_MAX so that they
                 * don't collide with any codepoints. This way, the type of an open parenthesis
                 * can literally be '(', which is a nice way to avoid verbose names like
                 * TOKEN_OPEN_PAREN.
                 */
                TOKEN_KEYWORD = INT_MAX - 256,
                TOKEN_IDENTIFIER,
                TOKEN_STRING,
                TOKEN_SPECIAL_STRING,
                TOKEN_REGEX,
                TOKEN_INTEGER,
                TOKEN_REAL,
                TOKEN_END,
                TOKEN_PLUS,
                TOKEN_MINUS,
                TOKEN_STAR,
                TOKEN_DIV,
                TOKEN_PERCENT,
                TOKEN_NOT_EQ,
                TOKEN_BANG,
                TOKEN_QUESTION,
                TOKEN_DBL_EQ,
                TOKEN_EQ,
                TOKEN_PLUS_EQ,
                TOKEN_STAR_EQ,
                TOKEN_DIV_EQ,
                TOKEN_MINUS_EQ,
                TOKEN_PERCENT_EQ,
                TOKEN_ARROW,
                TOKEN_FAT_ARROW,
                TOKEN_SQUIGGLY_ARROW,
                TOKEN_AND,
                TOKEN_OR,
                TOKEN_CMP,
                TOKEN_LEQ,
                TOKEN_GEQ,
                TOKEN_LT,
                TOKEN_GT,
                TOKEN_AT,
                TOKEN_INC,
                TOKEN_DEC,
                TOKEN_NEWLINE,
                TOKEN_DOT_MAYBE,
                TOKEN_DOT_DOT,
                TOKEN_DOT_DOT_DOT,
                TOKEN_USER_OP,
                TOKEN_MAYBE_EQ,
                TOKEN_WTF,
                TOKEN_CHECK_MATCH,
                TOKEN_ERROR,
        } type;
        int ctx;
        struct location start;
        struct location end;
        union {
                enum {
                        KEYWORD_RETURN,
                        KEYWORD_BREAK,
                        KEYWORD_LET,
                        KEYWORD_CONTINUE,
                        KEYWORD_IF,
                        KEYWORD_OR,
                        KEYWORD_AND,
                        KEYWORD_NOT,
                        KEYWORD_FUNCTION,
                        KEYWORD_ELSE,
                        KEYWORD_FOR,
                        KEYWORD_IN,
                        KEYWORD_WHILE,
                        KEYWORD_TRUE,
                        KEYWORD_FALSE,
                        KEYWORD_CONST,
                        KEYWORD_SELF,
                        KEYWORD_NIL,
                        KEYWORD_IMPORT,
                        KEYWORD_EXPORT,
                        KEYWORD_TAG,
                        KEYWORD_CLASS,
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
                } keyword;
                struct regex const *regex;
                struct {
                        vec(char *) strings;
                        vec(char *) fmts;
                        vec(LexState) expressions;
                        vec(struct location) starts;
                        vec(struct location) ends;
                };
                struct {
                        char *module;
                        char *identifier;
                };
                char *operator;
                char *string;
                intmax_t integer;
                float real;
        };
};

char const *
token_show(struct token const *t);

char const *
token_show_type(int type);

char const *
keyword_show(int t);

int
keyword_get_number(char const *s);

int
operator_get_token_type(char const *s);

#endif
