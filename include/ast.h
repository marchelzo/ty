#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include <pcre.h>

#include "location.h"
#include "vec.h"

struct expression;
struct value;

struct environment;

struct statement {
        enum {
                STATEMENT_FOR_LOOP,
                STATEMENT_EACH_LOOP,
                STATEMENT_DEFINITION,
                STATEMENT_TAG_DEFINITION,
                STATEMENT_WHILE_LOOP,
                STATEMENT_WHILE_MATCH,
                STATEMENT_WHILE_LET,
                STATEMENT_IF_LET,
                STATEMENT_MATCH,
                STATEMENT_CONDITIONAL,
                STATEMENT_RETURN,
                STATEMENT_CONTINUE,
                STATEMENT_BREAK,
                STATEMENT_BLOCK,
                STATEMENT_HALT,
                STATEMENT_NULL,
                STATEMENT_EXPRESSION,
                STATEMENT_IMPORT,
        } type;
        struct location loc;
        union {
                char *tag;
                struct expression *expression;
                struct expression *return_value;
                vec(struct statement *) statements;
                struct {
                        char *module;
                        char *as;
                } import;
                struct {
                        struct statement *init;
                        struct expression *cond;
                        struct expression *next;

                        struct statement *body;
                } for_loop;
                struct {
                        struct expression *target;
                        struct expression *array;
                        struct statement *body;
                } each;
                struct {
                        struct expression *cond;
                        struct statement *body;
                } while_loop;
                struct {
                        struct expression *cond;
                        struct statement *then_branch;
                        struct statement *else_branch;
                } conditional;
                struct {
                        struct expression *e;
                        vec(struct expression *) patterns;
                        vec(struct expression *) conds;
                        vec(struct statement *) statements;
                } match;
                struct {
                        struct expression *e;
                        struct expression *pattern;
                        struct statement *block;
                } while_let;
                struct {
                        struct expression *e;
                        struct expression *pattern;
                        struct statement *then;
                        struct statement *otherwise;
                } if_let;
                struct {
                        struct expression *target;
                        struct expression *value;
                        bool pub;
                };
        };
};

struct expression {
        enum {
                EXPRESSION_FUNCTION,
                EXPRESSION_INTEGER,
                EXPRESSION_BOOLEAN,
                EXPRESSION_STRING,
                EXPRESSION_SPECIAL_STRING,
                EXPRESSION_REAL,
                EXPRESSION_REGEX,

                EXPRESSION_FUNCTION_CALL,
                EXPRESSION_MEMBER_ACCESS,
                EXPRESSION_SUBSCRIPT,
                EXPRESSION_ARRAY,
                EXPRESSION_OBJECT,
                EXPRESSION_METHOD_CALL,
                EXPRESSION_IDENTIFIER,
                EXPRESSION_TAG,
                EXPRESSION_TAG_APPLICATION,
                EXPRESSION_CONDITIONAL,
                EXPRESSION_EQ,

                EXPRESSION_RANGE,

                EXPRESSION_MATCH,

                EXPRESSION_MATCH_REST,
                EXPRESSION_VIEW_PATTERN,

                EXPRESSION_PLUS,
                EXPRESSION_MINUS,
                EXPRESSION_STAR,
                EXPRESSION_DIV,
                EXPRESSION_PERCENT,
                EXPRESSION_AND,
                EXPRESSION_OR,
                EXPRESSION_LT,
                EXPRESSION_LEQ,
                EXPRESSION_GT,
                EXPRESSION_GEQ,
                EXPRESSION_DBL_EQ,
                EXPRESSION_NOT_EQ,

                EXPRESSION_PLUS_EQ,
                EXPRESSION_STAR_EQ,
                EXPRESSION_DIV_EQ,
                EXPRESSION_MINUS_EQ,

                EXPRESSION_PREFIX_MINUS,
                EXPRESSION_PREFIX_BANG,
                EXPRESSION_PREFIX_AT,
                EXPRESSION_PREFIX_INC,
                EXPRESSION_PREFIX_DEC,

                EXPRESSION_POSTFIX_INC,
                EXPRESSION_POSTFIX_DEC,

                EXPRESSION_NIL,

                EXPRESSION_LIST,
        } type;

        char const *filename;
        struct location loc;

        union {
                intmax_t integer;
                bool boolean;
                char *string;
                float real;
                struct expression *operand;
                vec(struct expression *) elements;
                struct {
                        bool only_identifiers;
                        vec(struct expression *) es;
                };
                struct {
                        struct expression *cond;
                        struct expression *then;
                        struct expression *otherwise;
                };
                struct {
                        pcre *regex;
                        pcre_extra *extra;
                        char const *pattern;
                };
                struct {
                        vec(char *) strings;
                        vec(struct expression *) expressions;
                };
                struct {
                        enum { RANGE_EXCLUDE_LEFT = 1, RANGE_EXCLUDE_RIGHT = 2 } flags;
                        struct expression *low;
                        struct expression *high;
                };
                struct {
                        bool local;
                        struct expression *tagged;
                        int symbol;
                        int tag;
                        char *module;
                        char *identifier;
                };
                struct {
                        struct expression *left;
                        struct expression *right;
                };
                struct {
                        struct expression *target;
                        struct expression *value;
                };
                struct {
                        struct expression *subject;
                        vec(struct expression *) patterns;
                        vec(struct expression *) conds;
                        vec(struct expression *) thens;
                };
                struct {
                        char *name;
                        int function_symbol;
                        vec(char *) params;
                        vec(int) param_symbols;
                        vec(int) bound_symbols;
                        struct statement *body;
                };
                struct {
                        struct expression *function;
                        vec(struct expression *) args;
                };
                struct {
                        vec(struct expression *) keys;
                        vec(struct expression *) values;
                };
                struct {
                        struct expression *container;
                        struct expression *subscript;
                };
                struct {
                        struct expression *object;
                        union {
                                char *member_name;
                                struct {
                                        char const *method_name;
                                        vec(struct expression *) method_args;
                                };
                        };
                };
        };
};

#endif
