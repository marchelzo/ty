#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include <pcre.h>

#include "location.h"
#include "vec.h"
#include "scope.h"

typedef vec(int) int_vector;

struct expression;

struct class_definition {
        int symbol;
        char *name;
        struct expression *super;
        vec(struct expression *) methods;
};

struct statement {
        enum {
                STATEMENT_FOR_LOOP,
                STATEMENT_EACH_LOOP,
                STATEMENT_DEFINITION,
                STATEMENT_FUNCTION_DEFINITION,
                STATEMENT_TAG_DEFINITION,
                STATEMENT_CLASS_DEFINITION,
                STATEMENT_WHILE_LOOP,
                STATEMENT_WHILE_MATCH,
                STATEMENT_WHILE_LET,
                STATEMENT_IF_LET,
                STATEMENT_MATCH,
                STATEMENT_CONDITIONAL,
                STATEMENT_RETURN,
                STATEMENT_RETURN_GENERATOR,
                STATEMENT_NEXT,
                STATEMENT_CONTINUE,
                STATEMENT_THROW,
                STATEMENT_TRY,
                STATEMENT_BREAK,
                STATEMENT_BLOCK,
                STATEMENT_HALT,
                STATEMENT_NULL,
                STATEMENT_EXPRESSION,
                STATEMENT_IMPORT,
                STATEMENT_EXPORT,
        } type;
        struct location start;
        struct location end;
        union {
                struct expression *expression;
                struct expression *throw;
                vec(struct statement *) statements;
                vec(struct expression *) returns;
                vec(char *) exports;
                struct {
                        char *module;
                        char *as;
                        vec(char *) identifiers;
                } import;
                union {
                        struct class_definition tag;
                        struct class_definition class;
                };
                struct {
                        struct statement *init;
                        struct expression *cond;
                        struct expression *next;
                        struct statement *body;
                        int_vector check;
                } for_loop;
                struct {
                        struct expression *target;
                        struct expression *array;
                        struct statement *body;
                        struct expression *cond;
                        struct expression *stop;
                        int_vector check;
                } each;
                struct {
                        struct expression *cond;
                        struct statement *body;
                        int_vector check;
                } while_loop;
                struct {
                        struct expression *cond;
                        struct statement *then_branch;
                        struct statement *else_branch;
                } conditional;
                struct {
                        struct statement *s;
                        vec(struct expression *) patterns;
                        vec(struct statement *) handlers;
                        struct statement *finally;
                } try;
                struct {
                        struct expression *e;
                        vec(struct expression *) patterns;
                        vec(struct expression *) conds;
                        vec(struct statement *) statements;
                        int_vector check;
                } match;
                struct {
                        struct expression *e;
                        struct expression *pattern;
                        struct expression *cond;
                        struct statement *block;
                        int_vector check;
                } while_let;
                struct {
                        struct expression *e;
                        struct expression *pattern;
                        struct expression *cond;
                        struct statement *then;
                        struct statement *otherwise;
                        bool neg;
                } if_let;
                struct {
                        struct expression *target;
                        struct expression *value;
                };
        };
};

struct expression {
        enum {
                EXPRESSION_FUNCTION,
                EXPRESSION_IMPLICIT_FUNCTION,
                EXPRESSION_GENERATOR,
                EXPRESSION_INTEGER,
                EXPRESSION_BOOLEAN,
                EXPRESSION_STRING,
                EXPRESSION_REAL,
                EXPRESSION_ARRAY,
                EXPRESSION_ARRAY_COMPR,
                EXPRESSION_STATEMENT,
                EXPRESSION_DICT,
                EXPRESSION_DICT_COMPR,
                EXPRESSION_IDENTIFIER,
                EXPRESSION_TAG,
                EXPRESSION_CONDITIONAL,
                EXPRESSION_EQ,
                EXPRESSION_MAYBE_EQ,
                EXPRESSION_TICK,
                EXPRESSION_PREFIX_QUESTION,
                EXPRESSION_PREFIX_BANG,
                EXPRESSION_NIL,
                EXPRESSION_SELF,
                EXPRESSION_LIST,
                EXPRESSION_TUPLE,
                EXPRESSION_IN,
                EXPRESSION_NOT_IN,

                EXPRESSION_KEEP_LOC,

                EXPRESSION_YIELD,
                EXPRESSION_TAG_APPLICATION,
                EXPRESSION_SPREAD,
                EXPRESSION_MUST_EQUAL,
                EXPRESSION_REGEX,
                EXPRESSION_SPECIAL_STRING,
                EXPRESSION_FUNCTION_CALL,
                EXPRESSION_MEMBER_ACCESS,
                EXPRESSION_MODULE_ACCESS,
                EXPRESSION_SUBSCRIPT,
                EXPRESSION_METHOD_CALL,
                EXPRESSION_USER_OP,
                EXPRESSION_BIT_AND,
                EXPRESSION_BIT_OR,
                EXPRESSION_MATCH_NOT_NIL,
                EXPRESSION_MATCH_REST,
                EXPRESSION_DOT_DOT,
                EXPRESSION_DOT_DOT_DOT,
                EXPRESSION_MATCH,
                EXPRESSION_VIEW_PATTERN,
                EXPRESSION_PLUS,
                EXPRESSION_MINUS,
                EXPRESSION_STAR,
                EXPRESSION_DIV,
                EXPRESSION_PERCENT,
                EXPRESSION_AND,
                EXPRESSION_OR,
                EXPRESSION_KW_AND,
                EXPRESSION_KW_OR,
                EXPRESSION_WTF,
                EXPRESSION_LT,
                EXPRESSION_LEQ,
                EXPRESSION_GT,
                EXPRESSION_GEQ,
                EXPRESSION_CMP,
                EXPRESSION_DBL_EQ,
                EXPRESSION_NOT_EQ,
                EXPRESSION_CHECK_MATCH,
                EXPRESSION_PLUS_EQ,
                EXPRESSION_STAR_EQ,
                EXPRESSION_DIV_EQ,
                EXPRESSION_MINUS_EQ,
                EXPRESSION_PREFIX_MINUS,
                EXPRESSION_PREFIX_HASH,
                EXPRESSION_PREFIX_AT,
                EXPRESSION_PREFIX_INC,
                EXPRESSION_PREFIX_DEC,
                EXPRESSION_POSTFIX_INC,
                EXPRESSION_POSTFIX_DEC,
        } type;

        char const *filename;
        struct location start;
        struct location end;

        union {
                intmax_t integer;
                bool boolean;
                char *string;
                float real;
                struct statement *statement;
                struct expression *operand;
                struct {
                        struct symbol *atmp;
                        vec(struct expression *) elements;
                        struct {
                                struct expression *pattern;
                                struct expression *iter;
                                struct expression *cond;
                        } compr;
                };
                struct {
                        struct symbol *ltmp;
                        bool only_identifiers;
                        vec(struct expression *) es;
                };
                struct {
                        struct expression *cond;
                        struct expression *then;
                        struct expression *otherwise;
                };
                struct {
                        struct regex const *regex;
                        struct symbol const *match_symbol;
                };
                struct {
                        vec(char *) strings;
                        vec(char *) fmts;
                        vec(struct expression *) expressions;
                };
                struct {
                        bool local;
                        struct expression *tagged;
                        struct expression *constraint;
                        struct symbol *symbol;
                        char *module;
                        char *identifier;
                };
                struct {
                        char const *op_name;
                        struct expression *left;
                        struct expression *right;
                        struct expression *sc;
                };
                struct {
                        struct expression *target;
                        struct expression *value;
                };
                struct {
                        struct expression *subject;
                        vec(struct expression *) patterns;
                        vec(struct expression *) thens;
                };
                struct {
                        char *name;
                        struct symbol *function_symbol;
                        struct scope *scope;
                        vec(char *) params;
                        vec(struct expression *) dflts;
                        vec(struct expression *) constraints;
                        vec(struct symbol *) param_symbols;
                        vec(struct symbol *) bound_symbols;
                        struct statement *body;
                        bool is_method;
                        bool rest;
                        bool has_kwargs;
                };
                struct {
                        struct expression *function;
                        vec(struct expression *) args;
                        vec(struct expression *) kwargs;
                        vec(char *) kws;
                };
                struct {
                        struct symbol *dtmp;
                        vec(struct expression *) keys;
                        vec(struct expression *) values;
                        struct {
                                struct expression *pattern;
                                struct expression *iter;
                                struct expression *cond;
                        } dcompr;
                        struct expression *dflt;
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
                                        vec(struct expression *) method_kwargs;
                                        vec(char *) method_kws;
                                };
                        };
                        bool maybe;
                };
        };
};

#endif
