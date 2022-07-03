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
struct value;

struct class_definition {
        int symbol;
        bool pub;
        char *name;
        struct expression *super;
        vec(struct expression *) methods;
};

struct condpart {
        bool def;
        struct expression *e;
        struct expression *target;
};

typedef vec(struct condpart *) condpart_vector;
typedef vec(struct expression *) expression_vector;
typedef vec(char *) name_vector;

enum { FT_NONE, FT_FUNC, FT_GEN };

struct statement {
        enum {
                STATEMENT_FOR_LOOP,
                STATEMENT_EACH_LOOP,
                STATEMENT_DEFINITION,
                STATEMENT_FUNCTION_DEFINITION,
                STATEMENT_MACRO_DEFINITION,
                STATEMENT_TAG_DEFINITION,
                STATEMENT_CLASS_DEFINITION,
                STATEMENT_WHILE,
                STATEMENT_WHILE_MATCH,
                STATEMENT_IF_LET,
                STATEMENT_MATCH,
                STATEMENT_IF,
                STATEMENT_RETURN,
                STATEMENT_RETURN_GENERATOR,
                STATEMENT_NEXT,
                STATEMENT_CONTINUE,
                STATEMENT_BREAK,
                STATEMENT_THROW,
                STATEMENT_TRY,
                STATEMENT_DEFER,
                STATEMENT_CLEANUP,
                STATEMENT_TRY_CLEAN,
                STATEMENT_DROP,
                STATEMENT_BLOCK,
                STATEMENT_MULTI,
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
                expression_vector returns;
                vec(char *) exports;
                vec(struct symbol *) drop;
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
                        struct statement *s;
                        expression_vector patterns;
                        vec(struct statement *) handlers;
                        struct statement *finally;
                } try;
                struct {
                        struct expression *e;
                        expression_vector patterns;
                        expression_vector conds;
                        vec(struct statement *) statements;
                } match;
                struct {
                        condpart_vector parts;
                        struct statement *block;
                } While;
                struct {
                        condpart_vector parts;
                        struct statement *then;
                        struct statement *otherwise;
                        bool neg;
                } iff;
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

                EXPRESSION_WITH,
                EXPRESSION_YIELD,
                EXPRESSION_TAG_APPLICATION,
                EXPRESSION_SPREAD,
                EXPRESSION_SPLAT,
                EXPRESSION_MUST_EQUAL,
                EXPRESSION_REGEX,
                EXPRESSION_SPECIAL_STRING,
                EXPRESSION_FUNCTION_CALL,
                EXPRESSION_MEMBER_ACCESS,
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
                EXPRESSION_NOT_NIL_VIEW_PATTERN,
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

                EXPRESSION_MACRO_INVOCATION,
                EXPRESSION_VALUE,
                EXPRESSION_MAX_TYPE,
                EXPRESSION_SYMBOLIZED = 1 << 20
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
                struct value *v;
                struct {
                        struct symbol *atmp;
                        expression_vector elements;
                        expression_vector aconds;
                        vec(bool) optional;
                        struct {
                                struct expression *pattern;
                                struct expression *iter;
                                struct expression *cond;
                        } compr;
                };
                struct {
                    struct expression *m;
                    struct expression *e;
                } macro;
                struct {
                        struct statement *let;
                        struct statement *block;
                } with;
                struct {
                        struct symbol *ltmp;
                        bool only_identifiers;
                        expression_vector es;
                        vec(char const *) names;
                        vec(bool) required;
                        expression_vector tconds;
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
                        expression_vector expressions;
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
                        bool not_nil;
                };
                struct {
                        struct expression *target;
                        struct expression *value;
                };
                struct {
                        struct expression *subject;
                        expression_vector patterns;
                        vec(struct expression *) thens;
                };
                struct {
                        char *name;
                        struct symbol *function_symbol;
                        struct scope *scope;
                        vec(char *) params;
                        expression_vector dflts;
                        expression_vector constraints;
                        struct expression *return_type;
                        vec(struct symbol *) param_symbols;
                        vec(struct symbol *) bound_symbols;
                        struct statement *body;
                        bool is_method;
                        bool has_defer;
                        int ikwargs;
                        int rest;
                        unsigned char ftype;
                };
                struct {
                        struct expression *function;
                        expression_vector args;
                        expression_vector fconds;
                        expression_vector kwargs;
                        expression_vector fkwconds;
                        name_vector kws;
                };
                struct {
                        struct symbol *dtmp;
                        expression_vector keys;
                        expression_vector values;
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
                                        expression_vector method_args;
                                        expression_vector mconds;
                                        expression_vector method_kwargs;
                                        name_vector method_kws;
                                };
                        };
                        bool maybe;
                };
        };
};

#endif
