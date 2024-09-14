#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include <pcre.h>

#include "location.h"
#include "vec.h"
#include "scope.h"

typedef vec(int) int_vector;
typedef vec(struct expression *) expression_vector;

typedef struct scope Scope;

struct expression;
struct value;

typedef struct expression Expr;
typedef struct statement Stmt;

typedef Expr *ExprTransform(Expr *, Scope *, void *);
typedef Expr *PatternTransform(Expr *, Scope *, void *);
typedef Expr *LValueTransform(Expr *, bool, Scope *, void *);
typedef Stmt *StmtTransform(Stmt *, Scope *, void *);

typedef struct {
        ExprTransform    *e_pre, *e_post;
        PatternTransform *p_pre, *p_post;
        LValueTransform  *l_pre, *l_post;
        StmtTransform    *s_pre, *s_post;
        void *user;
} VisitorSet;

typedef struct ns Namespace;

struct ns {
        char *id;
        bool pub;
        bool braced;
        Namespace *next;
};

struct class_definition {
        int symbol;
        bool pub;
        char *name;
        char const *doc;
        struct expression *super;
        expression_vector methods;
        expression_vector getters;
        expression_vector setters;
        expression_vector statics;
        expression_vector fields;
};

struct condpart {
        bool def;
        struct expression *e;
        struct expression *target;
};

typedef vec(struct condpart *) condpart_vector;
typedef vec(struct statement *) statement_vector;
typedef vec(char *) name_vector;
typedef struct class_definition ClassDefinition;

enum { FT_NONE, FT_FUNC, FT_GEN };
enum { MT_NONE, MT_INSTANCE, MT_GET, MT_SET, MT_STATIC };

#define TY_STATEMENT_TYPES \
        X(FOR_LOOP), \
        X(EACH_LOOP), \
        X(DEFINITION), \
        X(FUNCTION_DEFINITION), \
        X(MACRO_DEFINITION), \
        X(FUN_MACRO_DEFINITION), \
        X(TAG_DEFINITION), \
        X(CLASS_DEFINITION), \
        X(WHILE), \
        X(WHILE_MATCH), \
        X(IF_LET), \
        X(MATCH), \
        X(IF), \
        X(RETURN), \
        X(GENERATOR_RETURN), \
        X(NEXT), \
        X(CONTINUE), \
        X(BREAK), \
        X(TRY), \
        X(DEFER), \
        X(CLEANUP), \
        X(TRY_CLEAN), \
        X(DROP), \
        X(BLOCK), \
        X(MULTI), \
        X(HALT), \
        X(NULL), \
        X(EXPRESSION), \
        X(IMPORT), \
        X(EXPORT)

struct statement {
        void *arena;

#define X(t) STATEMENT_ ## t
        enum {
                TY_STATEMENT_TYPES
        } type;
#undef X
        struct location start;
        struct location end;
        char const *filename;
        Namespace *ns;
        union {
                struct {
                        struct expression *expression;
                        int depth;
                };
                vec(Stmt *) statements;
                expression_vector returns;
                vec(char *) exports;
                vec(struct symbol *) drop;
                struct {
                        char *module;
                        char *as;
                        vec(char *) identifiers;
                        vec(char *) aliases;
                        bool pub;
                        bool hiding;
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
                } for_loop;
                struct {
                        struct expression *target;
                        struct expression *array;
                        struct statement *body;
                        struct expression *cond;
                        struct expression *stop;
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
                        char const *doc;
                        bool pub;
                };
        };
};

#define TY_EXPRESSION_TYPES \
        X(FUNCTION), \
        X(IMPLICIT_FUNCTION), \
        X(GENERATOR), \
        X(INTEGER), \
        X(BOOLEAN), \
        X(STRING), \
        X(REAL), \
        X(ARRAY), \
        X(ARRAY_COMPR), \
        X(STATEMENT), \
        X(DICT), \
        X(DICT_COMPR), \
        X(TAG), \
        X(CONDITIONAL), \
        X(COMPILE_TIME), \
        X(EQ), \
        X(MAYBE_EQ), \
        X(TICK), \
        X(PREFIX_QUESTION), \
        X(PREFIX_BANG), \
        X(NIL), \
        X(SELF), \
        X(LIST), \
        X(IN), \
        X(NOT_IN), \
        X(KEEP_LOC), \
        X(TUPLE), \
        X(IDENTIFIER), \
        X(RESOURCE_BINDING), \
        X(DEFINED), \
        X(WITH), \
        X(YIELD), \
        X(THROW), \
        X(TAG_APPLICATION), \
        X(TAG_PATTERN_CALL), \
        X(TAG_PATTERN), \
        X(ALIAS_PATTERN), \
        X(TEMPLATE), \
        X(TEMPLATE_HOLE), \
        X(TEMPLATE_VHOLE), \
        X(SPREAD), \
        X(SPLAT), \
        X(MUST_EQUAL), \
        X(REGEX), \
        X(SPECIAL_STRING), \
        X(FUNCTION_CALL), \
        X(MEMBER_ACCESS), \
        X(MODULE), \
        X(NAMESPACE), \
        X(SELF_ACCESS), \
        X(SUBSCRIPT), \
        X(SLICE), \
        X(METHOD_CALL), \
        X(USER_OP), \
        X(BIT_AND), \
        X(BIT_OR), \
        X(MATCH_ANY), \
        X(MATCH_NOT_NIL), \
        X(MATCH_REST), \
        X(DOT_DOT), \
        X(DOT_DOT_DOT), \
        X(MATCH), \
        X(VIEW_PATTERN), \
        X(NOT_NIL_VIEW_PATTERN), \
        X(PLUS), \
        X(MINUS), \
        X(STAR), \
        X(DIV), \
        X(PERCENT), \
        X(AND), \
        X(OR), \
        X(KW_AND), \
        X(KW_OR), \
        X(WTF), \
        X(LT), \
        X(LEQ), \
        X(GT), \
        X(GEQ), \
        X(CMP), \
        X(DBL_EQ), \
        X(NOT_EQ), \
        X(CHECK_MATCH), \
        X(PLUS_EQ), \
        X(STAR_EQ), \
        X(DIV_EQ), \
        X(MINUS_EQ), \
        X(PREFIX_MINUS), \
        X(PREFIX_HASH), \
        X(PREFIX_AT), \
        X(PREFIX_INC), \
        X(PREFIX_DEC), \
        X(POSTFIX_INC), \
        X(POSTFIX_DEC), \
        X(PTR), \
        X(EVAL), \
        X(IFDEF), \
        X(NONE), \
        X(MULTI_FUNCTION), \
        X(MACRO_INVOCATION), \
        X(VALUE), \
        X(EXPRESSION_MAX_TYPE)

#define ZERO_EXPR(e) memset( \
        ((char *)(e)) + offsetof(Expr, has_resources) + 1, \
        0, \
        sizeof (Expr) - offsetof(Expr, has_resources) - 1 \
)

struct expression {
        void *arena;

#define X(t) EXPRESSION_ ## t
        enum {
                TY_EXPRESSION_TYPES
        } type;
#undef X

        struct location start;
        struct location end;
        char const *filename;

        bool symbolized;
        bool has_resources;

        union {
                intmax_t integer;
                bool boolean;
                char const *string;
                float real;
                struct statement *statement;
                struct value *v;
                void *p;
                Expr *throw;
                struct {
                        struct expression *operand;
                        struct scope *escope;
                };
                struct {
                        statement_vector stmts;
                        expression_vector exprs;
                } template;
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
                        statement_vector defs;
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
                        union {
                                struct expression *tagged;
                                struct expression *aliased;
                        };
                        struct expression *constraint;
                        struct symbol *symbol;
                        char *module;
                        char *identifier;
                        Expr *namespace;
                        bool local;
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
                        char const *doc;
                        char const *proto;
                        struct symbol *function_symbol;
                        struct scope *scope;
                        vec(char *) params;
                        expression_vector dflts;
                        expression_vector constraints;
                        expression_vector decorators;
                        expression_vector functions;
                        union {
                                Expr *return_type;
                                Expr *parent;
                        };
                        vec(struct symbol *) param_symbols;
                        vec(struct symbol *) bound_symbols;
                        struct statement *body;
                        bool is_method;
                        bool is_overload;
                        bool has_defer;
                        int ikwargs;
                        int rest;
                        int t;
                        unsigned char ftype;
                        unsigned char mtype;
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
                        Expr *e;
                        Expr *i;
                        Expr *j;
                        Expr *k;
                } slice;
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

char const *
ExpressionTypeName(Expr const *e);

Stmt *
visit_statement(Stmt *s, Scope *, VisitorSet const *);

Expr *
visit_pattern(Expr *e, Scope *, VisitorSet const *);

Expr *
visit_lvalue(Expr *e, Scope *, VisitorSet const *, bool);

Expr *
visit_expression(Expr *e, Scope *, VisitorSet const *);

VisitorSet
visit_identitiy(void);

#endif

/* vim: set sts=8 sw=8 expandtab: */
