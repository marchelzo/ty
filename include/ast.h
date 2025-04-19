#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "location.h"
#include "vec.h"
#include "scope.h"

typedef vec(struct expression *) expression_vector;

typedef struct scope Scope;
typedef struct symbol Symbol;
typedef struct type Type;

struct expression;
struct value;

typedef struct expression Expr;
typedef struct statement Stmt;

typedef Expr *ExprTransform(Expr *, Scope *, void *);
typedef Expr *TypeTransform(Expr *, Scope *, void *);
typedef Expr *PatternTransform(Expr *, Scope *, void *);
typedef Expr *LValueTransform(Expr *, bool, Scope *, void *);
typedef Stmt *StmtTransform(Stmt *, Scope *, void *);

typedef struct {
        ExprTransform    *e_pre, *e_post;
        TypeTransform    *t_pre, *t_post;
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
        bool is_trait;
        char *name;
        char const *doc;
        Location loc;
        struct expression *super;
        expression_vector traits;
        union {
                struct {
                        expression_vector methods;
                        expression_vector getters;
                        expression_vector setters;
                        expression_vector statics;
                        expression_vector fields;
                };
                Expr *type;
        };
        expression_vector type_params;
        Scope *scope;
        Symbol *var;
};

struct condpart {
        bool def;
        struct expression *e;
        struct expression *target;
};

typedef vec(struct condpart *) condpart_vector;
typedef vec(struct statement *) statement_vector;
typedef struct class_definition ClassDefinition;

enum { FT_NONE, FT_FUNC, FT_GEN };
enum { MT_NONE, MT_INSTANCE, MT_GET, MT_SET, MT_STATIC };

#define TY_STATEMENT_TYPES        \
        X(FOR_LOOP),              \
        X(EACH_LOOP),             \
        X(DEFINITION),            \
        X(FUNCTION_DEFINITION),   \
        X(OPERATOR_DEFINITION),   \
        X(MACRO_DEFINITION),      \
        X(FUN_MACRO_DEFINITION),  \
        X(TAG_DEFINITION),        \
        X(CLASS_DEFINITION),      \
        X(TYPE_DEFINITION),       \
        X(WHILE),                 \
        X(WHILE_MATCH),           \
        X(IF_LET),                \
        X(MATCH),                 \
        X(IF),                    \
        X(RETURN),                \
        X(GENERATOR_RETURN),      \
        X(NEXT),                  \
        X(CONTINUE),              \
        X(BREAK),                 \
        X(TRY),                   \
        X(DEFER),                 \
        X(CLEANUP),               \
        X(TRY_CLEAN),             \
        X(DROP),                  \
        X(BLOCK),                 \
        X(MULTI),                 \
        X(HALT),                  \
        X(NULL),                  \
        X(EXPRESSION),            \
        X(USE),                   \
        X(IMPORT),                \
        X(EXPORT)

#define TY_EXPRESSION_TYPES                                                           \
        X(FUNCTION),                                                                  \
        X(FUNCTION_TYPE),                                                             \
        X(IMPLICIT_FUNCTION),                                                         \
        X(GENERATOR),                                                                 \
        X(INTEGER),                                                                   \
        X(BOOLEAN),                                                                   \
        X(STRING),                                                                    \
        X(REAL),                                                                      \
        X(ARRAY),                                                                     \
        X(ARRAY_COMPR),                                                               \
        X(STATEMENT),                                                                 \
        X(DICT),                                                                      \
        X(DICT_COMPR),                                                                \
        X(TAG),                                                                       \
        X(CONDITIONAL),                                                               \
        X(COMPILE_TIME),                                                              \
        X(EQ),                                                                        \
        X(MAYBE_EQ),                                                                  \
        X(TICK),                                                                      \
        X(PREFIX_QUESTION),                                                           \
        X(PREFIX_BANG),                                                               \
        X(NIL),                                                                       \
        X(SELF),                                                                      \
        X(SUPER),                                                                     \
        X(LIST),                                                                      \
        X(OR_LIST),                                                                   \
        X(CHOICE_PATTERN),                                                            \
        X(OPERATOR),                                                                  \
        X(IN),                                                                        \
        X(NOT_IN),                                                                    \
        X(REF_PATTERN),                                                               \
        X(REF_MAYBE_PATTERN),                                                         \
        X(KEEP_LOC), /* Below here we store Location in instruction pointer index */  \
        X(TUPLE),                                                                     \
        X(IDENTIFIER),                                                                \
        X(RESOURCE_BINDING),                                                          \
        X(DEFINED),                                                                   \
        X(TYPE),                                                                      \
        X(WITH),                                                                      \
        X(YIELD),                                                                     \
        X(THROW),                                                                     \
        X(TYPEOF),                                                                    \
        X(TAG_APPLICATION),                                                           \
        X(TAG_PATTERN_CALL),                                                          \
        X(TAG_PATTERN),                                                               \
        X(ALIAS_PATTERN),                                                             \
        X(TEMPLATE),                                                                  \
        X(TEMPLATE_HOLE),                                                             \
        X(TEMPLATE_VHOLE),                                                            \
        X(SPREAD),                                                                    \
        X(SPLAT),                                                                     \
        X(MUST_EQUAL),                                                                \
        X(REGEX),                                                                     \
        X(SPECIAL_STRING),                                                            \
        X(FUNCTION_CALL),                                                             \
        X(MEMBER_ACCESS),                                                             \
        X(DYN_MEMBER_ACCESS),                                                         \
        X(DYN_METHOD_CALL),                                                           \
        X(MODULE),                                                                    \
        X(NAMESPACE),                                                                 \
        X(SELF_ACCESS),                                                               \
        X(SUBSCRIPT),                                                                 \
        X(SLICE),                                                                     \
        X(METHOD_CALL),                                                               \
        X(USER_OP),                                                                   \
        X(UNARY_OP),                                                                  \
        X(BIT_AND),                                                                   \
        X(BIT_OR),                                                                    \
        X(XOR),                                                                       \
        X(SHL),                                                                       \
        X(SHR),                                                                       \
        X(MATCH_ANY),                                                                 \
        X(MATCH_NOT_NIL),                                                             \
        X(MATCH_REST),                                                                \
        X(DOT_DOT),                                                                   \
        X(DOT_DOT_DOT),                                                               \
        X(MATCH),                                                                     \
        X(VIEW_PATTERN),                                                              \
        X(NOT_NIL_VIEW_PATTERN),                                                      \
        X(PLUS),                                                                      \
        X(MINUS),                                                                     \
        X(STAR),                                                                      \
        X(DIV),                                                                       \
        X(PERCENT),                                                                   \
        X(AND),                                                                       \
        X(OR),                                                                        \
        X(KW_AND),                                                                    \
        X(KW_OR),                                                                     \
        X(WTF),                                                                       \
        X(LT),                                                                        \
        X(LEQ),                                                                       \
        X(GT),                                                                        \
        X(GEQ),                                                                       \
        X(CMP),                                                                       \
        X(DBL_EQ),                                                                    \
        X(NOT_EQ),                                                                    \
        X(CHECK_MATCH),                                                               \
        X(PLUS_EQ),                                                                   \
        X(STAR_EQ),                                                                   \
        X(DIV_EQ),                                                                    \
        X(MOD_EQ),                                                                    \
        X(MINUS_EQ),                                                                  \
        X(AND_EQ),                                                                    \
        X(OR_EQ),                                                                     \
        X(XOR_EQ),                                                                    \
        X(SHL_EQ),                                                                    \
        X(SHR_EQ),                                                                    \
        X(PREFIX_MINUS),                                                              \
        X(PREFIX_HASH),                                                               \
        X(PREFIX_AT),                                                                 \
        X(PREFIX_INC),                                                                \
        X(PREFIX_DEC),                                                                \
        X(POSTFIX_INC),                                                               \
        X(POSTFIX_DEC),                                                               \
        X(PTR),                                                                       \
        X(EVAL),                                                                      \
        X(IFDEF),                                                                     \
        X(NONE),                                                                      \
        X(MULTI_FUNCTION),                                                            \
        X(MACRO_INVOCATION),                                                          \
        X(FUN_MACRO_INVOCATION),                                                      \
        X(CTX_INFO),                                                                  \
        X(VALUE),                                                                     \
        X(MAX_TYPE)

#define ZERO_EXPR(e) memset(                               \
        ((char *)(e)) + offsetof(Expr, has_resources) + 1, \
        0,                                                 \
        sizeof (Expr) - offsetof(Expr, has_resources) - 1  \
)

#define COPY_EXPR(dst, src) memcpy(                          \
        ((char *)(dst)) + offsetof(Expr, has_resources) + 1, \
        ((char *)(src)) + offsetof(Expr, has_resources) + 1, \
        sizeof (Expr) - offsetof(Expr, has_resources) - 1    \
)

struct expression {
        void *arena;
        Expr *origin;

#define X(t) EXPRESSION_ ## t
        enum {
                TY_EXPRESSION_TYPES
        } type;
#undef X

        Location start;
        Location end;
        char const *file;
        Expr *xfunc;
        Scope *xscope;
        Type *_type;

        bool has_resources;

        union {
                intmax_t integer;
                bool boolean;
                char const *string;
                double real;
                struct statement *statement;
                struct value *v;
                void *p;
                Expr *throw;
                struct {
                        char const *uop;
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
                        struct expression *lang;
                        StringVector strings;
                        expression_vector fmts;
                        expression_vector fmtfs;
                        int_vector widths;
                        expression_vector expressions;
                };
                struct {
                        int u;
                        int b;
                        char *id;
                } op;
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
                        union {
                                struct expression *right;
                                condpart_vector p_cond;
                        };
                        struct expression *sc;
                        bool not_nil;
                };
                struct {
                        struct expression *target;
                        union {
                                struct expression *value;
                                Symbol *tmp;
                        };
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
                        Symbol *function_symbol;
                        Scope *scope;
                        expression_vector type_params;
                        StringVector params;
                        expression_vector dflts;
                        expression_vector constraints;
                        expression_vector decorators;
                        expression_vector functions;
                        union {
                                Expr *return_type;
                                Expr *parent;
                        };
                        vec(Symbol *) param_symbols;
                        vec(Symbol *) bound_symbols;
                        Stmt *body;
                        Expr *overload;
                        bool has_defer;
                        int class;
                        int ikwargs;
                        int rest;
                        int t;
                        unsigned char ftype;
                        unsigned char mtype;
                };
                struct {
                        Expr *function;
                        expression_vector args;
                        expression_vector fconds;
                        expression_vector kwargs;
                        expression_vector fkwconds;
                        StringVector kws;
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
                                Expr *member;
                                char *member_name;
                                struct {
                                        union {
                                                char const *method_name;
                                                Expr *method;
                                        };
                                        expression_vector method_args;
                                        expression_vector mconds;
                                        expression_vector method_kwargs;
                                        StringVector method_kws;
                                };
                        };
                        bool maybe;
                };
        };
};

struct statement {
        void *arena;
        Expr *origin;

#define X(t) STATEMENT_ ## t
        enum {
                STATEMENT_TYPE_START = EXPRESSION_MAX_TYPE,
                TY_STATEMENT_TYPES
        } type;
#undef X
        Location start;
        Location end;
        char const *file;
        Expr *xfunc;
        Scope *xscope;
        Type *_type;

        bool will_return;
        Namespace *ns;

        union {
                struct {
                        struct expression *expression;
                        int depth;
                };
                vec(Stmt *) statements;
                expression_vector returns;
                vec(char *) exports;
                vec(Symbol *) drop;
                struct {
                        char *module;
                        char *as;
                        vec(char *) identifiers;
                        vec(char *) aliases;
                        bool pub;
                        bool hiding;
                } import;
                struct {
                        StringVector name;
                        StringVector names;
                } use;
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
                        bool cnst;
                };
        };
};

inline static bool
is_method(Expr const *e) { return e->class != -1; }

char const *
ExpressionTypeName(Expr const *e);

Stmt *
visit_statement(Ty *ty, Stmt *s, Scope *, VisitorSet const *);

Expr *
visit_pattern(Ty *ty, Expr *e, Scope *, VisitorSet const *);

Expr *
visit_lvalue(Ty *ty, Expr *e, Scope *, VisitorSet const *, bool);

Expr *
visit_expression(Ty *ty, Expr *e, Scope *, VisitorSet const *);

Expr *
visit_type(Ty *ty, Expr *e, Scope *scope, VisitorSet const *hooks);

VisitorSet
visit_identitiy(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
