#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "location.h"
#include "tags.h"
#include "vec.h"
#include "scope.h"

typedef struct scope Scope;
typedef struct symbol Symbol;
typedef struct type Type;

typedef struct expression Expr;
typedef struct statement Stmt;
typedef struct type_bound TypeBound;
typedef struct type Type;

typedef vec(Expr *) expression_vector;
typedef vec(TypeBound) TypeBoundVector;


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
        bool redpilled;
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
                        expression_vector fields;

                        expression_vector s_methods;
                        expression_vector s_getters;
                        expression_vector s_setters;
                        expression_vector s_fields;
                };
                Expr *type;
        };
        expression_vector type_params;
        Scope *scope;
        Scope *s_scope;
        Symbol *var;
};

struct condpart {
        bool def;
        i32 when;
        Expr *e;
        Expr *target;
};

typedef vec(struct condpart *) condpart_vector;
typedef vec(Stmt *) statement_vector;
typedef struct class_definition ClassDefinition;

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
        X(EXPORT),                \
        X(SET_TYPE)

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
        X(TUPLE_SPEC),                                                                \
        X(IDENTIFIER),                                                                \
        X(RESOURCE_BINDING),                                                          \
        X(DEFINED),                                                                   \
        X(TYPE_OF),                                                                   \
        X(CAST),                                                                      \
        X(TYPE),                                                                      \
        X(TYPE_UNION),                                                                \
        X(WITH),                                                                      \
        X(YIELD),                                                                     \
        X(THROW),                                                                     \
        X(TAG_APPLICATION),                                                           \
        X(TAG_PATTERN_CALL),                                                          \
        X(TAG_PATTERN),                                                               \
        X(ALIAS_PATTERN),                                                             \
        X(TEMPLATE),                                                                  \
        X(TEMPLATE_HOLE),                                                             \
        X(TEMPLATE_VHOLE),                                                            \
        X(TEMPLATE_XHOLE),                                                            \
        X(TEMPLATE_THOLE),                                                            \
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
        X(ENTER),                                                                     \
        X(PTR),                                                                       \
        X(EVAL),                                                                      \
        X(TRACE),                                                                     \
        X(IFDEF),                                                                     \
        X(NONE),                                                                      \
        X(MULTI_FUNCTION),                                                            \
        X(MACRO_INVOCATION),                                                          \
        X(FUN_MACRO_INVOCATION),                                                      \
        X(CTX_INFO),                                                                  \
        X(PLACEHOLDER),                                                               \
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

typedef struct type_bound {
        Expr *var;
        Expr *bound;
} TypeBound;

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
        Module *mod;
        Expr *xfunc;
        Scope *xscope;
        Type *_type;

        bool has_resources;

        union {
                intmax_t integer;
                bool boolean;
                char const *string;
                double real;
                Stmt *statement;
                struct value *v;
                void *p;
                Expr *throw;
                struct {
                        char const *uop;
                        Expr *operand;
                        struct scope *escope;
                };
                struct {
                        statement_vector stmts;
                        expression_vector exprs;
                        expression_vector holes;
                } template;
                struct {
                        Symbol *atmp;
                        expression_vector elements;
                        expression_vector aconds;
                        vec(bool) optional;
                        struct {
                                Expr *pattern;
                                Expr *iter;
                                Expr *cond;
                                Stmt *where;
                        } compr;
                };
                struct {
                    Expr *m;
                    Expr *e;
                } macro;
                struct {
                        statement_vector defs;
                        Stmt *block;
                } with;
                struct {
                        Symbol *ltmp;
                        bool only_identifiers;
                        expression_vector es;
                        vec(char const *) names;
                        vec(bool) required;
                        expression_vector tconds;
                };
                struct {
                        Expr *cond;
                        Expr *then;
                        Expr *otherwise;
                };
                struct {
                        Regex const *regex;
                        Symbol const *match_symbol;
                };
                struct {
                        Expr *lang;
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
                                Expr *tagged;
                                Expr *aliased;
                        };
                        Expr *constraint;
                        Symbol *symbol;
                        char *module;
                        char *identifier;
                        Expr *namespace;
                        bool local;
                };
                struct {
                        char const *op_name;
                        Expr *left;
                        union {
                                Expr *right;
                                condpart_vector p_cond;
                        };
                        Expr *sc;
                        bool not_nil;
                };
                struct {
                        Expr *target;
                        union {
                                Expr *value;
                                Symbol *tmp;
                        };
                };
                struct {
                        int i;
                        Expr *expr;
                } hole;
                struct {
                        Expr *subject;
                        expression_vector patterns;
                        expression_vector thens;
                };
                struct {
                        char *name;
                        char const *doc;
                        char const *proto;
                        Symbol *fn_symbol;
                        Symbol *self;
                        Scope *scope;
                        expression_vector type_params;
                        StringVector params;
                        expression_vector dflts;
                        expression_vector constraints;
                        expression_vector decorators;
                        expression_vector functions;
                        union {
                                struct {
                                        Expr *return_type;
                                        Expr *yield_type;
                                };
                                Expr *parent;
                        };
                        symbol_vector param_symbols;
                        symbol_vector bound_symbols;
                        TypeBoundVector type_bounds;
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
                        Symbol *dtmp;
                        expression_vector keys;
                        expression_vector values;
                        expression_vector dconds;
                        struct {
                                Expr *pattern;
                                Expr *iter;
                                Expr *cond;
                                Stmt *where;
                        } dcompr;
                        Expr *dflt;
                };
                struct {
                        Expr *container;
                        Expr *subscript;
                };
                struct {
                        Expr *e;
                        Expr *i;
                        Expr *j;
                        Expr *k;
                } slice;
                struct {
                        Expr *object;
                        union {
                                Expr *member;
                                struct {
                                        Expr *method;
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
        Module *mod;
        Expr *xfunc;
        Scope *xscope;
        Type *_type;

        i32 when;
        bool will_return;
        Namespace *ns;

        union {
                struct {
                        Expr *expression;
                        int depth;
                };
                statement_vector statements;
                expression_vector returns;
                vec(char *) exports;
                vec(Symbol *) drop;
                struct {
                        char *module;
                        char *as;
                        StringVector identifiers;
                        StringVector aliases;
                        bool pub;
                        bool hiding;
                } import;
                struct {
                        StringVector name;
                        StringVector names;
                } use;
                union {
                        ClassDefinition tag;
                        ClassDefinition class;
                };
                struct {
                        Stmt *init;
                        Expr *cond;
                        Expr *next;
                        Stmt *body;
                } for_loop;
                struct {
                        Expr *target;
                        union {
                                Expr *array;
                                struct {
                                        Expr *a;
                                        Expr *b;
                                };
                        };
                        Stmt *body;
                        Expr *cond;
                        Expr *stop;
                } each;
                struct {
                        Stmt *s;
                        expression_vector patterns;
                        statement_vector handlers;
                        Stmt *finally;
                        bool need_trace;
                } try;
                struct {
                        Expr *e;
                        expression_vector patterns;
                        expression_vector conds;
                        statement_vector statements;
                } match;
                struct {
                        condpart_vector parts;
                        Stmt *block;
                } While;
                struct {
                        condpart_vector parts;
                        Stmt *then;
                        Stmt *otherwise;
                        bool neg;
                } iff;
                struct {
                        Expr *target;
                        Expr *value;
                        char const *doc;
                        bool pub;
                        bool cnst;
                        bool bang;
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
