#ifndef AST_H_INCLUDED
#define AST_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>

#include "tags.h"
#include "vec.h"
#include "scope.h"

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
} VisitorCtx;

typedef struct ns Namespace;

struct ns {
        char *id;
        char const *src_id;
        bool pub;
        bool braced;
        Namespace *next;
        Location start;
        Location end;
};

typedef struct {
        char *name;
        char *target;
        bool s;
        Location start;
        Location end;
} MethodAlias;

typedef vec(MethodAlias) MethodAliasVec;

struct class_definition {
        int symbol;
        bool pub;
        bool is_trait;
        bool redpilled;
        char *name;
        char const *module;
        char const *doc;
        Location loc;
        Expr *super;
        ExprVec traits;
        union {
                struct {
                        ExprVec methods;
                        ExprVec getters;
                        ExprVec setters;
                        ExprVec fields;

                        ExprVec s_methods;
                        ExprVec s_getters;
                        ExprVec s_setters;
                        ExprVec s_fields;

                        MethodAliasVec aliases;

                        ExprVec members;
                };
                Expr *type;
        };
        ExprVec type_params;
        Scope *scope;
        Scope *s_scope;
        Symbol *var;
        Stmt *tfn;
};

struct condpart {
        bool def;
        i32 when;
        Expr *e;
        Expr *target;
        Location start;
        Location end;
};

typedef vec(struct condpart *) condpart_vector;

typedef struct {
        Expr *pattern;
        Expr *iter;
        condpart_vector _if;
        Expr *_while;
        Stmt *where;
} ComprPart;

typedef vec(ComprPart) Comprehension;


#define TY_STATEMENT_TYPES        \
        X(FOR_LOOP),              \
        X(EACH_LOOP),             \
        X(DEFINITION),            \
        X(FUNCTION_DEFINITION),   \
        X(OPERATOR_DEFINITION),   \
        X(PATTERN_DEFINITION),    \
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
        X(SET),                                                                       \
        X(SET_COMPR),                                                                 \
        X(TAG),                                                                       \
        X(CONDITIONAL),                                                               \
        X(COMPILE_TIME),                                                              \
        X(LANG_LITERAL),                                                              \
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
        X(DYNAMIC_REGEX),                                                             \
        X(FUNCTION_CALL),                                                             \
        X(MEMBER_ACCESS),                                                             \
        X(DYN_MEMBER_ACCESS),                                                         \
        X(DYN_METHOD_CALL),                                                           \
        X(MODULE),                                                                    \
        X(NAMESPACE),                                                                 \
        X(SELF_ACCESS),                                                               \
        X(SUBSCRIPT),                                                                 \
        X(SAFE_SUBSCRIPT),                                                            \
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
        X(PACK),                                                                      \
        X(DOT_DOT),                                                                   \
        X(DOT_DOT_DOT),                                                               \
        X(PACK_UNION),                                                                \
        X(PACK_INTERSECT),                                                            \
        X(MATCH),                                                                     \
        X(PATTERN),                                                                   \
        X(VIEW_PATTERN),                                                              \
        X(NOT_NIL_VIEW_PATTERN),                                                      \
        X(OBJECT_PATTERN),                                                            \
        X(PLUS),                                                                      \
        X(MINUS),                                                                     \
        X(STAR),                                                                      \
        X(DIV),                                                                       \
        X(PERCENT),                                                                   \
        X(AND),                                                                       \
        X(OR),                                                                        \
        X(KW_AND),                                                                    \
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
        X(UNSAFE),                                                                    \
        X(MULTI_FUNCTION),                                                            \
        X(MACRO_INVOCATION),                                                          \
        X(FUN_MACRO_INVOCATION),                                                      \
        X(CTX_INFO),                                                                  \
        X(PLACEHOLDER),                                                               \
        X(VALUE),                                                                     \
        X(RESOLVED),                                                                  \
        X(ERROR),                                                                     \
        X(MAX_TYPE)

#define X(t) EXPRESSION_##t
enum {
        TY_EXPRESSION_TYPES
};
#undef X


#define X(t) STATEMENT_##t
enum {
        STATEMENT_TYPE_START = EXPRESSION_MAX_TYPE,
        TY_STATEMENT_TYPES
};
#undef X

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

typedef struct type_hint {
        T2Type type;
        i32 pc;
} TypeHint;

typedef struct fn_expr {
        char *name;
        char const *doc;
        char const *proto;
        Symbol *fn_symbol;
        Symbol *self;
        Scope *scope;
        ExprVec type_params;
        StringVector params;
        ExprVec dflts;
        ExprVec constraints;
        ExprVec retained_constraints;
        ExprVec decorators;
        ExprVec functions;
        union {
                Expr *return_type;
                Expr *parent;
        };
        symbol_vector param_symbols;
        symbol_vector bound_symbols;
        TypeBoundVector type_bounds;
        Stmt *body;
        Class *class;
        Expr *overload;
        TypeHintVector type_hints;
        bool has_defer;
        bool must_jit;
        bool inert;
        bool emit;
        bool star;
        bool clone;
        unsigned char ftype;
        unsigned char mtype;
        int ikwargs;
        int rest;
        int t;
} FnExpr;

#define NewFn()       ((FnExpr *)amA0(sizeof (FnExpr)))
#define NewClassDef() ((ClassDefinition *)amA0(sizeof (ClassDefinition)))

typedef struct call_kw {
        ExprVec kwargs;
        ExprVec fkwconds;
        StringVector kws;
} CallKw;

extern CallKw const NoCallKw;

#define CKW(e)  ((CallKw const *)(((e)->ckw != NULL) ? (e)->ckw : &NoCallKw))
#define CKWx(e) (((e)->ckw != NULL) ? (e)->ckw : ((e)->ckw = amA0(sizeof (CallKw))))
#define MKW(e)  ((CallKw const *)(((e)->mkw != NULL) ? (e)->mkw : &NoCallKw))
#define MKWx(e) (((e)->mkw != NULL) ? (e)->mkw : ((e)->mkw = amA0(sizeof (CallKw))))

typedef struct {
        ExprVec   holes;
        i32Vector ctxs;
} TemplateX;

typedef struct {
        vec(bool)     optional;
        Comprehension compr;
} ListX;

typedef struct {
        vec(bool) required;
        ExprVec   tconds;
} TupleX;

typedef struct {
        ExprVec    fmts;
        ExprVec    fmtfs;
        int_vector widths;
} FmtX;

typedef struct {
        ExprVec       dconds;
        Comprehension dcompr;
        Expr         *dflt;
} DictX;

extern TemplateX const NoTemplateX;
extern ListX     const NoListX;
extern TupleX    const NoTupleX;
extern FmtX      const NoFmtX;
extern DictX     const NoDictX;

#define ARMX(e, f, T) ((T const *)(((e)->f != NULL) ? (e)->f : &No##T))
#define ARMW(e, f, T) (((e)->f != NULL) ? (e)->f : ((e)->f = amA0(sizeof (T))))

#define TMX(t)  ARMX(t, tmx, TemplateX)
#define TMXx(t) ARMW(t, tmx, TemplateX)
#define LSX(e)  ARMX(e, lsx, ListX)
#define LSXx(e) ARMW(e, lsx, ListX)
#define TPX(e)  ARMX(e, tpx, TupleX)
#define TPXx(e) ARMW(e, tpx, TupleX)
#define FMX(e)  ARMX(e, fmx, FmtX)
#define FMXx(e) ARMW(e, fmx, FmtX)
#define DCX(e)  ARMX(e, dcx, DictX)
#define DCXx(e) ARMW(e, dcx, DictX)

struct expression {
        Expr *origin;
        Module *mod;
        Expr *xfunc;
        Scope *xscope;

        Location start;
        Location end;
        T2Type _type;

        u8 type;
        u8 dbg;
        u8 synth;

        bool annotated;
        bool has_resources;
        bool bang;
        bool maybe;

        union {
                intmax_t integer;
                bool boolean;
                Bytes string;
                char const *message;
                double real;
                Stmt *statement;
                Value *v;
                void *p;
                Expr *throw;
                struct {
                        char const *uop;
                        Expr *operand;
                        Scope *escope;
                };
                struct {
                        StmtVec stmts;
                        ExprVec exprs;
                        TemplateX *tmx;
                } template;
                struct {
                        Symbol *atmp;
                        ExprVec elements;
                        ExprVec aconds;
                        ListX *lsx;
                };
                struct {
                    Expr *m;
                    Expr *e;
                } macro;
                struct {
                        Expr *lang;
                        Bytes text;
                } lit;
                struct {
                        StmtVec defs;
                        Stmt *block;
                } with;
                struct {
                        Symbol *ltmp;
                        bool only_identifiers;
                        ExprVec es;
                        ConstStringVector names;
                        TupleX *tpx;
                };
                struct {
                        Expr *cond;
                        Expr *then;
                        Expr *_else;
                };
                struct {
                        Regex const *regex;
                        Symbol const *match_symbol;
                };
                struct {
                        union {
                                Expr *lang;
                                char const *re_flags;
                        };
                        vec(Bytes) strings;
                        ExprVec expressions;
                        FmtX *fmx;
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
                        Expr *constraint;
                } hole;
                struct {
                        Expr *subject;
                        ExprVec patterns;
                        ExprVec thens;
                };
                FnExpr *fn;
                struct {
                        Expr *function;
                        ExprVec args;
                        ExprVec fconds;
                        CallKw *ckw;
                };
                struct {
                        Symbol *dtmp;
                        ExprVec keys;
                        ExprVec values;
                        DictX *dcx;
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
                                        ExprVec method_args;
                                        ExprVec mconds;
                                        CallKw *mkw;
                                };
                        };
                };
        };
};

struct statement {
        Expr *origin;
        Module *mod;
        Expr *xfunc;
        Scope *xscope;

        Location start;
        Location end;
        T2Type _type;

        u8 type;
        u8 dbg;
        u8 synth;

        bool will_return;
        i32 when;
        Namespace *ns;

        union {
                struct {
                        Expr *expression;
                        int depth;
                };
                StmtVec statements;
                Expr *ret;
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
                        ClassDefinition *tag;
                        ClassDefinition *class;
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
                        Expr *_if;
                        Expr *_while;
                } each;
                struct {
                        Stmt *s;
                        ExprVec patterns;
                        StmtVec handlers;
                        Stmt *finally;
                        bool need_trace;
                } try;
                struct {
                        Expr *e;
                        ExprVec patterns;
                        ExprVec conds;
                        StmtVec statements;
                } match;
                struct {
                        condpart_vector parts;
                        Stmt *block;
                } _while;
                struct {
                        condpart_vector parts;
                        Stmt *then;
                        Stmt *_else;
                        bool neg;
                } _if;
                struct {
                        Expr *target;
                        Expr *value;
                        char const *doc;
                        bool pub;
                        bool cnst;
                        bool retry;
                };
        };
};

inline static bool
HasFnArm(int type)
{
        switch (type) {
        case EXPRESSION_FUNCTION:
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_NAMESPACE:
        case EXPRESSION_MODULE:
                return true;

        default:
                return false;
        }
}

inline static bool
HasClassArm(int type)
{
        switch (type) {
        case STATEMENT_CLASS_DEFINITION:
        case STATEMENT_TAG_DEFINITION:
        case STATEMENT_TYPE_DEFINITION:
                return true;

        default:
                return false;
        }
}

#define CloneExpr(e) ((CloneExpr)(ty, (e)))
inline static Expr *
(CloneExpr)(Ty *ty, Expr const *e)
{
        Expr *c = aclone(e);

        if (HasFnArm(c->type) && c->fn != NULL) {
                c->fn = aclone(c->fn);
        }

        if (c->type == EXPRESSION_FUNCTION_CALL && c->ckw != NULL) {
                c->ckw = aclone(c->ckw);
        }

        switch (c->type) {
        case EXPRESSION_METHOD_CALL:
        case EXPRESSION_DYN_METHOD_CALL:
                c->mkw = (c->mkw == NULL) ? NULL : aclone(c->mkw);
                break;

        case EXPRESSION_ARRAY:
        case EXPRESSION_SET:
        case EXPRESSION_ARRAY_COMPR:
        case EXPRESSION_SET_COMPR:
                c->lsx = (c->lsx == NULL) ? NULL : aclone(c->lsx);
                break;

        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE_SPEC:
                c->tpx = (c->tpx == NULL) ? NULL : aclone(c->tpx);
                break;

        case EXPRESSION_DICT:
        case EXPRESSION_DICT_COMPR:
                c->dcx = (c->dcx == NULL) ? NULL : aclone(c->dcx);
                break;

        case EXPRESSION_SPECIAL_STRING:
                c->fmx = (c->fmx == NULL) ? NULL : aclone(c->fmx);
                break;

        case EXPRESSION_TEMPLATE:
                c->template.tmx = (c->template.tmx == NULL) ? NULL : aclone(c->template.tmx);
                break;
        }

        return c;
}

#define CloneStmt(s) ((CloneStmt)(ty, (s)))
inline static Stmt *
(CloneStmt)(Ty *ty, Stmt const *s)
{
        Stmt *c = aclone(s);

        if (HasClassArm(c->type) && c->class != NULL) {
                c->class = aclone(c->class);
        }

        return c;
}

inline static bool
IsStmt(Expr const *expr)
{
        return (expr->type > STATEMENT_TYPE_START);
}

inline static bool
IsExpr(Stmt const *stmt)
{
        return (stmt->type < STATEMENT_TYPE_START);
}

inline static Expr *
unfurl(Expr const *e)
{
        while (e != NULL) {
                switch (e->type) {
                case EXPRESSION_STATEMENT:
                        e = (Expr *)e->statement;
                        break;

                case STATEMENT_EXPRESSION:
                        e = ((Stmt *)e)->expression;
                        break;

                default:
                        return (Expr *)e;
                }
        }

        return (Expr *)e;
}

inline static bool
HasBody(Expr const *fun)
{
        if (fun == NULL) {
                return false;
        }

        switch (fun->type) {
        case STATEMENT_FUNCTION_DEFINITION:
                return HasBody(((Stmt *)fun)->value);

        case EXPRESSION_FUNCTION:
                return (fun->fn->body != NULL);

        case EXPRESSION_MULTI_FUNCTION:
                for (int i = 0; i < vN(fun->fn->functions); ++i) {
                        if (HasBody(v__(fun->fn->functions, i))) {
                                return true;
                        }
                }
                return false;
        }

        return false;
}

inline static bool
is_method(Expr const *e) { return e->fn->class != NULL; }

char const *
ExpressionTypeName(Expr const *e);

Stmt *
visit_statement(Ty *ty, Stmt *s, Scope *, VisitorCtx *);

Expr *
visit_pattern(Ty *ty, Expr *e, Scope *, VisitorCtx *);

Expr *
visit_lvalue(Ty *ty, Expr *e, Scope *, VisitorCtx *, bool);

Expr *
visit_expression(Ty *ty, Expr *e, Scope *, VisitorCtx *);

Expr *
visit_type(Ty *ty, Expr *e, Scope *scope, VisitorCtx *);

VisitorCtx
visit_identity(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
