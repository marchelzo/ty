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

typedef svec(MethodAlias) MethodAliasVec;

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

typedef svec(struct condpart *) condpart_vector;

typedef struct {
        Expr *pattern;
        Expr *iter;
        condpart_vector _if;
        Expr *_while;
        Stmt *where;
} ComprPart;

typedef svec(ComprPart) Comprehension;


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

typedef svec(bool)  AstBoolVec;
typedef svec(Bytes) AstBytesVec;

typedef struct {
        StmtVec stmts;
        ExprVec exprs;
        ExprVec holes;
        i32Vector ctxs;
} AstTemplate;

typedef struct {
        Expr *m;
        Expr *e;
} AstMacro;

typedef struct {
        Expr *lang;
        Bytes text;
} AstLit;

typedef struct {
        StmtVec defs;
        Stmt *block;
} AstWith;

typedef struct {
        int u;
        int b;
        char *id;
} AstOp;

typedef struct {
        int i;
        Expr *expr;
        Expr *constraint;
} AstHole;

typedef struct {
        Expr *e;
        Expr *i;
        Expr *j;
        Expr *k;
} AstSlice;

typedef struct {
        char *module;
        char *as;
        StringVector identifiers;
        StringVector aliases;
        bool pub;
        bool hiding;
} StmtImport;

typedef struct {
        StringVector name;
        StringVector names;
} StmtUse;

typedef struct {
        Stmt *init;
        Expr *cond;
        Expr *next;
        Stmt *body;
} StmtFor;

typedef struct {
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
} StmtEach;

typedef struct {
        Stmt *s;
        ExprVec patterns;
        StmtVec handlers;
        Stmt *finally;
        bool need_trace;
} StmtTry;

typedef struct {
        Expr *e;
        ExprVec patterns;
        ExprVec conds;
        StmtVec statements;
} StmtMatch;

typedef struct {
        condpart_vector parts;
        Stmt *block;
} StmtWhile;

typedef struct {
        condpart_vector parts;
        Stmt *then;
        Stmt *_else;
        bool neg;
} StmtIf;

typedef struct type_bound {
        Expr *var;
        Expr *bound;
} TypeBound;

typedef struct type_hint {
        T2Type type;
        iptr pc;
} TypeHint;

#define TY_EXPR_FIELDS                                     \
        X(integer,              intmax_t,           0, 0)  \
        X(boolean,              bool,               0, 0)  \
        X(string,               Bytes,              0, 0)  \
        X(message,              const char *,       0, 0)  \
        X(real,                 double,             0, 0)  \
        X(statement,            Stmt *,             0, 0)  \
        X(v,                    Value *,            0, 0)  \
        X(p,                    void *,             0, 0)  \
        X(throw,                Expr *,             0, 0)  \
        X(uop,                  const char *,       0, 0)  \
        X(operand,              Expr *,             1, 0)  \
        X(escope,               Scope *,            2, 0)  \
        X(template,             AstTemplate,        0, 0)  \
        X(atmp,                 Symbol *,           0, 0)  \
        X(elements,             ExprVec,            1, 0)  \
        X(aconds,               ExprVec,            3, 0)  \
        X(optional,             AstBoolVec,         5, 0)  \
        X(compr,                Comprehension,      7, 0)  \
        X(macro,                AstMacro,           0, 0)  \
        X(lit,                  AstLit,             0, 0)  \
        X(with,                 AstWith,            0, 0)  \
        X(ltmp,                 Symbol *,           0, 0)  \
        X(only_identifiers,     bool,               1, 0)  \
        X(es,                   ExprVec,            2, 0)  \
        X(names,                ConstStringVector,  4, 0)  \
        X(required,             AstBoolVec,         6, 0)  \
        X(tconds,               ExprVec,            8, 0)  \
        X(cond,                 Expr *,             0, 0)  \
        X(then,                 Expr *,             1, 0)  \
        X(_else,                Expr *,             2, 0)  \
        X(regex,                const Regex *,      0, 0)  \
        X(match_symbol,         const Symbol *,     1, 0)  \
        X(lang,                 Expr *,             0, 0)  \
        X(re_flags,             const char *,       0, 0)  \
        X(strings,              AstBytesVec,        1, 0)  \
        X(fmts,                 ExprVec,            3, 0)  \
        X(fmtfs,                ExprVec,            5, 0)  \
        X(widths,               int_vector,         7, 0)  \
        X(expressions,          ExprVec,            9, 0)  \
        X(op,                   AstOp,              0, 0)  \
        X(tagged,               Expr *,             0, 0)  \
        X(aliased,              Expr *,             0, 0)  \
        X(constraint,           Expr *,             1, 0)  \
        X(symbol,               Symbol *,           2, 0)  \
        X(module,               char *,             3, 0)  \
        X(identifier,           char *,             4, 0)  \
        X(namespace,            Expr *,             5, 0)  \
        X(local,                bool,               6, 0)  \
        X(op_name,              const char *,       0, 0)  \
        X(left,                 Expr *,             1, 0)  \
        X(right,                Expr *,             2, 0)  \
        X(p_cond,               condpart_vector,    2, 0)  \
        X(sc,                   Expr *,             4, 0)  \
        X(not_nil,              bool,               5, 0)  \
        X(target,               Expr *,             0, 0)  \
        X(value,                Expr *,             1, 0)  \
        X(tmp,                  Symbol *,           1, 0)  \
        X(hole,                 AstHole,            0, 0)  \
        X(subject,              Expr *,             0, 0)  \
        X(patterns,             ExprVec,            1, 0)  \
        X(thens,                ExprVec,            3, 0)  \
        X(name,                 char *,             0, 0)  \
        X(scope,                Scope *,            1, 0)  \
        X(return_type,          Expr *,             2, 0)  \
        X(parent,               Expr *,             2, 0)  \
        X(doc,                  const char *,       3, 0)  \
        X(proto,                const char *,       4, 0)  \
        X(fn_symbol,            Symbol *,           5, 0)  \
        X(self,                 Symbol *,           6, 0)  \
        X(type_params,          ExprVec,            7, 0)  \
        X(params,               StringVector,       9, 0)  \
        X(dflts,                ExprVec,           11, 0)  \
        X(constraints,          ExprVec,           13, 0)  \
        X(retained_constraints, ExprVec,           15, 0)  \
        X(decorators,           ExprVec,           17, 0)  \
        X(functions,            ExprVec,           19, 0)  \
        X(param_symbols,        symbol_vector,     21, 0)  \
        X(bound_symbols,        symbol_vector,     23, 0)  \
        X(type_bounds,          TypeBoundVector,   25, 0)  \
        X(body,                 Stmt *,            27, 0)  \
        X(class,                Class *,           28, 0)  \
        X(overload,             Expr *,            29, 0)  \
        X(type_hints,           TypeHintVector,    30, 0)  \
        X(has_defer,            bool,              32, 0)  \
        X(must_jit,             bool,              32, 1)  \
        X(inert,                bool,              32, 2)  \
        X(emit,                 bool,              32, 3)  \
        X(star,                 bool,              32, 4)  \
        X(clone,                bool,              32, 5)  \
        X(ftype,                unsigned char,     32, 6)  \
        X(mtype,                unsigned char,     32, 7)  \
        X(ikwargs,              int,               33, 0)  \
        X(rest,                 int,               33, 4)  \
        X(t,                    int,               34, 0)  \
        X(function,             Expr *,             0, 0)  \
        X(args,                 ExprVec,            1, 0)  \
        X(fconds,               ExprVec,            3, 0)  \
        X(kwargs,               ExprVec,            5, 0)  \
        X(fkwconds,             ExprVec,            7, 0)  \
        X(kws,                  StringVector,       9, 0)  \
        X(dtmp,                 Symbol *,           0, 0)  \
        X(keys,                 ExprVec,            1, 0)  \
        X(values,               ExprVec,            3, 0)  \
        X(dconds,               ExprVec,            5, 0)  \
        X(dcompr,               Comprehension,      7, 0)  \
        X(dflt,                 Expr *,             9, 0)  \
        X(container,            Expr *,             0, 0)  \
        X(subscript,            Expr *,             1, 0)  \
        X(slice,                AstSlice,           0, 0)  \
        X(object,               Expr *,             0, 0)  \
        X(member,               Expr *,             1, 0)  \
        X(method,               Expr *,             1, 0)  \
        X(method_args,          ExprVec,            2, 0)  \
        X(mconds,               ExprVec,            4, 0)  \
        X(method_kwargs,        ExprVec,            6, 0)  \
        X(method_kws,           StringVector,       8, 0)  \
        X(maybe,                bool,              10, 0) 

#define TY_STMT_FIELDS                                 \
        X(expression, Expr *,                   0, 0)  \
        X(depth,      int,                      1, 0)  \
        X(statements, StmtVec,                  0, 0)  \
        X(ret,        Expr *,                   0, 0)  \
        X(exports,    StringVector,             0, 0)  \
        X(drop,       symbol_vector,            0, 0)  \
        X(import,     StmtImport,               0, 0)  \
        X(use,        StmtUse,                  0, 0)  \
        X(tag,        ClassDefinition,          0, 0)  \
        X(class,      ClassDefinition,          0, 0)  \
        X(for_loop,   StmtFor,                  0, 0)  \
        X(each,       StmtEach,                 0, 0)  \
        X(try,        StmtTry,                  0, 0)  \
        X(match,      StmtMatch,                0, 0)  \
        X(_while,     StmtWhile,                0, 0)  \
        X(_if,        StmtIf,                   0, 0)  \
        X(target,     Expr *,                   0, 0)  \
        X(value,      Expr *,                   1, 0)  \
        X(doc,        const char *,             2, 0)  \
        X(pub,        bool,                     3, 0)  \
        X(cnst,       bool,                     3, 1)  \
        X(retry,      bool,                     3, 2) 

#define TY_EXPR_VIEWS               \
        V(integer,               0)  \
        V(boolean,               1)  \
        V(string,                2)  \
        V(message,               3)  \
        V(real,                  4)  \
        V(statement,             5)  \
        V(v,                     6)  \
        V(p,                     7)  \
        V(throw,                 8)  \
        V(uop,                   9)  \
        V(operand,               9)  \
        V(escope,                9)  \
        V(template,             10)  \
        V(atmp,                 11)  \
        V(elements,             11)  \
        V(aconds,               11)  \
        V(optional,             11)  \
        V(compr,                11)  \
        V(macro,                12)  \
        V(lit,                  13)  \
        V(with,                 14)  \
        V(ltmp,                 15)  \
        V(only_identifiers,     15)  \
        V(es,                   15)  \
        V(names,                15)  \
        V(required,             15)  \
        V(tconds,               15)  \
        V(cond,                 16)  \
        V(then,                 16)  \
        V(_else,                16)  \
        V(regex,                17)  \
        V(match_symbol,         17)  \
        V(lang,                 18)  \
        V(re_flags,             18)  \
        V(strings,              18)  \
        V(fmts,                 18)  \
        V(fmtfs,                18)  \
        V(widths,               18)  \
        V(expressions,          18)  \
        V(op,                   19)  \
        V(tagged,               20)  \
        V(aliased,              20)  \
        V(constraint,           20)  \
        V(symbol,               20)  \
        V(module,               20)  \
        V(identifier,           20)  \
        V(namespace,            20)  \
        V(local,                20)  \
        V(op_name,              21)  \
        V(left,                 21)  \
        V(right,                21)  \
        V(p_cond,               21)  \
        V(sc,                   21)  \
        V(not_nil,              21)  \
        V(target,               22)  \
        V(value,                22)  \
        V(tmp,                  22)  \
        V(hole,                 23)  \
        V(subject,              24)  \
        V(patterns,             24)  \
        V(thens,                24)  \
        V(name,                 25)  \
        V(scope,                25)  \
        V(return_type,          25)  \
        V(parent,               25)  \
        V(doc,                  25)  \
        V(proto,                25)  \
        V(fn_symbol,            25)  \
        V(self,                 25)  \
        V(type_params,          25)  \
        V(params,               25)  \
        V(dflts,                25)  \
        V(constraints,          25)  \
        V(retained_constraints, 25)  \
        V(decorators,           25)  \
        V(functions,            25)  \
        V(param_symbols,        25)  \
        V(bound_symbols,        25)  \
        V(type_bounds,          25)  \
        V(body,                 25)  \
        V(class,                25)  \
        V(overload,             25)  \
        V(type_hints,           25)  \
        V(has_defer,            25)  \
        V(must_jit,             25)  \
        V(inert,                25)  \
        V(emit,                 25)  \
        V(star,                 25)  \
        V(clone,                25)  \
        V(ftype,                25)  \
        V(mtype,                25)  \
        V(ikwargs,              25)  \
        V(rest,                 25)  \
        V(t,                    25)  \
        V(function,             26)  \
        V(args,                 26)  \
        V(fconds,               26)  \
        V(kwargs,               26)  \
        V(fkwconds,             26)  \
        V(kws,                  26)  \
        V(dtmp,                 27)  \
        V(keys,                 27)  \
        V(values,               27)  \
        V(dconds,               27)  \
        V(dcompr,               27)  \
        V(dflt,                 27)  \
        V(container,            28)  \
        V(subscript,            28)  \
        V(slice,                29)  \
        V(object,               30)  \
        V(member,               30)  \
        V(method,               30)  \
        V(method_args,          30)  \
        V(mconds,               30)  \
        V(method_kwargs,        30)  \
        V(method_kws,           30)  \
        V(maybe,                30) 

#define TY_EXPR_KIDS                          \
        K( 5, statement, AK_STMT)              \
        K( 8, throw, AK_EXPR)                  \
        K( 9, operand, AK_EXPR)                \
        KM(10, template, stmts, AK_STMTS)      \
        KM(10, template, exprs, AK_EXPRS)      \
        KM(10, template, holes, AK_EXPRS)      \
        K(11, elements, AK_EXPRS)              \
        K(11, aconds, AK_EXPRS)                \
        K(11, compr, AK_COMPR)                 \
        KM(12, macro, m, AK_EXPR)              \
        KM(12, macro, e, AK_EXPR)              \
        KM(13, lit, lang, AK_EXPR)             \
        KM(14, with, defs, AK_STMTS)           \
        KM(14, with, block, AK_STMT)           \
        K(15, es, AK_EXPRS)                    \
        K(15, tconds, AK_EXPRS)                \
        K(16, cond, AK_EXPR)                   \
        K(16, then, AK_EXPR)                   \
        K(16, _else, AK_EXPR)                  \
        K(18, lang, AK_EXPR)                   \
        K(18, fmts, AK_EXPRS)                  \
        K(18, fmtfs, AK_EXPRS)                 \
        K(18, expressions, AK_EXPRS)           \
        K(20, tagged, AK_EXPR)                 \
        K(20, aliased, AK_EXPR)                \
        K(20, constraint, AK_EXPR)             \
        K(20, namespace, AK_EXPR)              \
        K(21, left, AK_EXPR)                   \
        K(21, right, AK_EXPR)                  \
        K(21, p_cond, AK_PARTS)                \
        K(21, sc, AK_EXPR)                     \
        K(22, target, AK_EXPR)                 \
        K(22, value, AK_EXPR)                  \
        KM(23, hole, expr, AK_EXPR)            \
        KM(23, hole, constraint, AK_EXPR)      \
        K(24, subject, AK_EXPR)                \
        K(24, patterns, AK_EXPRS)              \
        K(24, thens, AK_EXPRS)                 \
        K(25, return_type, AK_EXPR)            \
        K(25, parent, AK_EXPR)                 \
        K(25, type_params, AK_EXPRS)           \
        K(25, dflts, AK_EXPRS)                 \
        K(25, constraints, AK_EXPRS)           \
        K(25, retained_constraints, AK_EXPRS)  \
        K(25, decorators, AK_EXPRS)            \
        K(25, functions, AK_EXPRS)             \
        K(25, body, AK_STMT)                   \
        K(25, overload, AK_EXPR)               \
        K(26, function, AK_EXPR)               \
        K(26, args, AK_EXPRS)                  \
        K(26, fconds, AK_EXPRS)                \
        K(26, kwargs, AK_EXPRS)                \
        K(26, fkwconds, AK_EXPRS)              \
        K(27, keys, AK_EXPRS)                  \
        K(27, values, AK_EXPRS)                \
        K(27, dconds, AK_EXPRS)                \
        K(27, dcompr, AK_COMPR)                \
        K(27, dflt, AK_EXPR)                   \
        K(28, container, AK_EXPR)              \
        K(28, subscript, AK_EXPR)              \
        KM(29, slice, e, AK_EXPR)              \
        KM(29, slice, i, AK_EXPR)              \
        KM(29, slice, j, AK_EXPR)              \
        KM(29, slice, k, AK_EXPR)              \
        K(30, object, AK_EXPR)                 \
        K(30, member, AK_EXPR)                 \
        K(30, method, AK_EXPR)                 \
        K(30, method_args, AK_EXPRS)           \
        K(30, mconds, AK_EXPRS)                \
        K(30, method_kwargs, AK_EXPRS)        

#define TY_STMT_VIEWS     \
        V(expression,  0)  \
        V(depth,       0)  \
        V(statements,  1)  \
        V(ret,         2)  \
        V(exports,     3)  \
        V(drop,        4)  \
        V(import,      5)  \
        V(use,         6)  \
        V(tag,         7)  \
        V(class,       7)  \
        V(for_loop,    8)  \
        V(each,        9)  \
        V(try,        10)  \
        V(match,      11)  \
        V(_while,     12)  \
        V(_if,        13)  \
        V(target,     14)  \
        V(value,      14)  \
        V(doc,        14)  \
        V(pub,        14)  \
        V(cnst,       14)  \
        V(retry,      14) 

#define TY_STMT_KIDS                         \
        K( 0, expression, AK_EXPR)            \
        K( 1, statements, AK_STMTS)           \
        K( 2, ret, AK_EXPR)                   \
        KM( 7, tag, super, AK_EXPR)           \
        KM( 7, tag, traits, AK_EXPRS)         \
        KM( 7, tag, methods, AK_EXPRS)        \
        KM( 7, tag, getters, AK_EXPRS)        \
        KM( 7, tag, setters, AK_EXPRS)        \
        KM( 7, tag, fields, AK_EXPRS)         \
        KM( 7, tag, s_methods, AK_EXPRS)      \
        KM( 7, tag, s_getters, AK_EXPRS)      \
        KM( 7, tag, s_setters, AK_EXPRS)      \
        KM( 7, tag, s_fields, AK_EXPRS)       \
        KM( 7, tag, members, AK_EXPRS)        \
        KM( 7, tag, type, AK_EXPR)            \
        KM( 7, tag, type_params, AK_EXPRS)    \
        KM( 7, tag, tfn, AK_STMT)             \
        KM( 7, class, super, AK_EXPR)         \
        KM( 7, class, traits, AK_EXPRS)       \
        KM( 7, class, methods, AK_EXPRS)      \
        KM( 7, class, getters, AK_EXPRS)      \
        KM( 7, class, setters, AK_EXPRS)      \
        KM( 7, class, fields, AK_EXPRS)       \
        KM( 7, class, s_methods, AK_EXPRS)    \
        KM( 7, class, s_getters, AK_EXPRS)    \
        KM( 7, class, s_setters, AK_EXPRS)    \
        KM( 7, class, s_fields, AK_EXPRS)     \
        KM( 7, class, members, AK_EXPRS)      \
        KM( 7, class, type, AK_EXPR)          \
        KM( 7, class, type_params, AK_EXPRS)  \
        KM( 7, class, tfn, AK_STMT)           \
        KM( 8, for_loop, init, AK_STMT)       \
        KM( 8, for_loop, cond, AK_EXPR)       \
        KM( 8, for_loop, next, AK_EXPR)       \
        KM( 8, for_loop, body, AK_STMT)       \
        KM( 9, each, target, AK_EXPR)         \
        KM( 9, each, array, AK_EXPR)          \
        KM( 9, each, a, AK_EXPR)              \
        KM( 9, each, b, AK_EXPR)              \
        KM( 9, each, body, AK_STMT)           \
        KM( 9, each, _if, AK_EXPR)            \
        KM( 9, each, _while, AK_EXPR)         \
        KM(10, try, s, AK_STMT)               \
        KM(10, try, patterns, AK_EXPRS)       \
        KM(10, try, handlers, AK_STMTS)       \
        KM(10, try, finally, AK_STMT)         \
        KM(11, match, e, AK_EXPR)             \
        KM(11, match, patterns, AK_EXPRS)     \
        KM(11, match, conds, AK_EXPRS)        \
        KM(11, match, statements, AK_STMTS)   \
        KM(12, _while, parts, AK_PARTS)       \
        KM(12, _while, block, AK_STMT)        \
        KM(13, _if, parts, AK_PARTS)          \
        KM(13, _if, then, AK_STMT)            \
        KM(13, _if, _else, AK_STMT)           \
        K(14, target, AK_EXPR)                \
        K(14, value, AK_EXPR)                

#define X(f, T, s, b) char f[(s) * sizeof (u64) + (b) + sizeof (T)];
typedef union { TY_EXPR_FIELDS } AstExprExtent;
typedef union { TY_STMT_FIELDS } AstStmtExtent;
#undef X

enum {
        AST_EXPR_SLOTS = (sizeof (AstExprExtent) + sizeof (u64) - 1) / sizeof (u64),
        AST_STMT_SLOTS = (sizeof (AstStmtExtent) + sizeof (u64) - 1) / sizeof (u64)
};

struct expression {
        void *arena;
        Expr *origin;

        u8 type;
        u8 dbg;
        u8 synth;
        u8 cap;

        Location start;
        Location end;
        Module *mod;
        Expr *xfunc;
        Scope *xscope;
        T2Type _type;

        bool annotated;
        bool has_resources;
        bool bang;
        u8 shared;

        u64 k[AST_EXPR_SLOTS];
};

struct statement {
        void *arena;
        Expr *origin;

        u8 type;
        u8 dbg;
        u8 synth;
        u8 cap;

        Location start;
        Location end;
        Module *mod;
        Expr *xfunc;
        Scope *xscope;
        T2Type _type;

        i32 when;
        bool will_return;
        u8 shared;
        Namespace *ns;

        u64 ks[AST_STMT_SLOTS];
};

#define X(f, T, s, b) typedef T AstXT_##f; enum { AstXO_##f = (s) * sizeof (u64) + (b) };
TY_EXPR_FIELDS
#undef X

#define X(f, T, s, b) typedef T AstST_##f; enum { AstSO_##f = (s) * sizeof (u64) + (b) };
TY_STMT_FIELDS
#undef X

#define X(f, T, s, b) _Static_assert(AstXO_##f % _Alignof (T) == 0, "misaligned Expr field " #f);
TY_EXPR_FIELDS
#undef X

#define X(f, T, s, b) _Static_assert(AstSO_##f % _Alignof (T) == 0, "misaligned Stmt field " #f);
TY_STMT_FIELDS
#undef X

#define V(f, v) enum { AstXV_##f = (v) };
TY_EXPR_VIEWS
#undef V

#define V(f, v) enum { AstSV_##f = (v) };
TY_STMT_VIEWS
#undef V

enum {
        AK_EXPR,
        AK_STMT,
        AK_EXPRS,
        AK_STMTS,
        AK_PARTS,
        AK_COMPR
};

enum {
        AST_MAX_KIDS = 24
};

typedef struct {
        u8  how;
        u8  view;
        u16 off;
} AstKid;

extern u8     AstKidCount[256];
extern AstKid AstKidTable[256][AST_MAX_KIDS];

enum {
        AST_SHARED = 1 << 0,
        AST_COPIED = 1 << 1
};

inline static u8 *
AstShared(void const *node)
{
        Expr const *e = node;

        return (e->type > STATEMENT_TYPE_START) ? &((Stmt *)node)->shared
             :                                     &((Expr *)node)->shared;
}

void
AstKidsInit(void);

void
AstEachKid(void *node, void (*f)(void **slot, void *ctx), void *ctx);

void *
AstSlotFault(void const *node, usize off, usize n);

inline static void *
AstXChk(u64 const *k, usize off, usize n)
{
        Expr const *e = (Expr const *)((char const *)k - offsetof(Expr, k));

        if (UNLIKELY(e->cap != 0 && off + n > e->cap * sizeof (u64))) {
                return AstSlotFault(e, off, n);
        }

        return (char *)k + off;
}

inline static void *
AstSChk(u64 const *k, usize off, usize n)
{
        Stmt const *s = (Stmt const *)((char const *)k - offsetof(Stmt, ks));

        if (UNLIKELY(s->cap != 0 && off + n > s->cap * sizeof (u64))) {
                return AstSlotFault(s, off, n);
        }

        return (char *)k + off;
}

#if defined(TY_RELEASE)
 #define xF(e, f) (*(AstXT_##f *)((char *)(e)->k + AstXO_##f))
 #define sF(s, f) (*(AstST_##f *)((char *)(s)->ks + AstSO_##f))
#else
 #define xF(e, f) (*(AstXT_##f *)AstXChk((e)->k, AstXO_##f, sizeof (AstXT_##f)))
 #define sF(s, f) (*(AstST_##f *)AstSChk((s)->ks, AstSO_##f, sizeof (AstST_##f)))
#endif

inline static bool
IsStmt(Expr const *expr)
{
        return (expr->type > STATEMENT_TYPE_START);
}

enum {
        AST_EXPR_HDR   = offsetof(Expr, k),
        AST_STMT_HDR   = offsetof(Stmt, ks),
        AST_EXPR_FLOOR = (AstXO_local + sizeof (AstXT_local) + sizeof (u64) - 1) / sizeof (u64)
};

extern u8 const AstSlots[256];

inline static usize
AstHdr(int type)
{
        return (type > STATEMENT_TYPE_START) ? AST_STMT_HDR : AST_EXPR_HDR;
}

inline static u32
AstFull(int type)
{
        return (type > STATEMENT_TYPE_START) ? AST_STMT_SLOTS : AST_EXPR_SLOTS;
}

inline static u32
AstNeed(int type)
{
        return (AstSlots[type] == 0)            ? AstFull(type)
             : (type > STATEMENT_TYPE_START)    ? AstSlots[type]
             : (AstSlots[type] < AST_EXPR_FLOOR) ? AST_EXPR_FLOOR
             :                                    AstSlots[type];
}

inline static u32
AstGrow(int type)
{
        return (type == EXPRESSION_FUNCTION_CALL) ? AstFull(type) : AstNeed(type);
}

inline static u32
AstCap(Expr const *e)
{
        return (e->cap == 0) ? AstFull(e->type) : e->cap;
}

inline static usize
AstBytes(int type, u32 slots)
{
        return AstHdr(type) + slots * sizeof (u64);
}

#define AstNew(t)      ((AstNew)(ty, (t), AstGrow(t)))
#define AstRelease(e)  ((AstRelease)(ty, (e)))
#define AstNewFull(t)  ((AstNew)(ty, (t), AstFull(t)))
#define AstClone(e)    ((__typeof__(e))(AstClone)(ty, (Expr const *)(e), -1))
#define AstCloneAs(e, t) ((AstClone)(ty, (Expr const *)(e), (t)))
#define AstReplace(d, s) ((AstReplace)((Expr *)(d), (Expr const *)(s), 0))
#define ZERO_EXPR(e)     ((AstZero)((Expr *)(e)))
#define COPY_EXPR(d, s)  ((AstReplace)((Expr *)(d), (Expr const *)(s), offsetof(Expr, has_resources) + 1))

inline static Expr
AstValue(Expr const *e)
{
        Expr x = {0};

        memcpy(&x, e, AstBytes(e->type, min(AstCap(e), AST_EXPR_SLOTS)));
        x.cap = 0;

        *AstShared(e) |= AST_COPIED;
        *AstShared(&x) |= AST_COPIED;

        return x;
}

void *
(AstNew)(Ty *ty, int type, u32 slots);

void
(AstRelease)(Ty *ty, void *node);

Expr *
(AstClone)(Ty *ty, Expr const *e, int type);

void
(AstReplace)(Expr *dst, Expr const *src, usize from);

void
(AstZero)(Expr *e);

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
                        e = (Expr *)xF(e, statement);
                        break;

                case STATEMENT_EXPRESSION:
                        e = sF(((Stmt *)e), expression);
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
                return HasBody(sF(((Stmt *)fun), value));

        case EXPRESSION_FUNCTION:
                return (xF(fun, body) != NULL);

        case EXPRESSION_MULTI_FUNCTION:
                for (int i = 0; i < vN(xF(fun, functions)); ++i) {
                        if (HasBody(v__(xF(fun, functions), i))) {
                                return true;
                        }
                }
                return false;
        }

        return false;
}

inline static bool
is_method(Expr const *e) { return xF(e, class) != NULL; }

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
