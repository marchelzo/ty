#include <setjmp.h>
#include <stdarg.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>
#include <errno.h>
#include <math.h>
#include <stdnoreturn.h>

#include "vec.h"
#include "token.h"
#include "test.h"
#include "ast.h"
#include "util.h"
#include "alloc.h"
#include "lex.h"
#include "operators.h"
#include "value.h"
#include "table.h"
#include "log.h"
#include "vm.h"

#define BINARY_OPERATOR(name, token, prec, right_assoc) \
        static struct expression * \
        infix_ ## name(struct expression *left) \
        { \
                consume(TOKEN_ ## token); \
                struct expression *e = mkexpr(); \
                e->type = EXPRESSION_ ## token; \
                e->left = left; \
                e->right = parse_expr(prec - (right_assoc ? 1 : 0)); \
                return e; \
        } \

#define BINARY_LVALUE_OPERATOR(name, token, prec, right_assoc) \
        static struct expression * \
        infix_ ## name(struct expression *left) \
        { \
                consume(TOKEN_ ## token); \
                struct expression *e = mkexpr(); \
                e->type = EXPRESSION_ ## token; \
                e->target = assignment_lvalue(left); \
                e->value = parse_expr(prec - (right_assoc ? 1 : 0)); \
                return e; \
        } \

#define PREFIX_OPERATOR(name, token, prec) \
        static struct expression * \
        prefix_ ## name(void) \
        { \
                consume(TOKEN_ ## token); \
                struct expression *e = mkexpr(); \
                e->type = EXPRESSION_PREFIX_ ## token; \
                e->operand = parse_expr(prec); \
                return e; \
        } \

#define PREFIX_LVALUE_OPERATOR(name, token, prec) \
        static struct expression * \
        prefix_ ## name(void) \
        { \
                consume(TOKEN_ ## token); \
                struct expression *e = mkexpr(); \
                e->type = EXPRESSION_PREFIX_ ## token; \
                e->operand = assignment_lvalue(parse_expr(prec)); \
                return e; \
        } \

typedef struct expression *parse_fn();

enum {
        MAX_ERR_LEN  = 2048
};

/*
 * Meaningful names for different contexts in which we can parse lvalues.
 *
 * In a let declaration, the lvalue must be '='.
 * In a for-each loop, it must be followed by 'in'.
 *
 * Passing these values to parse_definition_lvalue determines its behaviour.
 */
enum {
        LV_LET,
        LV_EACH,
        LV_SUB,
        LV_ANY
};

static jmp_buf jb;
static char errbuf[MAX_ERR_LEN + 1];

static struct table uops;
static vec(struct token) tokens;
static int tokidx = 0;
enum lex_context lex_ctx = LEX_PREFIX;

static struct location loc;
static int depth;
static bool NoEquals = false;

typedef vec(char *) param_list;
static param_list pnames;

static char const *filename;

static struct statement BREAK_STATEMENT    = { .type = STATEMENT_BREAK,    .loc = {42, 42}  };
static struct statement CONTINUE_STATEMENT = { .type = STATEMENT_CONTINUE, .loc = {42, 42}  };
static struct statement NULL_STATEMENT     = { .type = STATEMENT_NULL,     .loc = {42, 42}  };

static struct statement *
parse_statement(void);

static struct expression *
parse_expr(int);

static struct statement *
parse_match_statement(void);

static struct statement *
parse_let_definition(void);

static struct expression *
parse_target_list(void);

static struct statement *
parse_block(void);

static struct expression *
assignment_lvalue(struct expression *e);

static struct expression *
definition_lvalue(struct expression *e);

static struct expression *
infix_member_access(struct expression *e);

static struct expression *
prefix_parenthesis(void);

inline static struct token *
tok(void);

char *
mksym(int s)
{
        char b[32];

        snprintf(b, sizeof b - 1, ":%d", s);
        return sclone(b);
}

/*
 * Get a unique identifier name.
 * This sucks.
 */
char *
gensym(void)
{
        static int sym = 0;
        return mksym(sym++);
}

inline static struct expression *
mkexpr(void)
{
        struct expression *e = alloc(sizeof *e);
        e->loc = loc;
        return e;
}

inline static struct statement *
mkstmt(void)
{
        struct statement *s = alloc(sizeof *s);
        s->loc = loc;
        return s;
}

inline static struct statement *
mkret(struct expression *value)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);
        vec_push(s->returns, value);
        return s;
}

inline static struct statement *
mkdef(struct expression *lvalue, char *name)
{
        struct expression *value = mkexpr();
        value->type = EXPRESSION_IDENTIFIER;
        value->identifier = name;
        value->module = NULL;

        struct statement *s = mkstmt();
        s->type = STATEMENT_DEFINITION;
        s->target = lvalue;
        s->value = value;

        return s;
}

noreturn static void
error(char const *fmt, ...)
{
        if (fmt == NULL) {
                strcpy(errbuf, lex_error());
        } else {
                va_list ap;
                va_start(ap, fmt);

                int n = 0;

                char *err = errbuf;
                n += sprintf(err, "ParseError: %s:%d:%d: ", filename, tok()->loc.line + 1, tok()->loc.col + 1);
                vsnprintf(err + n, MAX_ERR_LEN - n, fmt, ap);

                va_end(ap);
        }

        LOG("Parse Error: %s", errbuf);

        longjmp(jb, 1);
}

inline static void
skip(int n)
{
        tokidx += n;
}

inline static void
next(void)
{
        skip(1);
}

inline static struct token *
token(int i)
{
        struct token t;
        while (tokens.count <= i + tokidx) {
                t = lex_token(lex_ctx);
                if (t.type == TOKEN_ERROR) {
                        error(NULL);
                }
                vec_push(tokens, t);
        }

        loc = tokens.items[tokidx + i].loc;
        return &tokens.items[tokidx + i];
}

inline static struct token *
tok(void)
{
        return token(0);
}

/*
 * Push a token into the token stream, so that it will be returned by the next call
 * to tok().
 */
inline static void
unconsume(int type)
{
        vec_insert(
                tokens,
                ((struct token){
                        .type = type,
                        .loc = loc
                }),
                tokidx
        );
}

static void
expect(int type)
{
        if (tok()->type != type) {
                error("expected %s but found %s", token_show_type(type), token_show(tok()));
        }
}


static void
expect_keyword(int type)
{
        if (tok()->type != TOKEN_KEYWORD || tok()->keyword != type) {
                error("expected %s but found %s", token_show(&(struct token){ .type = TOKEN_KEYWORD, .keyword = type }), token_show(tok()));
        }
}

inline static void
consume(int type)
{
        expect(type);
        tokidx += 1;
}

inline static void
consume_keyword(int type)
{
        expect_keyword(type);
        tokidx += 1;

}

/* * * * | prefix parsers | * * * */
static struct expression *
prefix_integer(void)
{
        expect(TOKEN_INTEGER);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_INTEGER;
        e->integer = tok()->integer;

        consume(TOKEN_INTEGER);

        return e;
}

static struct expression *
prefix_real(void)
{
        expect(TOKEN_REAL);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_REAL;
        e->real = tok()->real;

        consume(TOKEN_REAL);

        return e;
}

static struct expression *
prefix_string(void)
{
        expect(TOKEN_STRING);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_STRING;
        e->string = tok()->string;

        consume(TOKEN_STRING);

        return e;
}

static struct expression *
prefix_special_string(void)
{
        expect(TOKEN_SPECIAL_STRING);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_SPECIAL_STRING;
        vec_init(e->expressions);
        
        e->strings.items = tok()->strings.items;
        e->strings.count = tok()->strings.count;

        char **exprs = tok()->expressions.items;
        int count = tok()->expressions.count;

        struct location *locs = tok()->locations.items;

        consume(TOKEN_SPECIAL_STRING);

        for (int i = 0; i < count; ++i) {
                lex_start(exprs[i]);
                vec_push(e->expressions, parse_expr(0));
                if (tok()->type != TOKEN_END) {
                        /*
                         * This results in a more accurate location in the error message.
                         */
                        tok()->loc = locs[i];
                        error("expression in interpolated string has trailing tokens: %s", exprs[i]);
                }
                consume(TOKEN_END);
                lex_end();
        }

        return e;
}

static struct expression *
prefix_hash(void)
{
        consume('#');

        struct expression *e = mkexpr();
        e->type = EXPRESSION_PREFIX_HASH;
        e->operand = parse_expr(10);

        return e;
}

static struct expression *
prefix_dollar(void)
{
        consume('$');
        lex_ctx = LEX_INFIX;

        struct expression *e = mkexpr();

        if (tok()->type == TOKEN_IDENTIFIER) {
                e->type = EXPRESSION_MATCH_NOT_NIL;
                e->identifier = tok()->identifier;
                e->module = tok()->module;

                if (e->module != NULL)
                        error("unpexpected module in lvalue");

                consume(TOKEN_IDENTIFIER);
        } else {
                int i = 1;
                if (tok()->type == TOKEN_INTEGER) {
                        i = tok()->integer;
                        next();
                }
                if (i < 1) {
                        error("invalid implicit parameter index: $%d", i);
                }
                while (pnames.count < i) {
                        vec_push(pnames, gensym());
                }
                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = pnames.items[i - 1];
                e->module = NULL;
        }

        return e;
}

static struct expression *
prefix_identifier(void)
{
        expect(TOKEN_IDENTIFIER);

        struct expression *e = mkexpr();

        e->type = EXPRESSION_IDENTIFIER;
        e->identifier = tok()->identifier;
        e->module = tok()->module;

        consume(TOKEN_IDENTIFIER);

        return e;
}

static struct expression *
prefix_function(void)
{
        consume_keyword(KEYWORD_FUNCTION);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_FUNCTION;
        e->rest = false;
        vec_init(e->params);

        if (tok()->type == TOKEN_IDENTIFIER) {
                e->name = tok()->identifier;
                next();
        } else {
                e->name = NULL;
        }

        consume('(');

        while (tok()->type != ')') {
                bool rest = false;
                if (tok()->type == TOKEN_STAR) {
                        rest = true;
                        next();
                }

                expect(TOKEN_IDENTIFIER);
                vec_push(e->params, sclone(tok()->identifier));
                next();

                if (rest) {
                        e->params.count -= 1;
                        e->rest = 1;
                        expect(')');
                } else if (tok()->type == ',') {
                        next();
                }
        }

        consume(')');

        e->body = parse_statement();

        return e;
}

/* rewrite [ op ] as ((a, b) -> a op b) */
static struct expression *
opfunc(void)
{
        struct token t = *tok();
        next();

        consume(']');

        char *a = gensym();
        char *b = gensym();

        unconsume(')');

        unconsume(TOKEN_IDENTIFIER);
        tok()->module = NULL;
        tok()->identifier = b;

        unconsume(TOKEN_USER_OP);
        *tok() = t;

        unconsume(TOKEN_IDENTIFIER);
        tok()->module = NULL;
        tok()->identifier = a;

        unconsume(TOKEN_ARROW);

        unconsume(')');

        unconsume(TOKEN_IDENTIFIER);
        tok()->module = NULL;
        tok()->identifier = b;

        unconsume(',');

        unconsume(TOKEN_IDENTIFIER);
        tok()->module = NULL;
        tok()->identifier = a;

        unconsume('(');
        unconsume('(');

        struct expression *e = parse_expr(0);

        return e;
}

static struct expression *
prefix_star(void)
{
        consume(TOKEN_STAR);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_MATCH_REST;

        expect(TOKEN_IDENTIFIER);
        e->identifier = tok()->identifier;
        if (tok()->module != NULL)
                error("unexpected module qualifier in lvalue");

        consume(TOKEN_IDENTIFIER);

        return e;
}

static struct expression *
prefix_match(void)
{
        consume_keyword(KEYWORD_MATCH);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_MATCH;

        e->subject = parse_expr(-1);

        consume('{');

        vec_init(e->patterns);
        vec_init(e->conds);
        vec_init(e->thens);

        vec_push(e->patterns, parse_expr(-1));
        if (tok()->type == TOKEN_BIT_OR) {
                next();
                vec_push(e->conds, parse_expr(0));
        } else {
                vec_push(e->conds, NULL);
        }

        consume(TOKEN_FAT_ARROW);
        vec_push(e->thens, parse_expr(0));

        while (tok()->type == ',') {
                next();
                vec_push(e->patterns, parse_expr(-1));
                if (tok()->type == TOKEN_BIT_OR) {
                        next();
                        vec_push(e->conds, parse_expr(0));
                } else {
                        vec_push(e->conds, NULL);
                }

                consume(TOKEN_FAT_ARROW);
                vec_push(e->thens, parse_expr(0));
        }

        consume('}');

        return e;
}

static struct expression *
prefix_parenthesis(void)
{
        /*
         * This can either be a plain old parenthesized expression, e.g., (4 + 4)
         * or it can be an identifier list for an arrow function, e.g., (a, b, c).
         */

        consume('(');

        /*
         * () is an empty identifier list.
         */
        if (tok()->type == ')') {
                next();
                struct expression *list = mkexpr();
                list->type = EXPRESSION_LIST;
                list->only_identifiers = true;
                vec_init(list->es);
                return list;
        }

        struct expression *e = parse_expr(0);

        if (tok()->type == ',') {
                struct expression *list = mkexpr();
                list->only_identifiers = true;

                /*
                 * It _must_ be an identifier list.
                 */
                if (e->type != EXPRESSION_IDENTIFIER && e->type != EXPRESSION_MATCH_REST) {
                        list->only_identifiers = false;
                }

                list->type = EXPRESSION_LIST;
                vec_init(list->es);
                vec_push(list->es, e);

                while (tok()->type == ',') {
                        next();
                        struct expression *e = parse_expr(0);
                        if (e->type == EXPRESSION_MATCH_REST) {
                                expect(')');
                        } else if (e->type != EXPRESSION_IDENTIFIER) {
                                list->only_identifiers = false;
                        }
                        vec_push(list->es, e);
                }

                consume(')');

                return list;
        } else {
                consume(')');
                return e;
        }
}

static struct expression *
prefix_true(void)
{
        consume_keyword(KEYWORD_TRUE);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_BOOLEAN;
        e->boolean = true;

        return e;
}

static struct expression *
prefix_false(void)
{
        consume_keyword(KEYWORD_FALSE);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_BOOLEAN;
        e->boolean = false;

        return e;
}

static struct expression *
prefix_nil(void)
{
        consume_keyword(KEYWORD_NIL);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_NIL;

        return e;
}

static struct expression *
prefix_regex(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_REGEX;
        e->regex = tok()->regex;
        e->extra = tok()->extra;
        e->pattern = tok()->pattern;

        consume(TOKEN_REGEX);

        return e;
}


static struct expression *
prefix_array(void)
{
        consume('[');

        struct lex_state ls;
        lex_save(&ls);

        lex_ctx = LEX_INFIX;
        if (token(1)->type == ']') switch (tok()->type) {
        case TOKEN_USER_OP:
        case TOKEN_PERCENT:
        case TOKEN_PLUS:
        case TOKEN_MINUS:
        case TOKEN_STAR:
        case TOKEN_DIV:
        case TOKEN_CMP:
        case TOKEN_AND:
        case TOKEN_OR:
        case TOKEN_WTF:
        case TOKEN_DOT_DOT:
        case TOKEN_DOT_DOT_DOT:
        case TOKEN_LT:
        case TOKEN_GT:
        case TOKEN_LEQ:
        case TOKEN_GEQ:
        case TOKEN_NOT_EQ:
        case TOKEN_DBL_EQ:
                return opfunc();
        default: break;
        }

        skip(2);
        lex_rewind(&ls);

        lex_ctx = LEX_PREFIX;

        struct expression *e = mkexpr();
        e->type = EXPRESSION_ARRAY;
        vec_init(e->elements);

        while (tok()->type != ']') {
                vec_push(e->elements, parse_expr(0));

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_FOR) {
                        next();
                        e->type = EXPRESSION_ARRAY_COMPR;
                        e->compr.pattern = parse_target_list();
                        consume_keyword(KEYWORD_IN);
                        e->compr.iter = parse_expr(0);
                        if (tok()->type == TOKEN_BIT_OR) {
                                next();
                                e->compr.cond = parse_expr(0);
                        } else {
                                e->compr.cond = NULL;
                        }
                        expect(']');
                } else if (tok()->type == ',') {
                        next();
                } else {
                        expect(']');
                }
        }

        next();

        return e;
}

static struct expression *
prefix_tick(void)
{
        consume('`');

        expect(TOKEN_IDENTIFIER);

        if (tok()->module != NULL)
                error("unexpected module qualifier in ` pattern");

        struct expression *e = mkexpr();

        e->type = EXPRESSION_TICK;
        e->identifier = tok()->identifier;
        e->module = NULL;

        next();

        return e;
}

static struct expression *
prefix_incrange(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_DOT_DOT_DOT;

        struct expression *zero = mkexpr();
        zero->type = EXPRESSION_INTEGER;
        zero->integer = 0;

        consume(TOKEN_DOT_DOT_DOT);

        e->left = zero;
        e->right = parse_expr(0);

        return e;
}

static struct expression *
prefix_range(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_DOT_DOT;

        struct expression *zero = mkexpr();
        zero->type = EXPRESSION_INTEGER;
        zero->integer = 0;

        consume(TOKEN_DOT_DOT);

        e->left = zero;
        e->right = parse_expr(0);

        return e;
}

static struct expression *
prefix_implicit_method(void)
{
        consume(TOKEN_BIT_AND);

        bool maybe = false;
        if (tok()->type == TOKEN_QUESTION) {
                next();
                maybe = true;
        }

        expect(TOKEN_IDENTIFIER);

        struct expression *o = mkexpr();
        o->type = EXPRESSION_IDENTIFIER;
        o->identifier = gensym();
        o->module = NULL;

        struct expression *e = mkexpr();
        e->type = EXPRESSION_METHOD_CALL;
        e->maybe = maybe;
        e->object = o;
        e->method_name = tok()->identifier;
        vec_init(e->method_args);

        next();

        if (tok()->type == '(') {
                next();

                lex_ctx = LEX_PREFIX;

                if (tok()->type == ')') {
                        next();
                        return e;
                } else {
                        vec_push(e->method_args, parse_expr(0));
                }

                while (tok()->type == ',') {
                        next();
                        vec_push(e->method_args, parse_expr(0));
                }

                consume(')');
        }

        struct expression *f = mkexpr();
        f->type = EXPRESSION_FUNCTION;
        f->rest = false;
        f->name = NULL;
        f->body = mkret(e);

        vec_init(f->params);
        vec_push(f->params, o->identifier);

        return f;
}

static struct expression *
prefix_implicit_lambda(void)
{
        param_list pnames_save = pnames;
        vec_init(pnames);

        next();

        unconsume(TOKEN_ARROW);
        unconsume(')');
        unconsume('(');

        struct expression *f = parse_expr(0);

        for (int i = 0; i < pnames.count; ++i) {
                vec_push(f->params, pnames.items[i]);
        }

        vec_empty(pnames);
        pnames = pnames_save;

        consume(TOKEN_BIT_OR);

        return f;
}

static struct expression *
prefix_arrow(void)
{
        param_list pnames_save = pnames;
        vec_init(pnames);

        unconsume(')');
        unconsume('(');

        struct expression *f = parse_expr(0);

        for (int i = 0; i < pnames.count; ++i) {
                vec_push(f->params, pnames.items[i]);
        }

        vec_empty(pnames);
        pnames = pnames_save;

        return f;
}

static struct expression *
prefix_object(void)
{
        consume('{');

        struct expression *e = mkexpr();
        e->type = EXPRESSION_DICT;
        e->dflt = NULL;

        vec_init(e->keys);
        vec_init(e->values);

        while (tok()->type != '}') {
                if (tok()->type == TOKEN_STAR && token(1)->type == ':') {
                        next();
                        next();
                        unconsume(TOKEN_ARROW);
                        e->dflt = parse_expr(0);
                } else {
                        vec_push(e->keys, parse_expr(0));
                        if (tok()->type == ':') {
                                next();
                                vec_push(e->values, parse_expr(0));
                        } else {
                                vec_push(e->values, NULL);
                        }
                }

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_FOR) {
                        next();
                        e->type = EXPRESSION_DICT_COMPR;
                        e->dcompr.pattern = parse_target_list();
                        consume_keyword(KEYWORD_IN);
                        e->dcompr.iter = parse_expr(0);
                        if (tok()->type == TOKEN_BIT_OR) {
                                next();
                                e->dcompr.cond = parse_expr(0);
                        } else {
                                e->dcompr.cond = NULL;
                        }
                        expect('}');
                } else if (tok()->type == ',') {
                        next();
                } else {
                        expect('}');
                }
        }

        next();

        return e;
}

PREFIX_OPERATOR(at,     AT,       9)
PREFIX_OPERATOR(minus,  MINUS,    9)
PREFIX_OPERATOR(bang,   BANG,     10)
PREFIX_OPERATOR(is_nil, QUESTION, 10)

PREFIX_LVALUE_OPERATOR(inc,   INC,   9)
PREFIX_LVALUE_OPERATOR(dec,   DEC,   9)
/* * * * | end of prefix parsers | * * * */

/* * * * | infix parsers | * * * */
static struct expression *
infix_function_call(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_FUNCTION_CALL;
        e->function = left;
        vec_init(e->args);

        consume('(');

        lex_ctx = LEX_PREFIX;

        if (tok()->type == ')') {
                next();
                return e;
        } else {
                vec_push(e->args, parse_expr(0));
        }

        while (tok()->type == ',') {
                next();
                vec_push(e->args, parse_expr(0));
        }

        consume(')');

        return e;
}

static struct expression *
infix_eq(struct expression *left)
{
        struct expression *e = mkexpr();

        e->type = tok()->type == TOKEN_EQ ? EXPRESSION_EQ : EXPRESSION_MAYBE_EQ;
        next();

        e->target = assignment_lvalue(left);
        if (left->type == EXPRESSION_LIST) {
                e->value = parse_expr(-1);
        } else {
                e->value = parse_expr(1);
        }

        return e;
}

static struct expression *
prefix_user_op(struct expression *e)
{
        error("not implemented");
}

static struct expression *
infix_user_op(struct expression *left)
{
        struct expression *e = mkexpr();

        e->type = EXPRESSION_METHOD_CALL;
        e->maybe = false;
        e->object = left;
        e->method_name = tok()->identifier;
        consume(TOKEN_USER_OP);
        vec_init(e->method_args);

        int prec = 8;

        struct value *p = table_look(&uops, e->method_name);
        if (p != NULL) {
                prec = (p->integer > 0) ? p->integer : abs(p->integer) - 1;
        }

        vec_push(e->method_args, parse_expr(prec));

        return e;
}

static struct expression *
infix_list(struct expression *left)
{

        struct expression *e = mkexpr();
        e->type = EXPRESSION_LIST;
        vec_init(e->es);
        vec_push(e->es, left);

        NoEquals = true;

        while (tok()->type == ',') {
                next();
                vec_push(e->es, parse_expr(1));
        }

        NoEquals = false;

        return e;
}

static struct expression *
infix_subscript(struct expression *left)
{
        consume('[');
        
        struct expression *e = mkexpr();
        e->type = EXPRESSION_SUBSCRIPT;
        e->container = left;
        e->subscript = parse_expr(0);

        consume(']');

        return e;
}

static struct expression *
infix_member_access(struct expression *left)
{
        struct expression *e = mkexpr();
        e->object = left;

        e->maybe = tok()->type == TOKEN_DOT_MAYBE;
        next();

        expect(TOKEN_IDENTIFIER);

        if (token(1)->type != '(') {
                e->type = EXPRESSION_MEMBER_ACCESS;
                e->member_name = sclone(tok()->identifier);
                consume(TOKEN_IDENTIFIER);
                return e;
        }

        e->type = EXPRESSION_METHOD_CALL;
        e->method_name = sclone(tok()->identifier);
        consume(TOKEN_IDENTIFIER);
        vec_init(e->method_args);

        consume('(');

        lex_ctx = LEX_PREFIX;

        if (tok()->type == ')')
                goto End;
        else
                vec_push(e->method_args, parse_expr(0));

        while (tok()->type == ',') {
                next();
                vec_push(e->method_args, parse_expr(0));
        }

End:
        consume(')');
        return e;
}

static struct expression *
infix_squiggly_arrow(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_VIEW_PATTERN;

        consume(TOKEN_SQUIGGLY_ARROW);

        e->left = left;
        e->right = parse_expr(0);

        return e;
}

static struct expression *
infix_arrow_function(struct expression *left)
{

        consume(TOKEN_ARROW);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_FUNCTION;
        e->rest = false;
        e->name = NULL;
        vec_init(e->params);

        if (left->type != EXPRESSION_LIST) {
                struct expression *l = mkexpr();
                l->type = EXPRESSION_LIST;
                vec_init(l->es);
                vec_push(l->es, left);
                left = l;
        }

        struct statement *body = mkstmt();
        body->type = STATEMENT_BLOCK;
        vec_init(body->statements);

        for (int i = 0; i < left->es.count; ++i) {
                struct expression *p = left->es.items[i];
                if (p->type == EXPRESSION_IDENTIFIER) {
                        vec_push(e->params, p->identifier);
                } else if (p->type == EXPRESSION_MATCH_REST) {
                        vec_push(e->params, p->identifier);
                        e->params.count -= 1;
                        e->rest = true;
                } else {
                        char *name = gensym();
                        vec_push(e->params, name);
                        vec_push(body->statements, mkdef(definition_lvalue(p), name));
                }
        }

        struct statement *ret = mkret(parse_expr(0));

        if (body->statements.count == 0) {
                free(body);
                e->body = ret;
        } else {
                vec_push(body->statements, ret);
                e->body = body;
        }

        return e;
}

static struct expression *
infix_conditional(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_CONDITIONAL;

        e->then = left;
        consume_keyword(KEYWORD_IF);
        e->cond = parse_expr(0);
        consume_keyword(KEYWORD_ELSE);
        e->otherwise = parse_expr(0);

        return e;
}

static struct expression *
postfix_inc(struct expression *left)
{
        struct expression *e = mkexpr();

        consume(TOKEN_INC);

        e->type = EXPRESSION_POSTFIX_INC;
        e->operand = assignment_lvalue(left);
        
        return e;
}

static struct expression *
postfix_dec(struct expression *left)
{
        struct expression *e = mkexpr();

        consume(TOKEN_DEC);

        e->type = EXPRESSION_POSTFIX_DEC;
        e->operand = assignment_lvalue(left);
        
        return e;
}

BINARY_OPERATOR(star,     STAR,        9, false)
BINARY_OPERATOR(div,      DIV,         9, false)
BINARY_OPERATOR(percent,  PERCENT,     9, false)

BINARY_OPERATOR(plus,     PLUS,        8, false)
BINARY_OPERATOR(minus,    MINUS,       8, false)

BINARY_OPERATOR(range,    DOT_DOT,     7, false)
BINARY_OPERATOR(incrange, DOT_DOT_DOT, 7, false)

BINARY_OPERATOR(lt,       LT,          7, false)
BINARY_OPERATOR(gt,       GT,          7, false)
BINARY_OPERATOR(geq,      GEQ,         7, false)
BINARY_OPERATOR(leq,      LEQ,         7, false)
BINARY_OPERATOR(cmp,      CMP,         7, false)

BINARY_OPERATOR(not_eq,   NOT_EQ,      6, false)
BINARY_OPERATOR(dbl_eq,   DBL_EQ,      6, false)

BINARY_OPERATOR(and,      AND,         5, false)

BINARY_OPERATOR(or,       OR,          4, false)
BINARY_OPERATOR(wtf,      WTF,         4, false)

BINARY_LVALUE_OPERATOR(plus_eq,  PLUS_EQ,  2, true)
BINARY_LVALUE_OPERATOR(star_eq,  STAR_EQ,  2, true)
BINARY_LVALUE_OPERATOR(div_eq,   DIV_EQ,   2, true)
BINARY_LVALUE_OPERATOR(minus_eq, MINUS_EQ, 2, true)
/* * * * | end of infix parsers | * * * */

static parse_fn *
get_prefix_parser(void)
{
        lex_ctx = LEX_PREFIX;

        switch (tok()->type) {
        case TOKEN_INTEGER:        return prefix_integer;
        case TOKEN_REAL:           return prefix_real;
        case TOKEN_STRING:         return prefix_string;
        case TOKEN_SPECIAL_STRING: return prefix_special_string;
        case TOKEN_REGEX:          return prefix_regex;

        case TOKEN_IDENTIFIER:     return prefix_identifier;
        case TOKEN_KEYWORD:        goto Keyword;

        case TOKEN_BIT_AND:        return prefix_implicit_method;
        case TOKEN_BIT_OR:         return prefix_implicit_lambda;
        case '#':                  return prefix_hash;

        case '(':                  return prefix_parenthesis;
        case '[':                  return prefix_array;
        case '{':                  return prefix_object;

        case '$':                  return prefix_dollar;
        case '`':                  return prefix_tick;
        
        case TOKEN_DOT_DOT:        return prefix_range;
        case TOKEN_DOT_DOT_DOT:    return prefix_incrange;

        case TOKEN_QUESTION:       return prefix_is_nil;
        case TOKEN_BANG:           return prefix_bang;
        case TOKEN_AT:             return prefix_at;
        case TOKEN_MINUS:          return prefix_minus;
        case TOKEN_INC:            return prefix_inc;
        case TOKEN_DEC:            return prefix_dec;
        case TOKEN_USER_OP:        return prefix_user_op;

        case TOKEN_ARROW:          return prefix_arrow;

        case TOKEN_STAR:           return prefix_star;

        default:                   return NULL;
        }

Keyword:

        switch (tok()->keyword) {
        case KEYWORD_MATCH:    return prefix_match;
        case KEYWORD_FUNCTION: return prefix_function;
        case KEYWORD_TRUE:     return prefix_true;
        case KEYWORD_FALSE:    return prefix_false;
        case KEYWORD_NIL:      return prefix_nil;
        default:               return NULL;
        }
}

static parse_fn *
get_infix_parser(void)
{
        lex_ctx = LEX_INFIX;

        switch (tok()->type) {
        case TOKEN_KEYWORD:        goto Keyword;
        case '(':                  return infix_function_call;
        case '.':                  return infix_member_access;
        case TOKEN_DOT_MAYBE:      return infix_member_access;
        case '[':                  return infix_subscript;
        case ',':                  return infix_list;
        case TOKEN_INC:            return postfix_inc;
        case TOKEN_DEC:            return postfix_dec;
        case TOKEN_ARROW:          return infix_arrow_function;
        case TOKEN_SQUIGGLY_ARROW: return infix_squiggly_arrow;
        case TOKEN_DOT_DOT:        return infix_range;
        case TOKEN_DOT_DOT_DOT:    return infix_incrange;
        case TOKEN_PLUS_EQ:        return infix_plus_eq;
        case TOKEN_STAR_EQ:        return infix_star_eq;
        case TOKEN_DIV_EQ:         return infix_div_eq;
        case TOKEN_MINUS_EQ:       return infix_minus_eq;
        case TOKEN_MAYBE_EQ:
        case TOKEN_EQ:             return infix_eq;
        case TOKEN_STAR:           return infix_star;
        case TOKEN_DIV:            return infix_div;
        case TOKEN_PERCENT:        return infix_percent;
        case TOKEN_PLUS:           return infix_plus;
        case TOKEN_MINUS:          return infix_minus;
        case TOKEN_LT:             return infix_lt;
        case TOKEN_GT:             return infix_gt;
        case TOKEN_GEQ:            return infix_geq;
        case TOKEN_LEQ:            return infix_leq;
        case TOKEN_CMP:            return infix_cmp;
        case TOKEN_NOT_EQ:         return infix_not_eq;
        case TOKEN_DBL_EQ:         return infix_dbl_eq;
        case TOKEN_OR:             return infix_or;
        case TOKEN_WTF:            return infix_wtf;
        case TOKEN_AND:            return infix_and;
        case TOKEN_USER_OP:        return infix_user_op;
        default:                   return NULL;
        }

Keyword:

        switch (tok()->keyword) {
        case KEYWORD_IF: return infix_conditional;
        default:         return NULL;
        }
}

static int
get_infix_prec(void)
{
        struct value *p;
        lex_ctx = LEX_INFIX;

        switch (tok()->type) {
        case '.':                  return 12;
        case TOKEN_DOT_MAYBE:      return 12;

        case '[':                  return 11;
        case '(':                  return 11;

        case TOKEN_INC:            return 10;
        case TOKEN_DEC:            return 10;

        case TOKEN_DIV:            return 9;
        case TOKEN_STAR:           return 9;
        case TOKEN_PERCENT:        return 9;

        case TOKEN_MINUS:          return 8;
        case TOKEN_PLUS:           return 8;

        case TOKEN_DOT_DOT:        return 7;
        case TOKEN_DOT_DOT_DOT:    return 7;

        case TOKEN_CMP:            return 7;
        case TOKEN_GEQ:            return 7;
        case TOKEN_LEQ:            return 7;
        case TOKEN_GT:             return 7;
        case TOKEN_LT:             return 7;

        case TOKEN_NOT_EQ:         return 6;
        case TOKEN_DBL_EQ:         return 6;

        case TOKEN_AND:            return 5;

        case TOKEN_OR:             return 4;
        case TOKEN_WTF:            return 4;

        /* this may need to have lower precedence. I'm not sure yet. */
        case TOKEN_SQUIGGLY_ARROW: return 3;

        case TOKEN_MAYBE_EQ:
        case TOKEN_EQ:             return NoEquals ? -3 : 2;
        case TOKEN_PLUS_EQ:        return 2;
        case TOKEN_STAR_EQ:        return 2;
        case TOKEN_DIV_EQ:         return 2;
        case TOKEN_MINUS_EQ:       return 2;
        case TOKEN_ARROW:          return 2;

        case ',':                  return 0;

        case TOKEN_KEYWORD:        goto Keyword;
        case TOKEN_USER_OP:        goto UserOp;

        default:                   return -3;
        }

Keyword:
        switch (tok()->keyword) {
        case KEYWORD_IF: return 3;
        default:         return -3;
        }

UserOp:
        p = table_look(&uops, tok()->identifier);
        return (p != NULL) ? abs(p->integer) : 8;
}

static struct expression *
definition_lvalue(struct expression *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_LIST:
                return e;
        case EXPRESSION_FUNCTION_CALL:
                for (int i = 0; i < e->args.count; ++i) {
                        e->args.items[i] = definition_lvalue(e->args.items[i]);
                }
                return e;
        case EXPRESSION_VIEW_PATTERN:
                e->right = definition_lvalue(e->right);
                return e;
        case EXPRESSION_ARRAY:
                if (e->elements.count == 0)
                        break;
                for (size_t i = 0; i < e->elements.count; ++i)
                        e->elements.items[i] = assignment_lvalue(e->elements.items[i]);
                return e;
        }

        error("expression is not a valid definition lvalue");
}

static struct expression *
assignment_lvalue(struct expression *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_SUBSCRIPT:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_FUNCTION_CALL:
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_LIST:
                return e;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i)
                        e->elements.items[i] = assignment_lvalue(e->elements.items[i]);
                return e;
        default:
                error("expression is not a valid assignment lvalue");
        }
}

/*
 * This is kind of a hack.
 */
static struct expression *
parse_definition_lvalue(int context)
{
        struct expression *e;
        int save = tokidx;

        NoEquals = true;
        e = definition_lvalue(parse_expr(1));
        NoEquals = false;

        if (context == LV_LET && tok()->type == ',') {
                struct expression *l = mkexpr();
                l->type = EXPRESSION_LIST;
                vec_init(l->es);
                vec_push(l->es, e);
                while (tok()->type == ',') {
                        next();
                        struct expression *e = parse_definition_lvalue(LV_SUB);
                        if (e == NULL) {
                                error("expected lvalue but found %s", token_show(tok()));
                        }
                        vec_push(l->es, e);
                }
                e = l;
        }

        switch (context) {
        case LV_LET: 
                if (tok()->type != TOKEN_EQ)
                        goto Error;
                break;
        case LV_EACH:
                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IN)
                        break;
                if (tok()->type != ',')
                        goto Error;
                if (token(1)->type != TOKEN_IDENTIFIER)
                        goto Error;
                break;
        default:
                break;
        }

        return e;

Error:
        free(e);
        tokidx = save;
        return NULL;
}

static struct expression *
parse_target_list(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_LIST;
        vec_init(e->es);
        vec_push(e->es, parse_definition_lvalue(LV_EACH));

        if (e->es.items[0] == NULL)
        Error:
                error("expected lvalue in for-each loop");

        while (tok()->type == ',' && (token(1)->type == TOKEN_IDENTIFIER || token(1)->type == '[')) {
                next();
                vec_push(e->es, parse_definition_lvalue(LV_EACH));
                if (vec_last(e->es) == NULL) {
                        goto Error;
                }
        }

        return e;
}

static struct statement *
parse_for_loop(void)
{
        consume_keyword(KEYWORD_FOR);

        struct statement *s = mkstmt();
        s->type = STATEMENT_FOR_LOOP;

        /*
         * First try to parse this as a for-each loop. If that fails, assume it's
         * a C-style for loop.
         */
        if (tok()->type != '(') {
                s->type = STATEMENT_EACH_LOOP;
                s->each.target = parse_target_list();
                consume_keyword(KEYWORD_IN);
                s->each.array = parse_expr(0);
                if (tok()->type == TOKEN_BIT_OR) {
                        next();
                        s->each.cond = parse_expr(0);
                } else {
                        s->each.cond = NULL;
                }
                s->each.body = parse_statement();
                return s;
        }

        consume('(');

        s->for_loop.init = parse_statement();

        if (tok()->type == ';')
                s->for_loop.cond = NULL;
        else
                s->for_loop.cond = parse_expr(0);

        consume(';');

        if (tok()->type == ')')
                s->for_loop.next = NULL;
        else
                s->for_loop.next = parse_expr(0);

        consume(')');

        s->for_loop.body = parse_statement();

        return s;
}

static struct statement *
parse_while_loop(void)
{
        consume_keyword(KEYWORD_WHILE);

        /*
         * Maybe it's a while-match loop.
         */
        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_MATCH) {
                struct statement *m = parse_match_statement();
                m->type = STATEMENT_WHILE_MATCH;
                return m;
        }

        /*
         * Maybe it's a while-let loop.
         */
        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_LET) {
                next();

                struct statement *s = mkstmt();

                s->type = STATEMENT_WHILE_LET;
                s->while_let.pattern = parse_definition_lvalue(LV_LET);

                consume(TOKEN_EQ);

                s->while_let.e = parse_expr(-1);
                s->while_let.block = parse_block();

                return s;
        }

        /*
         * Nope; just a plain old while loop.
         */

        struct statement *s = mkstmt();
        s->type = STATEMENT_WHILE_LOOP;

        consume('(');
        s->while_loop.cond = parse_expr(0);
        consume(')');

        s->while_loop.body = parse_statement();

        return s;
}

static struct statement *
parse_if_statement(void)
{
        consume_keyword(KEYWORD_IF);

        struct statement *s = mkstmt();

        /*
         * Maybe it's an if-let statement.
         */
        if (tok()->type == TOKEN_BANG || (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_LET)) {
                bool neg = tok()->type == TOKEN_BANG;
                if (neg)
                        next();
                consume_keyword(KEYWORD_LET);
                s->type = STATEMENT_IF_LET;
                s->if_let.neg = neg;
                s->if_let.pattern = parse_definition_lvalue(LV_LET);
                consume(TOKEN_EQ);
                s->if_let.e = parse_expr(-1);
                s->if_let.then = parse_block();
                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_ELSE) {
                        next();
                        s->if_let.otherwise = parse_statement();
                } else {
                        s->if_let.otherwise = NULL;
                }
                return s;
        }

        s->type = STATEMENT_CONDITIONAL;

        consume('(');
        s->conditional.cond = parse_expr(0);
        consume(')');

        s->conditional.then_branch = parse_statement();

        if (tok()->type != TOKEN_KEYWORD || tok()->keyword != KEYWORD_ELSE) {
                s->conditional.else_branch = NULL;
                return s;
        }

        consume_keyword(KEYWORD_ELSE);

        s->conditional.else_branch = parse_statement();

        return s;
}

static struct statement *
parse_match_statement(void)
{
        consume_keyword(KEYWORD_MATCH);

        struct statement *s = mkstmt();
        s->type = STATEMENT_MATCH;

        s->match.e = parse_expr(-1);

        consume('{');

        vec_init(s->match.patterns);
        vec_init(s->match.conds);
        vec_init(s->match.statements);

        vec_push(s->match.patterns, parse_expr(-1));
        if (tok()->type == TOKEN_BIT_OR) {
                next();
                vec_push(s->match.conds, parse_expr(0));
        } else {
                vec_push(s->match.conds, NULL);
        }

        consume(TOKEN_FAT_ARROW);
        vec_push(s->match.statements, parse_statement());

        while (tok()->type == ',') {
                next();
                vec_push(s->match.patterns, parse_expr(-1));
                if (tok()->type == TOKEN_BIT_OR) {
                        next();
                        vec_push(s->match.conds, parse_expr(0));
                } else {
                        vec_push(s->match.conds, NULL);
                }
                consume(TOKEN_FAT_ARROW);
                vec_push(s->match.statements, parse_statement());
        }

        consume('}');

        return s;
}

static struct statement *
parse_function_definition(void)
{
        struct expression *f = prefix_function();
        if (f->name == NULL)
                error("unnamed function definitions cannot be used as statements");

        struct expression *target = mkexpr();
        target->type = EXPRESSION_IDENTIFIER;
        target->identifier = f->name;
        target->module = NULL;

        struct statement *s = mkstmt();
        s->type = STATEMENT_FUNCTION_DEFINITION;
        s->target = target;
        s->value = f;
        
        return s;
}

static struct statement *
parse_operator_directive(void)
{
        lex_ctx = LEX_INFIX;

        if (token(1)->type != TOKEN_USER_OP) {
                consume_keyword(KEYWORD_OPERATOR);
                expect(TOKEN_USER_OP);
        }

        next();
        char const *uop = tok()->identifier;
        next();

        expect(TOKEN_INTEGER);
        int p = tok()->integer;
        next();

        expect(TOKEN_IDENTIFIER);
        char const *assoc = tok()->identifier;
        next();

        if (strcmp(assoc, "left") == 0) {
                table_put(&uops, uop, INTEGER(p));
        } else if (strcmp(assoc, "right") == 0) {
                table_put(&uops, uop, INTEGER(-p));
        } else {
                error("expected 'left' or 'right' in operator directive");
        }

        consume(TOKEN_NEWLINE);

        return &NULL_STATEMENT;
}

static struct statement *
parse_return_statement(void)
{
        consume_keyword(KEYWORD_RETURN);

        struct statement *s = mkstmt();
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);

        while (tok()->type != ';') {
        Expr:
                vec_push(s->returns, parse_expr(0));
                if (tok()->type == ',') {
                        next();
                        goto Expr;
                }
        }

        consume(';');

        return s;
}

static struct statement *
parse_let_definition(void)
{

        struct statement *s = mkstmt();
        s->type = STATEMENT_DEFINITION;

        consume_keyword(KEYWORD_LET);

        struct expression *target = parse_definition_lvalue(LV_LET);
        if (target == NULL)
                error("failed to parse lvalue in 'let' definition");

        consume(TOKEN_EQ);

        struct expression *value = parse_expr(-1);
        
        consume(';');

        s->target = target;
        s->value = value;

        return s;
}

static struct statement *
parse_break_statement(void)
{
        consume_keyword(KEYWORD_BREAK);
        consume(';');
        return &BREAK_STATEMENT;
}

static struct statement *
parse_continue_statement(void)
{
        consume_keyword(KEYWORD_CONTINUE);
        consume(';');
        return &CONTINUE_STATEMENT;
}

static struct statement *
parse_null_statement()
{
        consume(';');
        return &NULL_STATEMENT;
}

static struct expression *
parse_expr(int prec)
{
        struct expression *e;

        if (++depth > 256)
                error("exceeded maximum recursion depth of 256");

        parse_fn *f = get_prefix_parser();
        if (f == NULL)
                error("expected expression but found %s", token_show(tok()));

        e = f();

        while (prec < get_infix_prec()) {
                f = get_infix_parser();
                if (f == NULL)
                        error("unexpected token after expression: %s", token_show(tok()));
                e = f(e);
        }

        --depth;

        return e;
}

static struct statement *
parse_block(void)
{
        struct statement *s = mkstmt();

        consume('{');

        s->type = STATEMENT_BLOCK;
        vec_init(s->statements);

        while (tok()->type != '}') {
                vec_push(s->statements, parse_statement());
        }

        consume('}');

        return s;
}

static struct statement *
parse_class_definition(void)
{
        bool tag = tok()->keyword == KEYWORD_TAG;

        consume_keyword(tag ? KEYWORD_TAG : KEYWORD_CLASS);

        expect(TOKEN_IDENTIFIER);

        struct statement *s = mkstmt();
        s->type = tag ? STATEMENT_TAG_DEFINITION : STATEMENT_CLASS_DEFINITION;
        s->tag.name = tok()->identifier;
        vec_init(s->tag.methods);

        next();

        if (tok()->type == ':') {
                next();
                expect(TOKEN_IDENTIFIER);
                s->tag.super = mkexpr();
                s->tag.super->type = EXPRESSION_IDENTIFIER;
                s->tag.super->identifier = tok()->identifier;
                s->tag.super->module = tok()->module;
                next();
        } else {
                s->tag.super = NULL;
        }

        /* Hack to allow comma-separated tag declarations */
        if (tag && tok()->type == ',' && token(1)->type == TOKEN_IDENTIFIER) {
                next();
                unconsume(TOKEN_KEYWORD);
                tok()->keyword = KEYWORD_TAG;
                unconsume(';');
        }
                
        if (tag && tok()->type == ';') {
                next();
        } else {
                consume('{');
                lex_ctx = LEX_INFIX;
                while (tok()->type != '}') {
                        /*
                         * Lol.
                         */
                        switch (tok()->type) {
                        case TOKEN_DBL_EQ:  tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "==";   break;
                        case TOKEN_CMP:     tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "<=>";  break;
                        case TOKEN_PLUS:    tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "+";    break;
                        case TOKEN_DIV:     tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "/";    break;
                        case TOKEN_MINUS:   tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "-";    break;
                        case TOKEN_STAR:    tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "*";    break;
                        case TOKEN_PERCENT: tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "%";    break;
                        case TOKEN_USER_OP: tok()->type = TOKEN_IDENTIFIER;                             break;
                        default:                                                                        break;
                        }
                        /*
                         * Push a 'function' keyword token back onto the stream so that we can
                         * use the existing function parsing code to parse the method.
                         */
                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_FUNCTION;

                        vec_push(s->tag.methods, prefix_function());
                }
                lex_ctx = LEX_PREFIX;
                consume('}');
        }

        return s;
}

static struct statement *
parse_throw(void)
{
        consume_keyword(KEYWORD_THROW);

        struct statement *s = mkstmt();
        s->type = STATEMENT_THROW;
        s->throw = parse_expr(0);

        consume(';');

        return s;
}

static struct statement *
parse_try(void)
{
        consume_keyword(KEYWORD_TRY);

        struct statement *s = mkstmt();
        s->type = STATEMENT_TRY;

        s->try.s = parse_statement();

        vec_init(s->try.patterns);
        vec_init(s->try.handlers);

        while (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_CATCH) {
                next();
                vec_push(s->try.patterns, parse_expr(0));
                vec_push(s->try.handlers, parse_statement());
        }

        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_FINALLY) {
                next();
                s->try.finally = parse_statement();
        } else {
                s->try.finally = NULL;
        }

        return s;
}

static struct statement *
parse_export(void)
{
        consume_keyword(KEYWORD_EXPORT);

        struct statement *s = mkstmt();
        s->type = STATEMENT_EXPORT;

        vec_init(s->exports);

        while (tok()->type == TOKEN_IDENTIFIER || tok()->type == TOKEN_USER_OP) {
                vec_push(s->exports, tok()->identifier);
                next();
                if (tok()->type == ',')
                        next();
                else
                        expect(TOKEN_NEWLINE);
        }

        consume(TOKEN_NEWLINE);

        return s;
}

static struct statement *
parse_import(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_IMPORT;

        consume_keyword(KEYWORD_IMPORT);

        expect(TOKEN_IDENTIFIER);
        char *mod = tok()->module;
        char *id = tok()->identifier;
        next();

        int modlen = (mod == NULL) ? 0 : strlen(mod);
        int idlen = strlen(id);

        char *module = alloc(modlen + idlen + 2);
        if (mod != NULL) {
                strcpy(module, mod);
                strcat(module, "/");
                strcat(module, id);
        } else {
                strcpy(module, id);
        }

        s->import.module = module;

        if (tok()->type == TOKEN_IDENTIFIER && strcmp(tok()->identifier, "as") == 0) {
                next();
                expect(TOKEN_IDENTIFIER);
                s->import.as = tok()->identifier;
                next();
        } else {
                s->import.as = module;
        }

        vec_init(s->import.identifiers);

        if (tok()->type == '(') {
                next();
                if (tok()->type == TOKEN_DOT_DOT) {
                        next();
                        vec_push(s->import.identifiers, "..");
                } else while (tok()->type == TOKEN_IDENTIFIER) {
                        vec_push(s->import.identifiers, tok()->identifier);
                        next();
                        if (tok()->type == ',')
                                next();
                        else
                                expect(')');
                }
                consume(')');
        }

        consume(TOKEN_NEWLINE);

        return s;
}

static struct statement *
parse_statement(void)
{
        struct statement *s;

        lex_ctx = LEX_PREFIX;

        switch (tok()->type) {
        case '{':            return parse_block();
        case ';':            return parse_null_statement();
        case TOKEN_KEYWORD:  goto Keyword;
        default:             goto Expression;
        }

Keyword:

        switch (tok()->keyword) {
        case KEYWORD_CLASS:    return parse_class_definition();
        case KEYWORD_TAG:      return parse_class_definition();
        case KEYWORD_FOR:      return parse_for_loop();
        case KEYWORD_WHILE:    return parse_while_loop();
        case KEYWORD_IF:       return parse_if_statement();
        case KEYWORD_FUNCTION: return parse_function_definition();
        case KEYWORD_OPERATOR: return parse_operator_directive();
        case KEYWORD_MATCH:    return parse_match_statement();
        case KEYWORD_RETURN:   return parse_return_statement();
        case KEYWORD_LET:      return parse_let_definition();
        case KEYWORD_BREAK:    return parse_break_statement();
        case KEYWORD_CONTINUE: return parse_continue_statement();
        case KEYWORD_TRY:      return parse_try();
        case KEYWORD_THROW:    return parse_throw();
        default:               goto Expression;
        }

Expression:

        s = mkstmt();
        s->type = STATEMENT_EXPRESSION;
        s->expression = parse_expr(-1);
        consume(';');

        return s;
}

char const *
parse_error(void)
{
        return errbuf;
}

struct statement **
parse(char const *source, char const *file)
{
        vec(struct statement *) program;
        vec_init(program);

        depth = 0;

        filename = file;

        vec_init(tokens);
        tokidx = 0;
        lex_ctx = LEX_PREFIX;

        lex_init(file);
        lex_start(source);

        if (setjmp(jb) != 0) {
                vec_empty(program);
                lex_end();
                return NULL;
        }

        while (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IMPORT)
                vec_push(program, parse_import());

        while (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_EXPORT)
                vec_push(program, parse_export());

        while (tok()->type != TOKEN_END)
                vec_push(program, parse_statement());

        vec_push(program, NULL);

        lex_end();

        return program.items;
}

#define parse(s) parse(s, "<test>")

TEST(break_statement)
{
        char const *source = "break;";
        struct statement **p = parse(source);
        struct statement *s = p[0];

        claim(p[1] == NULL);

        claim(s != NULL);
        claim(s->type == STATEMENT_BREAK);
        claim(s == &BREAK_STATEMENT);
}

TEST(parse_error)
{
        char const *source = "function a (,) { }";
        struct statement **p = parse(source);
        claim(p == NULL);

        claim(strstr(parse_error(), "but found token ','"));
}

TEST(trivial_function)
{
        claim(parse("function f();") != NULL);
}

TEST(number)
{
        claim(parse("45.3;") != NULL);
}

TEST(string)
{
        claim(parse("'hello, world!';") != NULL);
}

TEST(function_call)
{
        struct statement **s;

        claim((s = parse("f();")) != NULL);

        claim((s = parse("f(43);")) != NULL);

        claim((s = parse("f(a, b, g(c));")) != NULL);
}

TEST(parenthesized_expression)
{
        claim(parse("(((3)));") != NULL);
}

TEST(plus_op)
{
        struct statement *s = parse("a + 4 + f();")[0];
        claim(s->type == STATEMENT_EXPRESSION);
        claim(s->expression->type == EXPRESSION_PLUS);
        claim(s->expression->left->type == EXPRESSION_PLUS);
        claim(s->expression->left->left->type == EXPRESSION_IDENTIFIER);
        claim(s->expression->left->right->type == EXPRESSION_INTEGER);
}

TEST(object_literal)
{
        
        struct statement *s = parse("1 + {};")[0];
        claim(s->type == STATEMENT_EXPRESSION);
        claim(s->expression->type == EXPRESSION_PLUS);
        claim(s->expression->right->type == EXPRESSION_DICT);
        claim(s->expression->right->keys.count == 0);
        claim(s->expression->right->values.count == 0);

        s = parse("1 + {4 + 3: 'test'};")[0];
        claim(s->type == STATEMENT_EXPRESSION);
        claim(s->expression->type == EXPRESSION_PLUS);
        claim(s->expression->right->type == EXPRESSION_DICT);
        claim(s->expression->right->keys.count == 1);
        claim(s->expression->right->values.count == 1);
        claim(s->expression->right->keys.items[0]->type == EXPRESSION_PLUS);
        claim(s->expression->right->values.items[0]->type == EXPRESSION_STRING);
}

TEST(array_literal)
{
        struct statement *s = parse("[1, 2, 3];")[0];
        claim(s->type == STATEMENT_EXPRESSION);
        claim(s->expression->type == EXPRESSION_ARRAY);
        claim(s->expression->elements.count == 3);
}

TEST(test_programs)
{
        char *test_progs[] = {
                "tests/programs/hello",
                "tests/programs/factorial",
                "tests/programs/closure",
        };

        for (size_t i = 0; i < sizeof test_progs / sizeof test_progs[0]; ++i) {
                struct statement **p = parse(slurp(test_progs[i]));
                if (p == NULL) {
                        printf("\n%s: %s\n", test_progs[i], parse_error());
                        claim(false);
                }
        }
}

TEST(method_call)
{
        struct statement **p = parse("buffer.verticalSplit();");
        claim(p != NULL);

        struct statement *s = p[0];
        claim(s->type == STATEMENT_EXPRESSION);
        claim(s->expression->type == EXPRESSION_METHOD_CALL);
        claim(s->expression->object->type == EXPRESSION_IDENTIFIER);
        claim(strcmp(s->expression->object->identifier, "buffer") == 0);
        claim(strcmp(s->expression->method_name, "verticalSplit") == 0);
        claim(s->expression->method_args.count == 0);
}

TEST(let)
{
        claim(parse("let a = 12;") != NULL);
        claim(parse("let [a, b] = [12, 14];") != NULL);
        claim(parse("let [[a1, a2], b] = [[12, 19], 14];") != NULL);

        claim(parse("let a[3] = 5;") == NULL);
        claim(strstr(parse_error(), "failed to parse lvalue in 'let' definition") != NULL);
}

TEST(each_loop)
{
        struct statement **p = parse("for (a in as) print(a);");
        claim(p != NULL);

        struct statement *s = p[0];
        claim(s->type == STATEMENT_EACH_LOOP);
        claim(s->each.array->type == EXPRESSION_IDENTIFIER);
        claim(s->each.target->type == EXPRESSION_IDENTIFIER);
        claim(s->each.body->type == STATEMENT_EXPRESSION);
        claim(s->each.body->expression->type == EXPRESSION_FUNCTION_CALL);
}

TEST(arrow)
{
        struct statement **p = parse("let f = (a, b) -> a + b;");
        claim(p != NULL);

        struct statement *s = p[0];
        claim(s->type == STATEMENT_DEFINITION);
        claim(s->value->type == EXPRESSION_FUNCTION);
        claim(s->value->params.count == 2);
        claim(s->value->body->type == STATEMENT_RETURN);
        claim(s->value->body->returns.items[0]->type == EXPRESSION_PLUS);
}

TEST(import)
{
        struct statement **p = parse("import editor::buffer as buffer\n");
        claim(p != NULL);

        struct statement *s = p[0];
        claim(s->type == STATEMENT_IMPORT);
        printf("module: %s", s->import.module);
        claim(strcmp(s->import.module, "editor/buffer") == 0);
        claim(strcmp(s->import.as, "buffer") == 0);
}

TEST(div_vs_regex)
{
        claim(parse("print(100 / 5 / 2);") != NULL);
}

TEST(regex)
{
        parse("/hello/;");
        printf("%s\n", parse_error());
}

TEST(match)
{
        claim(parse("match g(4, [4]) { Add([a, b]) | a != 0 => return a + b;, Mul([a, b]) => a * b; }") != NULL);
}

TEST(special_string)
{
        claim(parse("let s = \"{a +}\";") == NULL);
        claim(parse("let s = \"{a + 4}\";") != NULL);
}

TEST(method_defs)
{
        claim(parse("tag Foo;") != NULL);
        claim(parse("tag Baz {}") != NULL);
        claim(parse("tag Baz { foo(a, b, c) { return 42 * 10; } }") != NULL);

        claim(parse("tag Bar") == NULL);
        claim(parse("tag Blah { 5 }") == NULL);
        claim(parse("tag Blah {") == NULL);
}
