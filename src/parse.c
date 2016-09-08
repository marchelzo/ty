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
        LV_ANY
};

static jmp_buf jb;
static char errbuf[MAX_ERR_LEN + 1];

static vec(struct token) tokens;
static int tokidx = 0;
enum lex_context lex_ctx = LEX_PREFIX;

static int depth;

static struct statement BREAK_STATEMENT    = { .type = STATEMENT_BREAK,    .loc = {42, 42} };
static struct statement CONTINUE_STATEMENT = { .type = STATEMENT_CONTINUE, .loc = {42, 42} };
static struct statement NULL_STATEMENT     = { .type = STATEMENT_NULL,     .loc = {42, 42} };

static struct statement *
parse_statement(void);

static struct expression *
parse_expr(int);

static struct statement *
parse_match_statement(void);

static struct statement *
parse_let_definition(void);

static struct statement *
parse_block(void);

static struct expression *
assignment_lvalue(struct expression *e);

static struct expression *
definition_lvalue(struct expression *e);

inline static struct token *
tok(void);

/*
 * Get a unique identifier name.
 * This sucks.
 */
char *
gensym(void)
{
        static int sym = 0;
        char buf[24];

        sprintf(buf, ":%d", sym++);

        return sclone(buf);
}

inline static struct expression *
mkexpr(void)
{
        struct expression *e = alloc(sizeof *e);
        e->loc = tok()->loc;
        return e;
}

inline static struct statement *
mkstmt(void)
{
        struct statement *s = alloc(sizeof *s);
        s->loc = tok()->loc;
        return s;
}

inline static struct statement *
mkret(struct expression *value)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_RETURN;
        s->return_value = value;
        return s;
}

inline static struct statement *
mkdef(struct expression *lvalue, char *name)
{
        struct expression *value = mkexpr();
        value->type = EXPRESSION_IDENTIFIER;
        value->identifier = name;

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
                n += sprintf(err, "ParseError at %d:%d: ", tok()->loc.line + 1, tok()->loc.col + 1);
                vsnprintf(err + n, MAX_ERR_LEN - n, fmt, ap);

                va_end(ap);
        }

        LOG("Parse Error: %s", errbuf);

        longjmp(jb, 1);
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

        return &tokens.items[tokidx + i];
}

inline static struct token *
tok(void)
{
        return token(0);
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
prefix_tag(void)
{
        expect(TOKEN_TAG);

        struct expression *e = mkexpr();

        e->type = EXPRESSION_TAG;
        e->identifier = tok()->tag;
        e->module = tok()->module;

        consume(TOKEN_TAG);

        lex_ctx = LEX_INFIX;
        if (tok()->type == '(') {
                consume('(');
                e->type = EXPRESSION_TAG_APPLICATION;
                e->tagged = parse_expr(0);
                consume(')');
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
        vec_init(e->params);

        if (tok()->type == TOKEN_IDENTIFIER) {
                e->name = tok()->identifier;
                consume(TOKEN_IDENTIFIER);
        } else {
                e->name = NULL;
        }

        consume('(');

        if (tok()->type == ')') {
                consume(')');
                goto body;
        } else {
                expect(TOKEN_IDENTIFIER);
                vec_push(e->params, sclone(tok()->identifier));
                consume(TOKEN_IDENTIFIER);
        }

        while (tok()->type == ',') {
                consume(',');
                expect(TOKEN_IDENTIFIER);
                vec_push(e->params, sclone(tok()->identifier));
                consume(TOKEN_IDENTIFIER);
        }

        consume(')');

body:

        e->body = parse_statement();

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
        if (tok()->module != NULL) {
                error("unexpected module qualifier in lvalue");
        }
        consume(TOKEN_IDENTIFIER);

        return e;
}

static struct expression *
prefix_match(void)
{
        consume_keyword(KEYWORD_MATCH);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_MATCH;

        e->subject = parse_expr(0);

        consume('{');

        vec_init(e->patterns);
        vec_init(e->conds);
        vec_init(e->thens);

        vec_push(e->patterns, parse_expr(0));
        if (tok()->type == TOKEN_BIT_OR) {
                consume(TOKEN_BIT_OR);
                vec_push(e->conds, parse_expr(0));
        } else {
                vec_push(e->conds, NULL);
        }

        consume(TOKEN_FAT_ARROW);
        vec_push(e->thens, parse_expr(0));

        while (tok()->type == ',') {
                consume(',');
                vec_push(e->patterns, parse_expr(0));
                if (tok()->type == TOKEN_BIT_OR) {
                        consume(TOKEN_BIT_OR);
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
         * or it can be an identifier list for an arrow function, e.g., (a, b, c),
         * or it can be a range, e.g., (4 .. 10]
         */

        consume('(');

        /*
         * () is an empty identifier list.
         */
        if (tok()->type == ')') {
                consume(')');
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
                if (e->type != EXPRESSION_IDENTIFIER) {
                        list->only_identifiers = false;
                }

                list->type = EXPRESSION_LIST;
                vec_init(list->es);
                vec_push(list->es, e);

                while (tok()->type == ',') {
                        consume(',');
                        struct expression *e = parse_expr(0);
                        if (e->type != EXPRESSION_IDENTIFIER) {
                                list->only_identifiers = false;
                        }
                        vec_push(list->es, e);
                }

                consume(')');

                return list;
        } else if (tok()->type == TOKEN_DOT_DOT) {
                /* It's a range */
                struct expression *range = mkexpr();
                range->flags = RANGE_EXCLUDE_LEFT;
                range->type = EXPRESSION_RANGE;
                range->low = e;

                consume(TOKEN_DOT_DOT);

                range->high = parse_expr(0);

                if (tok()->type == ')') {
                        range->flags |= RANGE_EXCLUDE_RIGHT;
                        consume(')');
                } else if (tok()->type == ']') {
                        consume(']');
                } else {
                        error("expected ')' or ']' to close range");
                }

                return range;
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

        struct expression *e = mkexpr();
        e->type = EXPRESSION_ARRAY;
        vec_init(e->elements);

        if (tok()->type == ']') {
                consume(']');
                return e;
        } else {
                vec_push(e->elements, parse_expr(0));
        }

        /*
         * Maybe it's a range?
         */
        if (tok()->type == TOKEN_DOT_DOT) {
                consume(TOKEN_DOT_DOT);
                e->type = EXPRESSION_RANGE;
                e->low = e->elements.items[0];
                e->flags = 0;
                e->high = parse_expr(0);

                if (tok()->type == ')') {
                        e->flags |= RANGE_EXCLUDE_RIGHT;
                        consume(')');
                } else if (tok()->type == ']') {
                        consume(']');
                } else {
                        error("expected ')' or ']' to close range");
                }

                return e;
        }

        while (tok()->type == ',') {
                consume(',');
                vec_push(e->elements, parse_expr(0));
        }

        consume(']');

        return e;
}

static struct expression *
prefix_hash(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_IDENTIFIER;
        e->identifier = "#";

        consume('#');

        return e;
}

static struct expression *
prefix_implicit_lambda(void)
{
        consume(TOKEN_BIT_OR);

        struct expression *f = mkexpr();
        f->type = EXPRESSION_FUNCTION;
        f->name = NULL;
        vec_init(f->params);
        vec_push(f->params, "#");

        struct statement *ret = mkstmt();
        ret->type = STATEMENT_RETURN;
        ret->return_value = parse_expr(0);
        f->body = ret;

        consume(TOKEN_BIT_OR);

        return f;
}

static struct expression *
prefix_object(void)
{
        consume('{');

        struct expression *e = mkexpr();
        e->type = EXPRESSION_OBJECT;

        vec_init(e->keys);
        vec_init(e->values);

        if (tok()->type == '}') {
                consume('}');
                return e;
        } else {
                vec_push(e->keys, parse_expr(0));
                consume(':');
                vec_push(e->values, parse_expr(0));
        }

        while (tok()->type == ',') {
                consume(',');
                vec_push(e->keys, parse_expr(0));
                consume(':');
                vec_push(e->values, parse_expr(0));
        }

        consume('}');

        return e;
}

PREFIX_OPERATOR(at,    AT,    9)
PREFIX_OPERATOR(minus, MINUS, 9)
PREFIX_OPERATOR(bang,  BANG,  0)

PREFIX_LVALUE_OPERATOR(inc,   INC,   6)
PREFIX_LVALUE_OPERATOR(dec,   DEC,   6)
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
                consume(')');
                return e;
        } else {
                vec_push(e->args, parse_expr(0));
        }

        while (tok()->type == ',') {
                consume(',');
                vec_push(e->args, parse_expr(0));
        }

        consume(')');

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
        consume('.');
        
        struct expression *e = mkexpr();
        e->object = left;

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

        if (tok()->type == ')') {
                consume(')');
                return e;
        } else {
                vec_push(e->method_args, parse_expr(0));
        }

        while (tok()->type == ',') {
                consume(',');
                vec_push(e->method_args, parse_expr(0));
        }

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
        /*
         * If it's not a list, we need to make sure it's a valid definition lvalue.
         * For example, ([a, b, c] -> a + b * c) is allowed, but not ([a[0], b, c] -> b * c).
         */
        if (left->type != EXPRESSION_LIST) {
                left = definition_lvalue(left);
        }

        consume(TOKEN_ARROW);

        struct expression *e = mkexpr();
        e->type = EXPRESSION_FUNCTION;
        e->name = NULL;
        vec_init(e->params);


        /*
         * If the left hand side consists of nothing more than identifiers, we can use a regular function.
         *
         * e.g., (a, b, c) -> (a + b + c) can become function (a, b, c) { return (a + b + c); }
         *
         * but
         *
         *       ([a, b], [c, d]) -> (a + b + c + d) must be transformed into something more complicated.
         */
        if (left->type == EXPRESSION_IDENTIFIER || (left->type == EXPRESSION_LIST && left->only_identifiers)) {
                if (left->type == EXPRESSION_IDENTIFIER) {
                        vec_push(e->params, left->identifier);
                } else {
                        for (int i = 0; i < left->es.count; ++i) {
                                vec_push(e->params, left->es.items[i]->identifier);
                        }
                }

                e->body = mkret(parse_expr(0));

                return e;
        } else {
                /*
                 * In this case, we will generate unique names for each parameter, and then use
                 * 'let' statements in the function body to unpack them.
                 */
                struct statement *body = mkstmt();
                body->type = STATEMENT_BLOCK;
                vec_init(body->statements);

                if (left->type == EXPRESSION_LIST) {
                        for (int i = 0; i < left->es.count; ++i) {
                                char *name = gensym();
                                vec_push(e->params, name);
                                vec_push(body->statements, mkdef(left->es.items[i], name));
                        }
                } else {
                        char *name = gensym();
                        vec_push(e->params, name);
                        vec_push(body->statements, mkdef(left, name));
                }

                vec_push(body->statements, mkret(parse_expr(0)));

                e->body = body;

                return e;
        }
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

BINARY_OPERATOR(star,    STAR,    8, false)
BINARY_OPERATOR(div,     DIV,     8, false)
BINARY_OPERATOR(percent, PERCENT, 8, false)

BINARY_OPERATOR(plus,    PLUS,    7, false)
BINARY_OPERATOR(minus,   MINUS,   7, false)

BINARY_OPERATOR(lt,      LT,      6, false)
BINARY_OPERATOR(gt,      GT,      6, false)
BINARY_OPERATOR(geq,     GEQ,     6, false)
BINARY_OPERATOR(leq,     LEQ,     6, false)

BINARY_OPERATOR(not_eq,  NOT_EQ,  5, false)
BINARY_OPERATOR(dbl_eq,  DBL_EQ,  5, false)

BINARY_OPERATOR(and,     AND,     4, false)

BINARY_OPERATOR(or,      OR,      3, false)

BINARY_LVALUE_OPERATOR(eq,       EQ,       1, true)
BINARY_LVALUE_OPERATOR(plus_eq,  PLUS_EQ,  1, true)
BINARY_LVALUE_OPERATOR(star_eq,  STAR_EQ,  1, true)
BINARY_LVALUE_OPERATOR(div_eq,   DIV_EQ,   1, true)
BINARY_LVALUE_OPERATOR(minus_eq, MINUS_EQ, 1, true)
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

        case TOKEN_TAG:        return prefix_tag;
        case TOKEN_IDENTIFIER: return prefix_identifier;
        case TOKEN_KEYWORD:    goto keyword;

        case TOKEN_BIT_OR:     return prefix_implicit_lambda;
        case '#':              return prefix_hash;

        case '(':              return prefix_parenthesis;
        case '[':              return prefix_array;
        case '{':              return prefix_object;

        case TOKEN_BANG:       return prefix_bang;
        case TOKEN_AT:         return prefix_at;
        case TOKEN_MINUS:      return prefix_minus;
        case TOKEN_INC:        return prefix_inc;
        case TOKEN_DEC:        return prefix_dec;

        case TOKEN_STAR:       return prefix_star;

        default:               return NULL;
        }

keyword:

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
        case TOKEN_KEYWORD:        goto keyword;
        case '(':                  return infix_function_call;
        case '.':                  return infix_member_access;
        case '[':                  return infix_subscript;
        case TOKEN_INC:            return postfix_inc;
        case TOKEN_DEC:            return postfix_dec;
        case TOKEN_ARROW:          return infix_arrow_function;
        case TOKEN_SQUIGGLY_ARROW: return infix_squiggly_arrow;
        case TOKEN_PLUS_EQ:        return infix_plus_eq;
        case TOKEN_STAR_EQ:        return infix_star_eq;
        case TOKEN_DIV_EQ:         return infix_div_eq;
        case TOKEN_MINUS_EQ:       return infix_minus_eq;
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
        case TOKEN_NOT_EQ:         return infix_not_eq;
        case TOKEN_DBL_EQ:         return infix_dbl_eq;
        case TOKEN_OR:             return infix_or;
        case TOKEN_AND:            return infix_and;
        default:                   return NULL;
        }

keyword:

        switch (tok()->keyword) {
        case KEYWORD_IF: return infix_conditional;
        default:         return NULL;
        }
}

static int
get_infix_prec(void)
{
        lex_ctx = LEX_INFIX;

        switch (tok()->type) {
        case '.':                  return 11;

        case '[':                  return 10;
        case '(':                  return 10;

        case TOKEN_INC:            return 9;
        case TOKEN_DEC:            return 9;

        case TOKEN_PERCENT:        return 8;
        case TOKEN_DIV:            return 8;
        case TOKEN_STAR:           return 8;

        case TOKEN_MINUS:          return 7;
        case TOKEN_PLUS:           return 7;

        case TOKEN_GEQ:            return 6;
        case TOKEN_LEQ:            return 6;
        case TOKEN_GT:             return 6;
        case TOKEN_LT:             return 6;

        case TOKEN_NOT_EQ:         return 5;
        case TOKEN_DBL_EQ:         return 5;

        case TOKEN_AND:            return 4;

        case TOKEN_OR:             return 3;

        case TOKEN_EQ:             return 1;
        case TOKEN_PLUS_EQ:        return 1;
        case TOKEN_STAR_EQ:        return 1;
        case TOKEN_DIV_EQ:         return 1;
        case TOKEN_MINUS_EQ:       return 1;
        case TOKEN_ARROW:          return 1;

        // this may need to have lower precedence at; I'm not sure yet.
        case TOKEN_SQUIGGLY_ARROW: return 1;

        case TOKEN_KEYWORD:        goto keyword;

        default:                   return -1;
        }

keyword:

        switch (tok()->keyword) {
        case KEYWORD_IF: return 2;
        default:         return -1;
        }
}

static struct expression *
definition_lvalue(struct expression *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_TAG_APPLICATION:
                return e;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        e->elements.items[i] = assignment_lvalue(e->elements.items[i]);
                }
                return e;
        default:
                error("expression is not a valid definition lvalue");
        }
}

static struct expression *
assignment_lvalue(struct expression *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_SUBSCRIPT:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_MEMBER_ACCESS:
                return e;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i) {
                        e->elements.items[i] = assignment_lvalue(e->elements.items[i]);
                }
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
        struct expression *e, *elem;
        int save = tokidx;

        switch (tok()->type) {
        case TOKEN_IDENTIFIER:
                e = mkexpr();

                e->type = EXPRESSION_IDENTIFIER;
                e->identifier = tok()->identifier;

                if (tok()->module != NULL) {
                        error("unexpected module qualifier in lvalue");
                }

                consume(TOKEN_IDENTIFIER);
                break;
        case TOKEN_TAG:
                e = mkexpr();

                e->type = EXPRESSION_TAG_APPLICATION;
                e->identifier = tok()->tag;
                e->module = tok()->module;

                consume(TOKEN_TAG);

                lex_ctx = LEX_INFIX;

                consume('(');
                if (e->tagged = parse_definition_lvalue(LV_ANY), e->tagged == NULL) {
                        goto error;
                }
                consume(')');

                break;
        case '[':
                consume('[');
                e = mkexpr();
                e->type = EXPRESSION_ARRAY;
                vec_init(e->elements);
                if (tok()->type == ']') {
                        consume(']');
                        break;
                } else {
                        if (elem = parse_definition_lvalue(LV_ANY), elem == NULL) {
                                vec_empty(e->elements);
                                goto error;
                        } else {
                                vec_push(e->elements, elem);
                        }
                }
                while (tok()->type == ',') {
                        consume(',');
                        if (elem = parse_definition_lvalue(LV_ANY), elem == NULL) {
                                vec_empty(e->elements);
                                goto error;
                        } else {
                                vec_push(e->elements, elem);
                        }

                }
                if (tok()->type != ']') {
                        vec_empty(e->elements);
                        goto error;
                }

                consume(']');
                break;
        case '(':
                consume('(');
                e = parse_definition_lvalue(LV_ANY);
                if (e == NULL || tok()->type != ')') {
                        goto error;
                }
                consume(')');
                break;
        default:
                return NULL;
        }

        switch (context) {
        case LV_LET:  if (tok()->type != TOKEN_EQ)                                      goto error; break;
        case LV_EACH: if (tok()->type != TOKEN_KEYWORD || tok()->keyword != KEYWORD_IN) goto error; break;
        default:                                                                                    break;
        }

        return e;

error:
        free(e);
        tokidx = save;
        return NULL;
}

static struct statement *
parse_for_loop(void)
{
        consume_keyword(KEYWORD_FOR);

        struct statement *s = mkstmt();
        s->type = STATEMENT_FOR_LOOP;

        consume('(');

        /*
         * First try to parse this as a for-each loop. If that fails, assume it's
         * a C-style for loop.
         */
        struct expression *each_target = parse_definition_lvalue(LV_EACH);
        if (each_target != NULL) {
                s->type = STATEMENT_EACH_LOOP;
                s->each.target = each_target;

                consume_keyword(KEYWORD_IN);

                s->each.array = parse_expr(0);

                consume(')');

                s->each.body = parse_statement();

                return s;
        }

        s->for_loop.init = parse_statement();

        if (tok()->type == ';') {
                s->for_loop.cond = NULL;
        } else {
                s->for_loop.cond = parse_expr(0);
        }

        consume(';');

        if (tok()->type == ')') {
                s->for_loop.next = NULL;
        } else {
                s->for_loop.next = parse_expr(0);
        }

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
                consume_keyword(KEYWORD_LET);

                struct statement *s = mkstmt();

                s->type = STATEMENT_WHILE_LET;
                s->while_let.pattern = parse_definition_lvalue(LV_LET);

                consume(TOKEN_EQ);

                s->while_let.e = parse_expr(0);
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
        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_LET) {
                consume_keyword(KEYWORD_LET);
                s->type = STATEMENT_IF_LET;
                s->if_let.pattern = parse_definition_lvalue(LV_LET);
                consume(TOKEN_EQ);
                s->if_let.e = parse_expr(0);
                s->if_let.then = parse_block();
                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_ELSE) {
                        consume_keyword(KEYWORD_ELSE);
                        s->if_let.otherwise = parse_block();
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

        s->match.e = parse_expr(0);

        consume('{');

        vec_init(s->match.patterns);
        vec_init(s->match.conds);
        vec_init(s->match.statements);

        vec_push(s->match.patterns, parse_expr(0));
        if (tok()->type == TOKEN_BIT_OR) {
                consume(TOKEN_BIT_OR);
                vec_push(s->match.conds, parse_expr(0));
        } else {
                vec_push(s->match.conds, NULL);
        }

        consume(TOKEN_FAT_ARROW);
        vec_push(s->match.statements, parse_statement());

        while (tok()->type == ',') {
                consume(',');
                vec_push(s->match.patterns, parse_expr(0));
                if (tok()->type == TOKEN_BIT_OR) {
                        consume(TOKEN_BIT_OR);
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
parse_function_def(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_DEFINITION;
        s->pub = false;

        struct expression *f = prefix_function();
        if (f->name == NULL) {
                error("unnamed function definitions cannot be used as statements");
        }

        struct expression *target = mkexpr();
        target->type = EXPRESSION_IDENTIFIER;
        target->identifier = f->name;

        s->target = target;
        s->value = f;
        
        return s;
}

static struct statement *
parse_return_statement(void)
{
        consume_keyword(KEYWORD_RETURN);

        struct statement *s = mkstmt();
        s->type = STATEMENT_RETURN;

        if (tok()->type == ';') {
                s->return_value = NULL;
        } else {
                s->return_value = parse_expr(0);
        }

        consume(';');

        return s;

}

static struct statement *
parse_let_definition(void)
{

        struct statement *s = mkstmt();
        s->type = STATEMENT_DEFINITION;
        s->pub = false;

        consume_keyword(KEYWORD_LET);

        struct expression *target = parse_definition_lvalue(LV_LET);
        if (target == NULL) {
                error("failed to parse lvalue in 'let' definition");
        }

        consume(TOKEN_EQ);

        struct expression *value = parse_expr(0);
        
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
        if (f == NULL) {
                error("expected expression but found %s", token_show(tok()));
        }

        e = f();

        while (prec < get_infix_prec()) {
                f = get_infix_parser();
                if (f == NULL) {
                        error("unexpected token after expression: %s", token_show(tok()));
                }
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
parse_tag_def(void)
{
        consume_keyword(KEYWORD_TAG);

        expect(TOKEN_TAG);

        struct statement *s = mkstmt();
        s->type = STATEMENT_TAG_DEFINITION;
        s->tag = tok()->tag;

        consume(TOKEN_TAG);

        return s;
}

static struct statement *
parse_export(void)
{
        consume_keyword(KEYWORD_EXPORT);

        expect(TOKEN_KEYWORD);

        struct statement *s;

        if (tok()->keyword == KEYWORD_LET) {
                s = parse_let_definition();
        } else {
                s = parse_function_def();
        }

        s->pub = true;

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
        consume(TOKEN_IDENTIFIER);

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

        // TODO: maybe make 'as' an actual keyword
        if (tok()->type == TOKEN_IDENTIFIER && strcmp(tok()->identifier, "as") == 0) {
                consume(TOKEN_IDENTIFIER);
                expect(TOKEN_IDENTIFIER);
                s->import.as = tok()->identifier;
                consume(TOKEN_IDENTIFIER);
        } else {
                s->import.as = s->import.module;
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
        case TOKEN_KEYWORD:  goto keyword;
        default:             goto expression;
        }

keyword:

        switch (tok()->keyword) {
        case KEYWORD_TAG:      return parse_tag_def();
        case KEYWORD_FOR:      return parse_for_loop();
        case KEYWORD_WHILE:    return parse_while_loop();
        case KEYWORD_IF:       return parse_if_statement();
        case KEYWORD_FUNCTION: return parse_function_def();
        case KEYWORD_MATCH:    return parse_match_statement();
        case KEYWORD_RETURN:   return parse_return_statement();
        case KEYWORD_LET:      return parse_let_definition();
        case KEYWORD_EXPORT:   return parse_export();
        case KEYWORD_BREAK:    return parse_break_statement();
        case KEYWORD_CONTINUE: return parse_continue_statement();
        default:               goto expression;
        }

expression:

        s = mkstmt();
        s->type = STATEMENT_EXPRESSION;
        s->expression = parse_expr(0);
        consume(';');

        return s;
}

char const *
parse_error(void)
{
        return errbuf;
}

struct statement **
parse(char const *source)
{
        vec(struct statement *) program;
        vec_init(program);

        depth = 0;

        vec_init(tokens);
        tokidx = 0;
        lex_ctx = LEX_PREFIX;

        lex_init();
        lex_start(source);

        if (setjmp(jb) != 0) {
                vec_empty(program);
                lex_end();
                return NULL;
        }

        while (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IMPORT) {
                vec_push(program, parse_import());
        }
        while (tok()->type != TOKEN_END) {
                vec_push(program, parse_statement());
        }

        vec_push(program, NULL);

        lex_end();

        return program.items;
}

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
        claim(s->expression->right->type == EXPRESSION_OBJECT);
        claim(s->expression->right->keys.count == 0);
        claim(s->expression->right->values.count == 0);

        s = parse("1 + {4 + 3: 'test'};")[0];
        claim(s->type == STATEMENT_EXPRESSION);
        claim(s->expression->type == EXPRESSION_PLUS);
        claim(s->expression->right->type == EXPRESSION_OBJECT);
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
        claim(s->value->body->return_value->type == EXPRESSION_PLUS);
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
