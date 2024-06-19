#include <setjmp.h>
#include <stdarg.h>
#include <string.h>
#include <ctype.h>
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
#include "compiler.h"
#include "value.h"
#include "table.h"
#include "log.h"
#include "vm.h"

#define BINARY_OPERATOR(name, t, prec, right_assoc) \
        static struct expression * \
        infix_ ## name(struct expression *left) \
        { \
                struct expression *e = mkexpr(); \
                next(); \
                e->type = EXPRESSION_ ## t; \
                e->left = left; \
                e->right = parse_expr(prec - (right_assoc ? 1 : 0)); \
                e->start = left->start; \
                e->end = token(-1)->end; \
                return e; \
        } \

#define BINARY_LVALUE_OPERATOR(name, t, prec, right_assoc) \
        static struct expression * \
        infix_ ## name(struct expression *left) \
        { \
                struct expression *e = mkexpr(); \
                consume(TOKEN_ ## t); \
                e->type = EXPRESSION_ ## t; \
                e->target = assignment_lvalue(left); \
                e->value = parse_expr(prec - (right_assoc ? 1 : 0)); \
                e->start = e->target->start; \
                e->end = e->value->end; \
                return e; \
        } \

#define PREFIX_OPERATOR(name, token, prec) \
        static struct expression * \
        prefix_ ## name(void) \
        { \
                struct expression *e = mkexpr(); \
                consume(TOKEN_ ## token); \
                e->type = EXPRESSION_PREFIX_ ## token; \
                e->operand = parse_expr(prec); \
                e->end = e->operand->end; \
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
                e->end = End; \
                return e; \
        } \

typedef struct expression *parse_fn();

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

typedef vec(struct token) TokenVector;

static jmp_buf jb;

static struct table uops;
static struct table uopcs;

static LexState CtxCheckpoint;
static TokenVector tokens;

static expression_vector TemplateExprs;

static int TokenIndex = 0;
LexContext lctx = LEX_PREFIX;

static struct location EStart;
static struct location EEnd;

static struct location End;

static int depth;
static bool NoEquals = false;
static bool NoIn = false;
static bool NoPipe = false;

static struct expression WildCard = {
        .type = EXPRESSION_IDENTIFIER,
        .identifier = "_"
};

// Maybe try to use this instead, might be cleaner.
/*
static enum {
        PC_NORMAL,
        PC_LVALUE,
        PC_MATCH_PATTERN
} ParseContext = PC_NORMAL;

#define SAVE_PC(e) int PCSave = ParseContext; ParseContext = (e);
#define LOAD_PC(e) ParseContext = PCSave;
*/

#define SAVE_NE(b) bool NESave = NoEquals; NoEquals = (b);
#define SAVE_NC(b) bool NCSave = NoConstraint; NoConstraint = (b);
#define SAVE_NI(b) bool NISave = NoIn; NoIn = (b);
#define SAVE_NP(b) bool NPSave = NoPipe; NoPipe = (b);

#define LOAD_NE() NoEquals = NESave;
#define LOAD_NC() NoConstraint = NCSave;
#define LOAD_NI() NoIn = NISave;
#define LOAD_NP() NoPipe = NPSave;

static char const *filename;

noreturn static void
error(char const *fmt, ...);

static void
logctx(void);

static parse_fn *
get_infix_parser(void);

static parse_fn *
get_prefix_parser(void);

static struct statement *
parse_statement(int);

static struct expression *
parse_expr(int);

static struct statement *
parse_match_statement(void);

static struct statement *
parse_if(void);

static struct statement *
parse_while(void);

static struct statement *
parse_try(void);

static struct statement *
parse_for_loop(void);

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

static struct expression *
prefix_function(void);

static struct expression *
prefix_dict(void);

static struct expression *
prefix_implicit_lambda(void);

inline static struct token *
tok(void);

inline static struct token *
token(int i);

char *
mksym(int s)
{
        char b[32];

        snprintf(b, sizeof b - 1, ":%d", s);
        return sclonea(b);
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
        struct expression *e = Allocate(sizeof *e);
        e->constraint = NULL;
        e->is_method = false;
        e->symbolized = false;
        e->has_resources = false;
        e->start = tok()->start;
        e->end = tok()->end;
        return e;
}

inline static struct expression *
mkfunc(void)
{
        struct expression *f = mkexpr();

        static _Thread_local int t = -1;

        f->type = EXPRESSION_FUNCTION;
        f->rest = -1;
        f->ikwargs = -1;
        f->return_type = NULL;
        f->ftype = FT_NONE;
        f->name = NULL;
        f->doc = NULL;
        f->proto = NULL;
        f->body = NULL;
        f->has_defer = false;
        f->is_overload = false;
        f->t = ++t;

        vec_init(f->params);
        vec_init(f->dflts);
        vec_init(f->constraints);
        vec_init(f->decorators);
        vec_init(f->functions);

        return f;
}

inline static struct statement *
mkstmt(void)
{
        struct statement *s = Allocate(sizeof *s);
        s->start = tok()->start;
        s->end = tok()->start;
        return s;
}

inline static struct statement *
mkret(struct expression *value)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);
        VPush(s->returns, value);
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
        s->pub = false;
        s->target = lvalue;
        s->value = value;
        s->value = value;

        return s;
}

inline static struct token *
token(int i)
{
        struct token t;
        while (tokens.count <= i + TokenIndex) {
                if (tokens.count == TokenIndex) {
                        lex_save(&CtxCheckpoint);
                }
                t = lex_token(lctx);
                LOG("Adding tokens[%d] = %s", (int)tokens.count, token_show(&t));
                VPush(tokens, t);
        }

        LOG("tokens[%d] = %s", TokenIndex + i, token_show(&tokens.items[TokenIndex + i]));

        return &tokens.items[TokenIndex + i];
}

inline static struct token *
tok(void)
{
        return token(0);
}

inline static void
skip(int n)
{
        TokenIndex += n;
        End = token(-1)->end;
        EStart = tok()->start;
        EEnd = tok()->end;
}

inline static void
next(void)
{
        skip(1);
}

inline static void
seek(int i)
{
        TokenIndex = i;
        skip(0);
}

void
parse_sync_lex(void)
{
        if (TokenIndex > 0 && TokenIndex < tokens.count) {
                tokens.count = TokenIndex;
                lex_rewind(&token(-1)->end);
        }
}

inline static void
setctx(int ctx)
{
        if (lctx == ctx)
                return;

        if (tok()->ctx == LEX_FAKE)
                return;

        lctx = ctx;

        bool next_nl = tok()->type == TOKEN_NEWLINE;

        LOG("Rewinding to: %.*s...  TokenIndex=%d\n", (int)strcspn(tok()->start.s, "\n"), tok()->start.s, TokenIndex);

        struct location start = tok()->start;
        lex_rewind(&start);

        if (next_nl)
                lex_need_nl();

        // TODO: Should we be discarding LEX_FAKE tokens? (i.e. tokens that were unconsume()d)

        while (tokens.count > TokenIndex) {
                LOG("Popping tokens[%zu]: %s\n", tokens.count - 1, token_show(vec_last(tokens)));
                tokens.count -= 1;
        }

        while (tokens.count > 0 && vec_last(tokens)->start.s == start.s) {
                LOG("Popping tokens[%zu]: %s\n", tokens.count - 1, token_show(vec_last(tokens)));
                tokens.count -= 1;
        }

        // TODO: ???
        if (TokenIndex > tokens.count) {
                TokenIndex = tokens.count;
        }

        logctx();
}

static void
logctx(void)
{
#if 0
        tok();

        int lo = max(0, TokenIndex - 3);
        int hi = tokens.count - 1;

        fprintf(stderr, "Lex context: %-6s    ", lctx == LEX_PREFIX ? "prefix" : "infix");

        for (int i = lo; i <= hi; ++i) {
                if (i == TokenIndex) {
                        fprintf(stderr, "  %s[%s]%s", TERM(92), token_show(&tokens.items[i]), TERM(0));
                } else {
                        fprintf(stderr, "  [%s]", token_show(&tokens.items[i]));
                }
        }

        char const *ahead = lex_pos().s;

        fprintf(stderr, ": %.*s\n\n", (int)strcspn(ahead, "\n"), ahead);
#endif
}


/*
 * Push a token into the token stream, so that it will be returned by the next call
 * to tok().
 */
inline static void
unconsume(int type)
{
        struct token t = {
                .type = type,
                .start = End,
                .end = End,
                .ctx = LEX_FAKE
        };

        LOG("Inserting tokens[%d] = %s", TokenIndex, token_show(&t));

        logctx();

        VInsert(tokens, t, TokenIndex);
}

noreturn static void
error(char const *fmt, ...)
{
        if (fmt == NULL)
                goto End;

        if (tok()->type == TOKEN_ERROR) {
                /*
                 * The lexer already wrote an error message into ERR
                 */
                goto End;
        }

        va_list ap;
        va_start(ap, fmt);

        int sz = ERR_SIZE - 1;
        char *err = ERR;
        int n = snprintf(ERR, sz, "%s%sParseError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));

        n += vsnprintf(err + n, sz - n, fmt, ap);
        va_end(ap);

        struct location start = EStart;
        struct location end = EEnd;

        char buffer[512];

        snprintf(
                buffer,
                sizeof buffer - 1,
                "%36s %s%s%s:%s%d%s:%s%d%s",
                "at",
                TERM(34),
                filename,
                TERM(39),
                TERM(33),
                start.line + 1,
                TERM(39),
                TERM(33),
                start.col + 1,
                TERM(39)
        );

        char const *where = buffer;
        int m = strlen(buffer) - 6*strlen(TERM(00));

        while (m > 36) {
                m -= 1;
                where += 1;
        }

        n += snprintf(
                ERR + n,
                sz - n,
                "\n\n%s near: ",
                where
        );

        if (tok()->type == TOKEN_END) {
                while ((start.s[0] == '\0' || isspace(start.s[0])) && start.s[-1] != '\0') {
                        start.s -= 1;
                }
                end.s = start.s;
        }

        char const *prefix = start.s;

        while (prefix[-1] != '\0' && prefix[-1] != '\n')
                --prefix;

        while (isspace(prefix[0]))
                ++prefix;

        int before = start.s - prefix;
        int length = end.s - start.s;
        int after = strcspn(end.s, "\n");

        n += snprintf(
                ERR + n,
                sz - n,
                "%s%.*s%s%s%.*s%s%s%.*s%s",
                TERM(32),
                before,
                prefix,
                TERM(1),
                TERM(91),
                length,
                start.s,
                TERM(32),
                TERM(22),
                after,
                end.s,
                TERM(39)
        );

        n += snprintf(
                ERR + n,
                sz - n,
                "\n\t%*s%s%s",
                before + 35,
                "",
                TERM(1),
                TERM(91)
        );

        for (int i = 0; i < length && n < sz; ++i)
                ERR[n++] = '^';

        n += snprintf(
                ERR + n,
                sz - n,
                "%s%s",
                TERM(39),
                TERM(22)
        );


        LOG("Parse Error: %s", ERR);
End:
        longjmp(jb, 1);
}

inline static bool
have_keyword(int kw)
{
        return tok()->type == TOKEN_KEYWORD && tok()->keyword == kw;
}

inline static bool
have_keywords(int kw1, int kw2)
{
        return tok()->type == TOKEN_KEYWORD && tok()->keyword == kw1 &&
               token(1)->type == TOKEN_KEYWORD && token(1)->keyword == kw2;
}

static bool
have_not_in(void)
{
        return tok()->type == TOKEN_KEYWORD &&
               tok()->keyword == KEYWORD_NOT &&
               token(1)->type == TOKEN_KEYWORD &&
               token(1)->keyword == KEYWORD_IN;
}

static void
expect(int type)
{
        if (tok()->type != type) {
                error(
                        "expected %s but found %s%s%s",
                        token_show_type(type),
                        TERM(34),
                        token_show(tok()),
                        TERM(0)
                );
        }
}


static void
expect_keyword(int type)
{
        if (tok()->type != TOKEN_KEYWORD || tok()->keyword != type) {
                error(
                        "expected %s but found %s%s%s",
                        token_show(&(struct token){ .type = TOKEN_KEYWORD, .keyword = type }),
                        TERM(34),
                        token_show(tok()),
                        TERM(0)
                );
        }
}

inline static void
consume(int type)
{
        expect(type);
        next();
}

inline static void
consume_keyword(int type)
{
        expect_keyword(type);
        next();
}

inline static struct expression *
try_cond(void)
{
        if (have_keyword(KEYWORD_IF)) {
                next();
                return parse_expr(0);
        } else {
                return NULL;
        }
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

        e->fmts.items = tok()->fmts.items;
        e->fmts.count = tok()->fmts.count;
        vec_init(e->fmts);

        LexState *exprs = tok()->expressions.items;
        int count = tok()->expressions.count;

        consume(TOKEN_SPECIAL_STRING);

        int ti = TokenIndex;
        LexState cp = CtxCheckpoint;
        TokenVector ts = tokens;

        for (int i = 0; i < count; ++i) {
                TokenIndex = 0;
                vec_init(tokens);
                lex_start(&exprs[i]);
                lex_save(&CtxCheckpoint);
                VPush(e->expressions, parse_expr(0));
                (*vec_last(e->expressions))->end = End;
                setctx(LEX_FMT);
                if (tok()->type == TOKEN_STRING) {
                        VPush(e->fmts, tok()->string);
                        next();
                } else {
                        VPush(e->fmts, NULL);
                }
                consume(TOKEN_END);
                lex_end();
        }

        TokenIndex = ti;
        CtxCheckpoint = cp;
        tokens = ts;

        // Force lexer reset
        setctx(LEX_PREFIX);
        setctx(LEX_INFIX);

        return e;
}

static struct expression *
prefix_hash(void)
{
        struct expression *e = mkexpr();

        consume('#');

        e->type = EXPRESSION_PREFIX_HASH;
        e->operand = parse_expr(10);
        e->end = End;

        return e;
}

static struct expression *
prefix_dollar(void)
{
        if (token(1)->type == '{') {
                return prefix_implicit_lambda();
        }

        struct expression *e = mkexpr();

        consume('$');
        setctx(LEX_INFIX);

        expect(TOKEN_IDENTIFIER);

        e->type = EXPRESSION_MATCH_NOT_NIL;
        e->identifier = tok()->identifier;
        e->module = tok()->module;

        if (e->module != NULL)
                error("unpexpected module in lvalue");

        consume(TOKEN_IDENTIFIER);

        e->end = End;

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

        if (true && is_macro(e)) {
                return typarse(e, &e->start, &token(-1)->end);
        }

        // Is this a macro invocation?
        if (strchr(e->identifier, '$') != NULL) {
                e->identifier = sclonea(e->identifier);
                *strchr(e->identifier, '$') = '\0';
                struct expression *macro = mkexpr();
                macro->type = EXPRESSION_MACRO_INVOCATION;
                macro->macro.m = e;
                macro->macro.e = mkexpr();
                macro->macro.e->type = EXPRESSION_STATEMENT;
                macro->macro.e->statement = parse_statement(0);
                macro->start = e->start;
                macro->end = End;
                return macro;
        }

        // TODO: maybe get rid of this
        if (NoEquals && tok()->type == ':') {
                next();
                e->constraint = parse_expr(0);
        } else {
                e->constraint = NULL;
        }

        e->end = End;

        return e;
}

static struct expression *
prefix_eval(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_EVAL;
        next();
        consume('(');
        e->operand = parse_expr(0);
        consume(')');
        e->end = End;
        return e;
}

static struct expression *
prefix_defined(void)
{
        struct expression *e;
        struct location start = tok()->start;

        next();
        consume('(');

        if (tok()->type != TOKEN_IDENTIFIER || token(1)->type != ')') {
                consume(TOKEN_IDENTIFIER);
                consume(')');
                // unreachable
        }

        e = parse_expr(0);
        e->type = EXPRESSION_DEFINED;

        consume(')');

        e->start = start;
        e->end = End;

        return e;
}

static struct expression *
prefix_function(void)
{
        struct expression *e = mkfunc();

        if (tok()->type == TOKEN_AT) {
                consume(TOKEN_AT);
                consume('[');

                while (tok()->type != ']') {
                        struct expression *f = parse_expr(0);
                        if (f->type != EXPRESSION_FUNCTION_CALL && f->type != EXPRESSION_METHOD_CALL) {
                                struct expression *call = mkexpr();
                                if (f->type == EXPRESSION_MEMBER_ACCESS) {
                                        call->type = EXPRESSION_METHOD_CALL;
                                        call->sc = NULL;
                                        call->maybe = false;
                                        call->object = f->object;
                                        call->method_name = f->method_name;
                                        vec_init(call->method_args);
                                        vec_init(call->mconds);
                                        vec_init(call->method_kwargs);
                                        vec_init(call->method_kws);
                                } else {
                                        call->type = EXPRESSION_FUNCTION_CALL;
                                        call->function = f;
                                        vec_init(call->args);
                                        vec_init(call->kws);
                                        vec_init(call->kwargs);
                                        vec_init(call->fconds);
                                        vec_init(call->fkwconds);
                                }
                                vec_push(e->decorators, call);
                        } else {
                                vec_push(e->decorators, f);
                        }

                        if (tok()->type == ',') {
                                next();
                        }
                }

                consume(']');
        }

        if (tok()->keyword == KEYWORD_GENERATOR) {
                e->type = EXPRESSION_GENERATOR;
        } else {
                e->type = EXPRESSION_FUNCTION;
        }

        next();

        if (e->type == EXPRESSION_GENERATOR)
                goto Body;

        bool sugared_generator = false;

        if (tok()->type == TOKEN_IDENTIFIER) {
                e->name = tok()->identifier;
                next();
        }

        if (tok()->type == TOKEN_STAR) {
                sugared_generator = true;
                next();
        }

        char const *proto_start = tok()->start.s;

        consume('(');

        SAVE_NE(true);

        while (tok()->type != ')') {
                setctx(LEX_PREFIX);

                bool special = false;

                if (tok()->type == TOKEN_STAR) {
                        next();
                        e->rest = e->params.count;
                        special = true;
                } else if (tok()->type == TOKEN_PERCENT) {
                        next();
                        e->ikwargs = e->params.count;
                        special = true;
                }

                expect(TOKEN_IDENTIFIER);
                VPush(e->params, tok()->identifier);
                next();

                if (!special && tok()->type == ':') {
                        next();
                        VPush(e->constraints, parse_expr(0));
                        (*vec_last(e->constraints))->end = End;
                } else {
                        VPush(e->constraints, NULL);
                }

                if (!special && tok()->type == TOKEN_EQ) {
                        next();
                        VPush(e->dflts, parse_expr(0));
                        (*vec_last(e->dflts))->end = End;
                } else {
                        VPush(e->dflts, NULL);
                }

                if (tok()->type == ',') {
                        next();
                }
        }

        LOAD_NE();

        consume(')');

        // Optional return value constraint
        if (tok()->type == TOKEN_ARROW) {
                next();
                e->return_type = parse_expr(0);
        }

        char const *proto_end = End.s;
        size_t proto_len = proto_end - proto_start;
        char *proto = Allocate(proto_len + 1);
        memcpy(proto, proto_start, proto_len);
        proto[proto_len] = '\0';
        e->proto = proto;

        if (sugared_generator) {
                unconsume(TOKEN_KEYWORD);
                tok()->keyword = KEYWORD_GENERATOR;
        }

Body:
        e->body = parse_statement(-1);

        return e;
}

/* rewrite [ op ] as ((a, b) -> a op b) */
static struct expression *
opfunc(void)
{
        struct location start = tok()->start;

        consume('[');

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
        e->start = start;

        return e;
}

static struct expression *
prefix_at(void)
{
        if (token(1)->type == '[')
                return prefix_function();

        next();

        if (tok()->type == '{') {
                next();

                if (token(1)->type == '}') {
                        struct token id = *tok();

                        next();
                        unconsume(')');
                        unconsume('(');

                        unconsume(TOKEN_IDENTIFIER);
                        *tok() = id;
                }

                struct expression *m = parse_expr(0);

                if (m->type != EXPRESSION_FUNCTION_CALL) {
                        EStart = m->start;
                        EEnd = m->end;
                        error("expected function-like macro invocation inside @{...}");
                }

                consume('}');

                VPush(m->args, parse_expr(0));
                VPush(m->aconds, NULL);

                return m;
        } else {
                unconsume('.');

                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = "self";
                tok()->module = NULL;

                return prefix_identifier();
        }
}



static struct expression *
prefix_star(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_MATCH_REST;
        e->module = NULL;

        consume(TOKEN_STAR);

        if (tok()->type == TOKEN_IDENTIFIER) {
                e->identifier = tok()->identifier;

                if (tok()->module != NULL)
                        error("unexpected module qualifier in lvalue");

                next();
        } else {
                e->identifier = "_";
        }

        e->end = End;

        return e;
}

static struct expression *
prefix_statement(void)
{
        struct expression *e = mkexpr();

        e->type = EXPRESSION_STATEMENT;
        e->statement = parse_statement(-1);
        e->end = e->statement->end;

        return e;
}

static struct expression *
prefix_record(void)
{
        struct location start = tok()->start;
        struct expression *e = mkexpr();
        e->only_identifiers = false;
        e->type = EXPRESSION_TUPLE;
        vec_init(e->es);
        vec_init(e->names);
        vec_init(e->required);
        vec_init(e->tconds);

        consume('{');

        while (tok()->type != '}') {
                setctx(LEX_PREFIX);

                if (tok()->type == TOKEN_QUESTION) {
                        next();
                        VPush(e->required, false);
                } else {
                        VPush(e->required, true);
                }

                if (tok()->type == TOKEN_STAR) {
                        struct expression *item = mkexpr();
                        next();
                        if (tok()->type == '}') {
                                item->type = EXPRESSION_MATCH_REST;
                                item->identifier = "_";
                                item->module = NULL;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                                item->value = parse_expr(0);
                                item->end = End;
                        }
                        VPush(e->names, "*");
                        VPush(e->es, item);
                        goto Next;
                }

                expect(TOKEN_IDENTIFIER);
                VPush(e->names, tok()->identifier);

                if (token(1)->type == ':') {
                        next();
                        next();
                } else if (
                        token(1)->type != ',' && token(1)->type != '}' &&
                        (token(1)->type != TOKEN_KEYWORD || token(1)->keyword != KEYWORD_IF)
                ) {
                        // Force a parse error
                        next();
                        expect(':');
                }

                VPush(e->es, parse_expr(0));

Next:
                if (have_keyword(KEYWORD_IF)) {
                        next();
                        VPush(e->tconds, parse_expr(0));
                } else {
                        VPush(e->tconds, NULL);
                }
                if (tok()->type == ',') {
                        next();
                }
        }

        consume('}');

        return e;
}

static struct expression *
next_pattern(void)
{
        SAVE_NE(true);

        struct expression *p = parse_expr(0);
        p->end = End;

        if (false && p->type == EXPRESSION_IDENTIFIER && tok()->type == ':') {
                next();
                p->constraint = parse_expr(0);
                p->constraint->end = End;
        }

        LOAD_NE();

        return p;
}

static struct expression *
parse_pattern(void)
{
        struct expression *pattern = next_pattern();

        if (tok()->type == ',') {
                struct expression *p = mkexpr();

                p->type = EXPRESSION_LIST;
                p->start = pattern->start;

                vec_init(p->es);
                VPush(p->es, pattern);

                while (tok()->type == ',') {
                        next();
                        VPush(p->es, next_pattern());
                }

                p->end = (*vec_last(p->es))->end;

                pattern = p;
        }

        return pattern;
}

static struct expression *
parse_block_expr(void)
{
        expect('{');

        struct statement *s = parse_statement(0);
        struct expression *e = mkexpr();
        e->type = EXPRESSION_STATEMENT;
        e->statement = s;
        e->start = s->start;
        e->end = s->end;

        return e;
}

void
make_with(struct expression *e, statement_vector defs, struct statement *body)
{
        e->type = EXPRESSION_WITH;

        e->with.defs = defs;

        struct statement *try = mkstmt();
        try->type = STATEMENT_TRY;
        vec_init(try->try.patterns);
        vec_init(try->try.handlers);
        try->try.s = body;

        try->try.finally = mkstmt();
        try->try.finally->type = STATEMENT_DROP;
        vec_init(try->try.finally->drop);

        struct statement *s = mkstmt();
        s->type = STATEMENT_MULTI;
        vec_init(s->statements);
        VPushN(s->statements, defs.items, defs.count);
        VPush(s->statements, try);
        e->with.block = s;
}

static struct expression *
prefix_do(void)
{
        // do
        next();
        return prefix_statement();
}

static struct expression *
prefix_with(void)
{
        struct expression *with = mkexpr();
        statement_vector defs = {0};

        // with / use
        next();

        for (;;) {
            SAVE_NE(true);
            struct expression *e = parse_expr(0);
            LOAD_NE();

            struct statement *def = mkstmt();
            def->type = STATEMENT_DEFINITION;
            def->pub = false;

            if (tok()->type == TOKEN_EQ) {
                    next();
                    def->target = definition_lvalue(e);
                    def->value = parse_expr(0);
            } else {
                    struct expression *t = mkexpr();
                    t->type = EXPRESSION_IDENTIFIER;
                    t->identifier = gensym();
                    t->module = NULL;
                    def->target = t;
                    def->value = e;
            }

            VPush(defs, def);

            if (tok()->type == ',') {
                    next();
            } else {
                break;
            }
        }

        make_with(with, defs, parse_statement(0));

        with->end = End;

        return with;
}

static struct expression *
prefix_yield(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_YIELD;
        vec_init(e->es);

        consume_keyword(KEYWORD_YIELD);

        VPush(e->es, parse_expr(1));
        while (tok()->type == ',') {
                next();
                VPush(e->es, parse_expr(1));
        }

        e->end = End;

        return e;
}

static struct expression *
prefix_match(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_MATCH;

        consume_keyword(KEYWORD_MATCH);

        e->subject = parse_expr(-1);
        e->end = e->subject->end = End;

        consume('{');

        vec_init(e->patterns);
        vec_init(e->thens);

        VPush(e->patterns, parse_pattern());

        consume(TOKEN_FAT_ARROW);
        if (tok()->type == '{') {
                VPush(e->thens, parse_block_expr());
        } else {
                VPush(e->thens, parse_expr(0));
        }

        while (tok()->type == ',') {
                next();

                // Trailing comma is allowed
                if (tok()->type == '}') {
                        break;
                }

                VPush(e->patterns, parse_pattern());
                consume(TOKEN_FAT_ARROW);
                if (tok()->type == '{') {
                        VPush(e->thens, parse_block_expr());
                } else {
                        VPush(e->thens, parse_expr(0));
                }
        }

        consume('}');

        return e;
}

static struct expression *
gencompr(struct expression *e)
{
        next();
        struct expression *target = parse_target_list();
        consume_keyword(KEYWORD_IN);
        struct expression *iter = parse_expr(0);
        struct expression *g = mkfunc();
        g->start = e->start;
        g->type = EXPRESSION_GENERATOR;
        g->body = mkstmt();
        g->body->type = STATEMENT_EACH_LOOP;
        if (have_keyword(KEYWORD_IF)) {
                next();
                g->body->each.cond = parse_expr(0);
        } else {
                g->body->each.cond = NULL;
        }
        if (have_keyword(KEYWORD_WHILE)) {
                next();
                g->body->each.stop = parse_expr(0);
        } else {
                g->body->each.stop = NULL;
        }
        g->body->each.target = target;
        g->body->each.array = iter;
        g->body->each.body = mkstmt();
        g->body->each.body->type = STATEMENT_EXPRESSION;
        g->body->each.body->expression = mkexpr();
        g->body->each.body->expression->type = EXPRESSION_YIELD;
        vec_init(g->body->each.body->expression->es);
        VPush(g->body->each.body->expression->es, e);
        g->end = End;
        return g;
}

static struct expression *
prefix_parenthesis(void)
{
        /*
         * This can either be a plain old parenthesized expression, e.g., (4 + 4)
         * or it can be an identifier list for an arrow function, e.g., (a, b, c).
         */

        struct location start = tok()->start;
        struct expression *e;

        consume('(');

        /*
         * () is an empty identifier list.
         */
        if (tok()->type == ')') {
                next();
                e = mkexpr();
                e->start = start;
                e->type = EXPRESSION_TUPLE;
                e->only_identifiers = true;
                vec_init(e->es);
                vec_init(e->names);
                vec_init(e->required);
                vec_init(e->tconds);
                return e;
        }

        /*
         * If we have an infix operator that cannot also be a prefix
         * operator, assume this is an operator section.
         */
        if (get_infix_parser() != NULL && get_prefix_parser() == NULL) {
                e = mkfunc();
                VPush(e->params, gensym());
                VPush(e->dflts, NULL);
                VPush(e->constraints, NULL);

                struct expression *t = mkexpr();
                t->type = EXPRESSION_IDENTIFIER;
                t->identifier = e->params.items[0];
                t->module = NULL;

                e->body = mkstmt();
                e->body->type = STATEMENT_EXPRESSION;
                e->body->expression = get_infix_parser()(t);

                consume(')');

                return e;
        }

        // (:a, ...)
        if (tok()->type == ':' && token(1)->type == TOKEN_IDENTIFIER) {
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = token(2)->identifier;
                tok()->module = NULL;
        }

        SAVE_NE(false);
        e = parse_expr(0);
        LOAD_NE();

        if (e->type == EXPRESSION_EQ || e->type == EXPRESSION_MAYBE_EQ) {
                expect(')');
        }

        if (tok()->type == ',' || tok()->type == ':') {
                struct expression *list = mkexpr();
                list->start = start;
                list->only_identifiers = true;

                /*
                 * It _must_ be an identifier list.
                 *
                 * ^ idk what i meant by this
                 */
                if (e->type != EXPRESSION_IDENTIFIER && e->type != EXPRESSION_MATCH_REST) {
                        list->only_identifiers = false;
                }

                list->type = EXPRESSION_TUPLE;
                vec_init(list->names);
                vec_init(list->es);
                vec_init(list->required);
                vec_init(list->tconds);

                if (e->type == EXPRESSION_IDENTIFIER && tok()->type == ':') {
                        next();
                        VPush(list->names, e->identifier);
                        e = parse_expr(0);
                } else {
                        VPush(list->names, NULL);
                }

                e->end = End;
                VPush(list->es, e);
                VPush(list->required, true);

                if (have_keyword(KEYWORD_IF)) {
                        next();
                        VPush(list->tconds, parse_expr(0));
                } else {
                        VPush(list->tconds, NULL);
                }

                while (tok()->type == ',') {
                        next();

                        if (tok()->type == ':' && token(1)->type == TOKEN_IDENTIFIER) {
                                unconsume(TOKEN_IDENTIFIER);
                                tok()->identifier = token(2)->identifier;
                                tok()->module = NULL;
                        }

                        if (tok()->type == TOKEN_QUESTION) {
                                next();
                                VPush(list->required, false);
                        } else {
                                VPush(list->required, true);
                        }

                        if (tok()->type == TOKEN_IDENTIFIER && token(1)->type == ':') {
                                VPush(list->names, tok()->identifier);
                                next();
                                next();
                        } else {
                                VPush(list->names, NULL);
                        }

                        struct expression *e = parse_expr(0);
                        e->end = tok()->end;
                        if (e->type == EXPRESSION_MATCH_REST) {
                                expect(')');
                        } else if (e->type != EXPRESSION_IDENTIFIER) {
                                list->only_identifiers = false;
                        }

                        VPush(list->es, e);

                        if (have_keyword(KEYWORD_IF)) {
                                next();
                                VPush(list->tconds, parse_expr(0));
                        } else {
                                VPush(list->tconds, NULL);
                        }
                }

                consume(')');

                list->end = End;

                return list;
        } else if (have_keyword(KEYWORD_FOR)) {
                e = gencompr(e);
                consume(')');
                return e;
        } else {
                consume(')');

                if (e->type == EXPRESSION_TUPLE) {
                        struct expression *list = mkexpr();
                        list->start = start;
                        list->only_identifiers = false;
                        list->type = EXPRESSION_TUPLE;
                        vec_init(list->names);
                        vec_init(list->es);
                        vec_init(list->tconds);
                        vec_init(list->required);
                        VPush(list->names, NULL);
                        VPush(list->required, true);
                        VPush(list->es, e);
                        VPush(list->tconds, NULL);
                        return list;
                } else {
                        e->start = start;
                        e->end = End;
                        return e;
                }
        }
}

static struct expression *
prefix_true(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_BOOLEAN;
        e->boolean = true;

        consume_keyword(KEYWORD_TRUE);

        return e;
}

static struct expression *
prefix_false(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_BOOLEAN;
        e->boolean = false;

        consume_keyword(KEYWORD_FALSE);

        return e;
}

static struct expression *
prefix_self(void)
{

        struct expression *e = mkexpr();
        e->type = EXPRESSION_SELF;

        consume_keyword(KEYWORD_SELF);

        return e;
}

static struct expression *
prefix_nil(void)
{

        struct expression *e = mkexpr();
        e->type = EXPRESSION_NIL;

        consume_keyword(KEYWORD_NIL);

        return e;
}

static struct expression *
prefix_regex(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_REGEX;
        e->regex = tok()->regex;

        consume(TOKEN_REGEX);

        return e;
}


static struct expression *
prefix_array(void)
{
        setctx(LEX_INFIX);

        if (token(2)->type == ']') switch (token(1)->type) {
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
        case TOKEN_CHECK_MATCH:
        case TOKEN_DOT_DOT:
        case TOKEN_DOT_DOT_DOT:
        case TOKEN_LT:
        case TOKEN_GT:
        case TOKEN_LEQ:
        case TOKEN_GEQ:
        case TOKEN_NOT_EQ:
        case TOKEN_DBL_EQ:
        case '|':
        case '&':
                return opfunc();
        default: break;
        }

        struct expression *e, *f;

        struct location start = tok()->start;

        int in_type = EXPRESSION_IN;

        if (token(1)->type == TOKEN_KEYWORD) switch (token(1)->keyword) {
        case KEYWORD_IN:
        InSection:
                next();
                next();
                e = parse_expr(0);
                consume(']');
                f = mkfunc();
                VPush(f->params, gensym());
                VPush(f->dflts, NULL);
                VPush(f->constraints, NULL);
                f->body = mkstmt();
                f->body->type = STATEMENT_EXPRESSION;
                f->body->expression = mkexpr();
                f->body->expression->type = in_type;
                f->body->expression->left = mkexpr();
                f->body->expression->left->type = EXPRESSION_IDENTIFIER;
                f->body->expression->left->identifier = f->params.items[0];
                f->body->expression->left->module = NULL;
                f->body->expression->right = e;
                f->start = start;
                f->end = End;
                return f;
        case KEYWORD_NOT:
                next();
                if (token(1)->type == TOKEN_KEYWORD && token(1)->keyword == KEYWORD_IN) {
                        in_type = EXPRESSION_NOT_IN;
                        goto InSection;
                }
                break;
        }

        e = mkexpr();
        e->type = EXPRESSION_ARRAY;
        vec_init(e->elements);
        vec_init(e->aconds);
        vec_init(e->optional);

        consume('[');

        while (tok()->type != ']') {
                setctx(LEX_PREFIX);
                if (tok()->type == TOKEN_STAR) {
                        struct expression *item = mkexpr();
                        next();
                        if (tok()->type == ']') {
                                item->type = EXPRESSION_MATCH_REST;
                                item->identifier = "_";
                                item->module = NULL;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                                item->value = parse_expr(0);
                                item->end = End;
                        }
                        VPush(e->elements, item);
                        VPush(e->optional, false);
                } else {
                        if (tok()->type == TOKEN_QUESTION) {
                                next();
                                VPush(e->optional, true);
                        } else {
                                VPush(e->optional, false);
                        }
                        VPush(e->elements, parse_expr(0));
                }

                if (have_keyword(KEYWORD_IF)) {
                        next();
                        VPush(e->aconds, parse_expr(0));
                } else {
                        VPush(e->aconds, NULL);
                }

                if (have_keyword(KEYWORD_FOR)) {
                        next();
                        e->type = EXPRESSION_ARRAY_COMPR;
                        e->compr.pattern = parse_target_list();
                        consume_keyword(KEYWORD_IN);
                        e->compr.iter = parse_expr(0);
                        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IF) {
                                next();
                                e->compr.cond = parse_expr(0);
                        } else {
                                e->compr.cond = NULL;
                        }
                        expect(']');
                } else if (tok()->type == ',') {
                        next();
                } else if (
                        e->elements.count == 1 &&
                        get_infix_parser() != NULL &&
                        (token(1)->type == ']' || (have_not_in() && token(2)->type == ']'))
                ) {
                        f = mkfunc();
                        VPush(f->params, gensym());
                        VPush(f->dflts, NULL);
                        VPush(f->constraints, NULL);
                        struct token t = *tok();
                        next();
                        struct token t2 = *tok();
                        if (t2.type != ']') {
                                next();
                        }
                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = f->params.items[0];
                        tok()->module = NULL;
                        if (t2.type != ']') {
                                unconsume(TOKEN_STAR);
                                *tok() = t2;
                        }
                        unconsume(TOKEN_STAR);
                        *tok() = t;
                        f->body = mkstmt();
                        f->body->type = STATEMENT_EXPRESSION;
                        f->body->expression = get_infix_parser()(e->elements.items[0]);
                        consume(']');
                        f->start = start;
                        f->end = End;
                        return f;
                } else {
                        expect(']');
                }
        }

        next();

        e->end = End;

        return e;
}

static struct expression *
prefix_template(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_TEMPLATE;

        next();

        expression_vector TESave = TemplateExprs;
        vec_init(TemplateExprs);
        vec_init(e->template.stmts);

        while (tok()->type != TOKEN_TEMPLATE_END) {
                VPush(e->template.stmts, parse_statement(0));
        }

        next();

        e->end = End;

        e->template.exprs = TemplateExprs;
        TemplateExprs = TESave;

        return e;
}

static struct expression *
prefix_template_expr(void)
{
        next();

        struct expression *e = mkexpr();
        e->type = EXPRESSION_TEMPLATE_HOLE;
        e->integer = TemplateExprs.count;

        if (tok()->type == '(') {
                next();
                VPush(TemplateExprs, parse_expr(0));
                consume(')');
        } else {
                VPush(TemplateExprs, parse_expr(99));
        }

        e->end = vec_last(TemplateExprs)[0]->end;

        return e;
}

static struct expression *
prefix_carat(void)
{
        consume('^');
        struct expression *id = prefix_identifier();
        id->type = EXPRESSION_RESOURCE_BINDING;
        return id;
}

static struct expression *
prefix_tick(void)
{
        struct expression *e;
        struct location start = tok()->start;

        next();

        if (tok()->type != TOKEN_IDENTIFIER || token(1)->type != '`') {
                consume(TOKEN_IDENTIFIER);
                consume('`');
                // unreachable
        }

        e = parse_expr(0);
        e->type = EXPRESSION_IFDEF;

        consume('`');

        e->start = start;
        e->end = End;

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
        e->right = parse_expr(7);
        e->end = e->right->end;

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
        e->right = parse_expr(7);
        e->end = e->right->end;

        return e;
}

static struct expression *
implicit_subscript(struct expression *o)
{
        consume('[');

        struct expression *e = mkexpr();
        e->type = EXPRESSION_SUBSCRIPT;
        e->sc = NULL;
        e->container = o;

        setctx(LEX_PREFIX);
        e->subscript = parse_expr(0);

        consume(']');

        struct expression *f = mkfunc();
        f->body = mkret(e);

        VPush(f->params, o->identifier);
        VPush(f->dflts, NULL);
        VPush(f->constraints, NULL);

        return f;
}

static struct expression *
prefix_implicit_method(void)
{
        consume('&');

        if (tok()->type == '{') {
                return prefix_implicit_lambda();
        }

        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_NOT) {
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = "__not__";
                tok()->module = NULL;
        }

        struct expression *o = mkexpr();
        o->type = EXPRESSION_IDENTIFIER;
        o->identifier = gensym();
        o->module = NULL;

        if (tok()->type == TOKEN_INTEGER) {
                intmax_t k = tok()->integer;
                next();
                unconsume(']');
                unconsume(TOKEN_INTEGER);
                tok()->integer = k;
                unconsume('[');
        }

        if (tok()->type == '[') {
                return implicit_subscript(o);
        }

        bool maybe = false;
        if (tok()->type == TOKEN_QUESTION) {
                next();
                maybe = true;
        }

        struct expression *e = mkexpr();
        e->maybe = false;

        if (tok()->type == '.') {
                next();
                expect(TOKEN_IDENTIFIER);

                e->type = EXPRESSION_MEMBER_ACCESS;
                e->member_name = tok()->identifier;
                e->object = o;

                next();
        } else {
                expect(TOKEN_IDENTIFIER);

                e->type = EXPRESSION_METHOD_CALL;
                e->sc = NULL;
                e->maybe = maybe;
                e->object = o;
                e->method_name = tok()->identifier;
                vec_init(e->method_args);
                vec_init(e->mconds);
                vec_init(e->method_kwargs);
                vec_init(e->method_kws);

                next();

                if (tok()->type == '(') {
                        next();

                        setctx(LEX_PREFIX);

                        if (tok()->type == ')') {
                                next();
                                return e;
                        } else {
                                VPush(e->method_args, parse_expr(0));
                                VPush(e->mconds, try_cond());
                        }

                        while (tok()->type == ',') {
                                next();
                                VPush(e->method_args, parse_expr(0));
                                VPush(e->mconds, try_cond());
                        }

                        consume(')');
                }
        }

        struct expression *f = mkfunc();
        f->body = mkret(e);

        VPush(f->params, o->identifier);
        VPush(f->dflts, NULL);
        VPush(f->constraints, NULL);

        return f;
}

static struct expression *
prefix_implicit_lambda(void)
{
        consume('$');
        consume('{');

        struct expression *e = parse_expr(0);

        consume('}');


        struct expression *f = mkfunc();
        f->type = EXPRESSION_IMPLICIT_FUNCTION;
        f->body = mkstmt();
        f->body->type = STATEMENT_EXPRESSION;
        f->body->expression = e;

        return f;
}

static struct expression *
prefix_bit_or(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_LIST;
        e->only_identifiers = true;
        vec_init(e->es);

        next();

        SAVE_NE(true);
        SAVE_NP(true);
        for (int i = 0; tok()->type != '|'; ++i) {
                struct expression *item = parse_expr(1);
                e->only_identifiers &= (item->type == EXPRESSION_IDENTIFIER);
                VPush(e->es, item);
                if (tok()->type != '|')
                        consume(',');
        }
        LOAD_NE();
        LOAD_NP();

        consume('|');

        e->end = End;

        return e;
}

static struct expression *
prefix_arrow(void)
{
        unconsume(')');
        unconsume('(');

        struct expression *f = parse_expr(0);
        f->type = EXPRESSION_IMPLICIT_FUNCTION;

        return f;
}

static struct expression *
prefix_expr(void)
{
        struct expression *e = tok()->e;
        next();
        return e;
}

static struct expression *
prefix_dict(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_DICT;
        e->dflt = NULL;

        consume(TOKEN_PERCENT);
        consume('{');

        vec_init(e->keys);
        vec_init(e->values);

        while (tok()->type != '}') {
                if (tok()->type == TOKEN_STAR && token(1)->type == ':') {
                        struct location start = tok()->start;
                        next();
                        next();
                        unconsume(TOKEN_ARROW);
                        e->dflt = parse_expr(0);
                        e->dflt->start = start;
                        e->dflt->end = End;
                } else if (tok()->type == TOKEN_STAR) {
                        next();
                        struct expression *spread = mkexpr();
                        spread->type = EXPRESSION_SPREAD;
                        spread->value = parse_expr(0);
                        spread->start = spread->value->start;
                        VPush(e->keys, spread);
                        VPush(e->values, NULL);
                } else {
                        struct expression *key = parse_expr(0);
                        VPush(e->keys, key);
                        if (key->type == EXPRESSION_IDENTIFIER) {
                                VPush(e->values, key->constraint);
                                key->constraint = NULL;
                        } else {
                                VPush(e->values, NULL);
                        }
                        if (tok()->type == ':') {
                                next();
                                *vec_last(e->values) = parse_expr(0);
                        }
                }

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_FOR) {
                        next();
                        e->type = EXPRESSION_DICT_COMPR;
                        e->dcompr.pattern = parse_target_list();
                        consume_keyword(KEYWORD_IN);
                        e->dcompr.iter = parse_expr(0);
                        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IF) {
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

        e->end = End;

        return e;
}

//PREFIX_OPERATOR(at,     AT,       9)
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
        e->start = left->start;
        vec_init(e->args);
        vec_init(e->kws);
        vec_init(e->kwargs);
        vec_init(e->fconds);
        vec_init(e->fkwconds);

        consume('(');

        setctx(LEX_PREFIX);

        if (tok()->type == ')') {
                next();
                e->end = End;
                return e;
        } else {
                if (tok()->type == TOKEN_STAR) {
                        next();
                        struct expression *arg = mkexpr();
                        if (tok()->type == TOKEN_STAR) {
                                next();
                                arg->type = EXPRESSION_SPLAT;
                        } else {
                                arg->type = EXPRESSION_SPREAD;
                        }
                        arg->value = parse_expr(0);
                        arg->start = arg->value->start;
                        if (arg->type == EXPRESSION_SPLAT) {
                                VPush(e->kwargs, arg);
                                VPush(e->kws, "*");
                                VPush(e->fkwconds, NULL);
                        } else {
                                VPush(e->args, arg);
                                VPush(e->fconds, try_cond());
                        }
                } else if (tok()->type == TOKEN_IDENTIFIER && token(1)->type == ':') {
                        VPush(e->kws, tok()->identifier);
                        next();
                        next();
                        VPush(e->kwargs, parse_expr(0));
                        VPush(e->fkwconds, NULL);
                } else {
                        VPush(e->args, parse_expr(0));
                        VPush(e->fconds, try_cond());
                }
                if (have_keyword(KEYWORD_FOR)) {
                        *vec_last(e->args) = gencompr(*vec_last(e->args));
                }
        }

        while (tok()->type == ',') {
                next();
                setctx(LEX_PREFIX);
                if (tok()->type == TOKEN_STAR) {
                        next();
                        struct expression *arg = mkexpr();
                        if (tok()->type == TOKEN_STAR) {
                                next();
                                arg->type = EXPRESSION_SPLAT;
                        } else {
                                arg->type = EXPRESSION_SPREAD;
                        }
                        arg->value = parse_expr(0);
                        arg->start = arg->value->start;
                        if (arg->type == EXPRESSION_SPLAT) {
                                VPush(e->kwargs, arg);
                                VPush(e->kws, "*");
                                VPush(e->fkwconds, NULL);
                        } else {
                                VPush(e->args, arg);
                                VPush(e->fconds, try_cond());
                        }
                } else if (tok()->type == TOKEN_IDENTIFIER && token(1)->type == ':') {
                        VPush(e->kws, tok()->identifier);
                        next();
                        next();
                        VPush(e->kwargs, parse_expr(0));
                        VPush(e->fkwconds, NULL);
                } else {
                        VPush(e->args, parse_expr(0));
                        VPush(e->fconds, try_cond());
                }
        }

        consume(')');

        e->end = End;

        return e;
}

static struct expression *
infix_eq(struct expression *left)
{
        struct expression *e = mkexpr();

        e->type = tok()->type == TOKEN_EQ ? EXPRESSION_EQ : EXPRESSION_MAYBE_EQ;
        next();

        e->start = left->start;
        e->target = assignment_lvalue(left);

        if (left->type == EXPRESSION_LIST) {
                e->value = parse_expr(-1);
        } else {
                e->value = parse_expr(1);
        }

        e->end = e->value->end;

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

        e->type = EXPRESSION_USER_OP;
        e->start = left->start;
        e->left = left;
        e->op_name = tok()->identifier;
        consume(TOKEN_USER_OP);

        int prec = 8;

        struct value *p = table_look(&uops, e->op_name);
        if (p != NULL) {
                prec = (p->integer > 0) ? p->integer : abs(p->integer) - 1;
        }

        struct value *sc = table_look(&uopcs, e->op_name);
        if (sc != NULL) {
                e->sc = sc->ptr;
        } else {
                e->sc = NULL;
        }

        e->right = parse_expr(prec);
        e->end = End;

        return e;
}

static struct expression *
infix_list(struct expression *left)
{

        struct expression *e = mkexpr();
        e->start = left->start;
        e->type = EXPRESSION_LIST;
        vec_init(e->es);
        VPush(e->es, left);

        bool ne = NoEquals;
        NoEquals = true;

        while (tok()->type == ',') {
                next();
                VPush(e->es, parse_expr(1));
        }

        NoEquals = ne;

        e->end = End;

        return e;
}

static struct expression *
infix_subscript(struct expression *left)
{

        struct expression *e = mkexpr();

        consume('[');

        e->type = EXPRESSION_SUBSCRIPT;
        e->container = left;
        e->subscript = parse_expr(0);

        consume(']');

        e->end = End;

        return e;
}

static struct expression *
infix_member_access(struct expression *left)
{
        struct expression *e = mkexpr();

        e->start = left->start;
        e->maybe = tok()->type == TOKEN_DOT_MAYBE;

        next();

        /*
         * xs.<N> is syntactic sugar for xs[N - 1]
         */
        if (tok()->type == TOKEN_INTEGER) {
                e->type = EXPRESSION_SUBSCRIPT;
                e->container = left;
                e->subscript = mkexpr();
                e->subscript->type = EXPRESSION_INTEGER;
                e->subscript->integer = tok()->integer;
                next();
                e->start = left->start;
                e->end = End;
                return e;
        }

        e->object = left;

        expect(TOKEN_IDENTIFIER);

        if (token(1)->type != '(') {
                e->type = EXPRESSION_MEMBER_ACCESS;
                e->member_name = tok()->identifier;
                consume(TOKEN_IDENTIFIER);
                e->end = End;
                return e;
        }

        e->type = EXPRESSION_METHOD_CALL;
        e->sc = NULL;
        e->method_name = tok()->identifier;
        consume(TOKEN_IDENTIFIER);
        vec_init(e->method_args);
        vec_init(e->mconds);
        vec_init(e->method_kwargs);
        vec_init(e->method_kws);

        consume('(');

        setctx(LEX_PREFIX);

        if (tok()->type == ')') {
                goto End;
        } else if (tok()->type == TOKEN_STAR) {
                next();
                struct expression *arg = mkexpr();
                if (tok()->type == TOKEN_STAR) {
                        next();
                        arg->type = EXPRESSION_SPLAT;
                } else {
                        arg->type = EXPRESSION_SPREAD;
                }
                arg->value = parse_expr(0);
                arg->start = arg->value->start;
                if (arg->type == EXPRESSION_SPLAT) {
                        VPush(e->method_kwargs, arg);
                        VPush(e->method_kws, "*");
                } else {
                        VPush(e->method_args, arg);
                        VPush(e->mconds, try_cond());
                }
        } else if (tok()->type == TOKEN_IDENTIFIER && token(1)->type == ':') {
                VPush(e->method_kws, tok()->identifier);
                next();
                next();
                VPush(e->method_kwargs, parse_expr(0));
        } else {
                VPush(e->method_args, parse_expr(0));
                VPush(e->mconds, try_cond());
        }

        if (have_keyword(KEYWORD_FOR)) {
                *vec_last(e->method_args) = gencompr(*vec_last(e->method_args));
        }

        while (tok()->type == ',') {
                next();
                setctx(LEX_PREFIX);
                if (tok()->type == TOKEN_STAR) {
                        next();
                        struct expression *arg = mkexpr();
                        if (tok()->type == TOKEN_STAR) {
                                next();
                                arg->type = EXPRESSION_SPLAT;
                        } else {
                                arg->type = EXPRESSION_SPREAD;
                        }
                        arg->value = parse_expr(0);
                        arg->start = arg->value->start;
                        if (arg->type == EXPRESSION_SPLAT) {
                                VPush(e->method_kwargs, arg);
                                VPush(e->method_kws, "*");
                        } else {
                                VPush(e->method_args, arg);
                                VPush(e->mconds, try_cond());
                        }
                } else if (tok()->type == TOKEN_IDENTIFIER && token(1)->type == ':') {
                        VPush(e->method_kws, tok()->identifier);
                        next();
                        next();
                        VPush(e->method_kwargs, parse_expr(0));
                } else {
                        VPush(e->method_args, parse_expr(0));
                        VPush(e->mconds, try_cond());
                }
        }

End:
        consume(')');
        e->end = End;
        return e;
}

static struct expression *
infix_squiggly_not_nil_arrow(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_NOT_NIL_VIEW_PATTERN;

        consume('$~>');

        e->left = left;
        e->right = parse_expr(0);
        e->start = left->start;
        e->end = End;

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
        e->start = left->start;
        e->end = End;

        return e;
}

static struct expression *
infix_arrow_function(struct expression *left)
{

        consume(TOKEN_ARROW);

        struct expression *e = mkfunc();

        if (left->type != EXPRESSION_LIST && (left->type != EXPRESSION_TUPLE || !left->only_identifiers)) {
                struct expression *l = mkexpr();
                l->type = EXPRESSION_LIST;
                vec_init(l->es);
                VPush(l->es, left);
                left = l;
        } else {
                left->type = EXPRESSION_LIST;
        }

        struct statement *body = mkstmt();
        body->type = STATEMENT_BLOCK;
        vec_init(body->statements);

        for (int i = 0; i < left->es.count; ++i) {
                struct expression *p = left->es.items[i];
                if (p->type == EXPRESSION_IDENTIFIER) {
                        VPush(e->params, p->identifier);
                } else if (p->type == EXPRESSION_MATCH_REST) {
                        VPush(e->params, p->identifier);
                        e->rest = i;
                } else {
                        char *name = gensym();
                        VPush(e->params, name);
                        VPush(body->statements, mkdef(definition_lvalue(p), name));
                }
                VPush(e->dflts, NULL);
                VPush(e->constraints, NULL);
        }

        struct statement *ret = mkret((tok()->type == '{') ? parse_block_expr() : parse_expr(0));

        if (body->statements.count == 0) {
                e->body = ret;
        } else {
                VPush(body->statements, ret);
                e->body = body;
        }

        return e;
}

static struct expression *
infix_kw_or(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_KW_OR;
        e->left = left;
        e->start = left->start;

        consume_keyword(KEYWORD_OR);

        e->right = parse_expr(4);

        return e;
}

static struct expression *
infix_kw_and(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_KW_AND;
        e->left = left;
        e->start = left->start;

        consume_keyword(KEYWORD_AND);

        e->right = parse_expr(4);

        return e;
}

static struct expression *
infix_kw_in(struct expression *left)
{
        struct expression *e = mkexpr();
        e->left = left;
        e->start = left->start;

        if (tok()->keyword == KEYWORD_NOT) {
                next();
                e->type = EXPRESSION_NOT_IN;
        } else {
                e->type = EXPRESSION_IN;
        }

        consume_keyword(KEYWORD_IN);

        e->right = parse_expr(3);
        e->end = e->right->end;

        return e;
}

static struct expression *
infix_conditional(struct expression *left)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_CONDITIONAL;

        e->cond = left;

        consume(TOKEN_QUESTION);

        e->then = parse_expr(2);

        consume(':');

        e->otherwise = parse_expr(2);

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

BINARY_OPERATOR(not_eq,      NOT_EQ,    6, false)
BINARY_OPERATOR(dbl_eq,      DBL_EQ,    6, false)

BINARY_OPERATOR(and,      AND,         5, false)
BINARY_OPERATOR(bit_and,  BIT_AND,     5, false)
BINARY_OPERATOR(bit_or,   BIT_OR,      5, false)

BINARY_OPERATOR(or,           OR,          4, false)
BINARY_OPERATOR(wtf,          WTF,         4, false)

BINARY_OPERATOR(check_match, CHECK_MATCH,  3, false)

BINARY_LVALUE_OPERATOR(plus_eq,  PLUS_EQ,  2, true)
BINARY_LVALUE_OPERATOR(star_eq,  STAR_EQ,  2, true)
BINARY_LVALUE_OPERATOR(div_eq,   DIV_EQ,   2, true)
BINARY_LVALUE_OPERATOR(minus_eq, MINUS_EQ, 2, true)
/* * * * | end of infix parsers | * * * */

static parse_fn *
get_prefix_parser(void)
{
        setctx(LEX_PREFIX);

        switch (tok()->type) {
        case TOKEN_INTEGER:        return prefix_integer;
        case TOKEN_REAL:           return prefix_real;
        case TOKEN_STRING:         return prefix_string;
        case TOKEN_SPECIAL_STRING: return prefix_special_string;
        case TOKEN_REGEX:          return prefix_regex;

        case TOKEN_IDENTIFIER:     return prefix_identifier;
        case TOKEN_KEYWORD:        goto Keyword;

        case '&':                  return prefix_implicit_method;
        case TOKEN_PERCENT:        return prefix_dict;
        case '#':                  return prefix_hash;

        case '(':                  return prefix_parenthesis;
        case '[':                  return prefix_array;
        case '{':                  return prefix_record;

        case '$':                  return prefix_dollar;
        case '`':                  return prefix_tick;
        case '^':                  return prefix_carat;

        case TOKEN_TEMPLATE_BEGIN: return prefix_template;
        case '$$':                 return prefix_template_expr;

        case TOKEN_DOT_DOT:        return prefix_range;
        case TOKEN_DOT_DOT_DOT:    return prefix_incrange;

        case TOKEN_QUESTION:       return prefix_is_nil;
        case TOKEN_BANG:           return prefix_bang;
        case TOKEN_AT:             return prefix_at;
        case ':':                  return prefix_at;
        case TOKEN_MINUS:          return prefix_minus;
        case TOKEN_INC:            return prefix_inc;
        case TOKEN_DEC:            return prefix_dec;
        case TOKEN_USER_OP:        return prefix_user_op;

        case TOKEN_ARROW:          return prefix_arrow;

        case '|':                  return prefix_bit_or;

        case TOKEN_STAR:           return prefix_star;

        case TOKEN_EXPRESSION:     return prefix_expr;

        default:                   return NULL;
        }

Keyword:

        switch (tok()->keyword) {
        case KEYWORD_MATCH:     return prefix_match;
        case KEYWORD_FUNCTION:  return prefix_function;
        case KEYWORD_GENERATOR: return prefix_function;
        case KEYWORD_EVAL:      return prefix_eval;
        case KEYWORD_DEFINED:   return prefix_defined;
        case KEYWORD_TRUE:      return prefix_true;
        case KEYWORD_FALSE:     return prefix_false;
        case KEYWORD_SELF:      return prefix_self;
        case KEYWORD_NIL:       return prefix_nil;
        case KEYWORD_YIELD:     return prefix_yield;
        case KEYWORD_WITH:      return prefix_with;
        case KEYWORD_DO:        return prefix_do;

        case KEYWORD_IF:
        case KEYWORD_FOR:
        case KEYWORD_WHILE:
        case KEYWORD_TRY:
        case KEYWORD_THROW:
                return prefix_statement;

        default:                return NULL;
        }
}

static parse_fn *
get_infix_parser(void)
{
        setctx(LEX_INFIX);

        switch (tok()->type) {
        case TOKEN_KEYWORD:        goto Keyword;
        case '(':                  return infix_function_call;
        case '.':                  return infix_member_access;
        case TOKEN_DOT_MAYBE:      return infix_member_access;
        case '[':                  return infix_subscript;
        case ',':                  return infix_list;
        case '&':                  return infix_bit_and;
        case '|':                  return infix_bit_or;
        case TOKEN_INC:            return postfix_inc;
        case TOKEN_DEC:            return postfix_dec;
        case TOKEN_ARROW:          return infix_arrow_function;
        case TOKEN_SQUIGGLY_ARROW: return infix_squiggly_arrow;
        case '$~>':                return infix_squiggly_not_nil_arrow;
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
        case TOKEN_CHECK_MATCH:    return infix_check_match;
        case TOKEN_OR:             return infix_or;
        case TOKEN_WTF:            return infix_wtf;
        case TOKEN_AND:            return infix_and;
        case TOKEN_USER_OP:        return infix_user_op;
        case TOKEN_QUESTION:       return infix_conditional;
        default:                   return NULL;
        }

Keyword:

        switch (tok()->keyword) {
        //case KEYWORD_AND: return infix_kw_and;
        //case KEYWORD_OR:  return infix_kw_or;
        case KEYWORD_NOT:
        case KEYWORD_IN:  return infix_kw_in;
        default:          return NULL;
        }
}

static bool
is_postfix(struct token const *t)
{
        switch (t->type) {
        case TOKEN_INC:
        case TOKEN_DEC:
                return true;
        default:
                return false;
        }
}

static int
get_infix_prec(void)
{
        struct value *p;
        setctx(LEX_INFIX);

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
        case '&':                  return 5;
        case '|':                  return NoPipe ? -3 : 5;

        case TOKEN_OR:             return 4;
        case TOKEN_WTF:            return 4;

        /* this may need to have lower precedence. I'm not sure yet. */
        case '$~>':                return 3;
        case TOKEN_SQUIGGLY_ARROW: return 3;
        case TOKEN_CHECK_MATCH:    return 3;

        case TOKEN_QUESTION:       return 3;


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
        //case KEYWORD_OR:  return 4;
        //case KEYWORD_AND: return 4;
        case KEYWORD_NOT:
        case KEYWORD_IN:  return NoIn ? -3 : 6;
        default:          return -3;
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
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
        case EXPRESSION_TEMPLATE_HOLE:
                return e;
        case EXPRESSION_FUNCTION_CALL:
                for (int i = 0; i < e->args.count; ++i) {
                        e->args.items[i] = definition_lvalue(e->args.items[i]);
                }
                return e;
        case EXPRESSION_METHOD_CALL:
                if (e->object->type != EXPRESSION_IDENTIFIER) {
                        break;
                }
                for (int i = 0; i < e->method_args.count; ++i) {
                        e->method_args.items[i] = definition_lvalue(e->method_args.items[i]);
                }
                for (int i = 0; i < e->method_kwargs.count; ++i) {
                        e->method_kwargs.items[i] = definition_lvalue(e->method_kwargs.items[i]);
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
        case EXPRESSION_DICT:
                if (e->keys.count == 0)
                        break;
                for (size_t i = 0; i < e->elements.count; ++i) {
                        if (e->values.items[i] == NULL) {
                                struct expression *key = mkexpr();
                                if (e->keys.items[i]->type != EXPRESSION_IDENTIFIER) {
                                        EStart = e->keys.items[i]->start;
                                        EEnd = e->keys.items[i]->end;
                                        error("short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = assignment_lvalue(e->values.items[i]);
                }
                return e;
        }

        error("expression is not a valid definition lvalue");
}

static struct expression *
assignment_lvalue(struct expression *e)
{
        struct expression *v;

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
        case EXPRESSION_TUPLE:
                return e;
        case EXPRESSION_SPREAD:
                // TODO: fix this so spread/match-rest are differentiated earlier
                v = e->value;
                //assert(v->type == EXPRESSION_IDENTIFIER);
                v->type = EXPRESSION_MATCH_REST;
                v->start = e->start;
                return v;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i)
                        e->elements.items[i] = assignment_lvalue(e->elements.items[i]);
                return e;
        case EXPRESSION_DICT:
                for (size_t i = 0; i < e->keys.count; ++i) {
                        if (e->values.items[i] == NULL) {
                                struct expression *key = mkexpr();
                                if (e->keys.items[i]->type != EXPRESSION_IDENTIFIER) {
                                        EStart = key->start;
                                        EEnd = key->end;
                                        error("short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = assignment_lvalue(e->values.items[i]);
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
        struct expression *e;
        int save = TokenIndex;

        SAVE_NI(true);
        SAVE_NE(true);
        e = parse_expr(1);
        EStart = e->start;
        EEnd = e->end;
        e = definition_lvalue(e);
        LOAD_NE();
        LOAD_NI();

        if (context == LV_LET && tok()->type == ',') {
                struct expression *l = mkexpr();
                l->type = EXPRESSION_LIST;
                vec_init(l->es);
                VPush(l->es, e);
                while (tok()->type == ',') {
                        next();
                        struct expression *e = parse_definition_lvalue(LV_SUB);
                        if (e == NULL) {
                                error("expected lvalue but found %s", token_show(tok()));
                        }
                        VPush(l->es, e);
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
                if (false && token(1)->type != TOKEN_IDENTIFIER)
                        goto Error;
                break;
        default:
                break;
        }

        e->end = End;
        return e;

Error:
        seek(save);
        return NULL;
}

static struct expression *
parse_target_list(void)
{
        struct expression *e = mkexpr();
        e->type = EXPRESSION_LIST;
        vec_init(e->es);
        VPush(e->es, parse_definition_lvalue(LV_EACH));

        if (e->es.items[0] == NULL) {
        Error:
                error("expected lvalue in for-each loop");
        }

        while (
                tok()->type == ',' && (
                        token(1)->type == TOKEN_IDENTIFIER ||
                        token(1)->type == '[' ||
                        token(1)->type == '{' ||
                        (token(1)->type == '%' && token(2)->type == '{')
                )
        ) {
                next();
                VPush(e->es, parse_definition_lvalue(LV_EACH));
                if (*vec_last(e->es) == NULL) {
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

        bool match = false;
        bool cloop = false;

        if (have_keyword(KEYWORD_MATCH)) {
                match = true;
                next();
        } else {
                int save = TokenIndex;
                jmp_buf jb_save;
                memcpy(&jb_save, &jb, sizeof jb);
                SAVE_NI(true);
                if (setjmp(jb) != 0) {
                        cloop = true;
                } else {
                        parse_expr(0);
                        cloop = tok()->type == ';';
                }
                LOAD_NI();
                memcpy(&jb, &jb_save, sizeof jb);
                seek(save);
        }

        if (!cloop) {
                s->type = STATEMENT_EACH_LOOP;

                if (match) {
                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_IN;

                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = gensym();
                        tok()->module = NULL;
                }

                s->each.target = parse_target_list();

                consume_keyword(KEYWORD_IN);

                s->each.array = parse_expr(0);

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IF) {
                        next();
                        s->each.cond = parse_expr(0);
                } else {
                        s->each.cond = NULL;
                }

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_WHILE) {
                        next();
                        s->each.stop = parse_expr(0);
                } else {
                        s->each.stop = NULL;
                }

                if (match) {
                        unconsume(TOKEN_EXPRESSION);
                        tok()->e = s->each.target;

                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_MATCH;
                }

                s->each.body = parse_statement(-1);

                return s;
        }

        if (tok()->type == ';') {
                next();
                s->for_loop.init = NULL;
        } else {
                s->for_loop.init = parse_statement(-1);
        }

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

        expect('{');

        s->for_loop.body = parse_statement(-1);

        return s;
}

static struct condpart *
parse_condpart(void)
{
        struct condpart *p = Allocate(sizeof *p);
        p->e = NULL;
        p->target = NULL;
        p->def = false;

        if (have_keyword(KEYWORD_LET)) {
                next();
                p->def = true;
                p->target = parse_definition_lvalue(LV_LET);
                consume(TOKEN_EQ);
                p->e = parse_expr(-1);
                return p;
        }

        SAVE_NE(true);
        struct expression *e = parse_expr(0);
        LOAD_NE();

        if (tok()->type == TOKEN_EQ) {
                next();
                p->target = e;
                p->e = parse_expr(-1);
        } else {
                p->e = e;
        }

        return p;
}

static condpart_vector
parse_condparts(bool neg)
{
        condpart_vector parts;
        vec_init(parts);

        VPush(parts, parse_condpart());

        while ((!neg && have_keyword(KEYWORD_AND)) ||
               (neg && have_keyword(KEYWORD_OR))) {

                next();

                bool not = have_keyword(KEYWORD_NOT);
                if (not) {
                        next();
                }

                struct condpart *part = parse_condpart();

                if (part->target != NULL && neg != not) {
                        error("illegal condition used as controlling expression of if statement");
                }

                if (not && part->target == NULL) {
                        struct expression *not = mkexpr();
                        not->type = EXPRESSION_PREFIX_BANG;
                        not->operand = part->e;
                        part->e = not;
                }

                VPush(parts, part);
        }

        return parts;
}

static struct statement *
parse_while(void)
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

        struct statement *s = mkstmt();
        s->type = STATEMENT_WHILE;

        vec_init(s->While.parts);

        VPush(s->While.parts, parse_condpart());

        while (have_keyword(KEYWORD_AND)) {
                next();
                VPush(s->While.parts, parse_condpart());
        }

        s->While.block = parse_block();

        return s;
}

static struct statement *
parse_if(void)
{
        consume_keyword(KEYWORD_IF);

        struct statement *s = mkstmt();
        s->type = STATEMENT_IF;
        s->iff.neg = have_keyword(KEYWORD_NOT);

        if (s->iff.neg) {
                next();
        }

        s->iff.parts = parse_condparts(s->iff.neg);

        s->iff.then = parse_statement(-1);

        if (have_keyword(KEYWORD_ELSE)) {
                next();
                s->iff.otherwise = parse_statement(-1);
        } else {
                s->iff.otherwise = NULL;
        }

        return s;
}

static struct statement *
parse_match_statement(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_MATCH;

        consume_keyword(KEYWORD_MATCH);

        s->match.e = parse_expr(-1);

        consume('{');

        vec_init(s->match.patterns);
        vec_init(s->match.statements);

        VPush(s->match.patterns, parse_pattern());

        consume(TOKEN_FAT_ARROW);
        VPush(s->match.statements, parse_statement(0));

        while (tok()->type == ',') {
                next();

                if (tok()->type == '}') {
                        break;
                }

                VPush(s->match.patterns, parse_pattern());
                consume(TOKEN_FAT_ARROW);
                VPush(s->match.statements, parse_statement(0));
        }

        consume('}');

        return s;
}

static struct statement *
parse_function_definition(void)
{
        struct statement *s = mkstmt();

        if (tok()->keyword == KEYWORD_MACRO) {
                struct token kw = *token(0);
                kw.keyword = KEYWORD_FUNCTION;
                struct token name = *token(1);
                next();
                next();
                if (tok()->type == '(') {
                        s->type = STATEMENT_FUN_MACRO_DEFINITION;
                } else {
                        s->type = STATEMENT_MACRO_DEFINITION;
                        unconsume(')');
                        unconsume('(');
                }
                unconsume(TOKEN_IDENTIFIER);
                *tok() = name;
                unconsume(TOKEN_KEYWORD);
                *tok() = kw;
        } else {
                s->type = STATEMENT_FUNCTION_DEFINITION;

        }

        Location target_start = tok()->start;
        Location target_end = tok()->end;

        for (int i = 0; i < 128; ++i) { 
                if (token(i)->type == TOKEN_KEYWORD && token(i)->keyword == KEYWORD_FUNCTION) {
                        target_start = token(i + 1)->start;
                        target_end = token(i + 1)->end;
                        break;
                }
        }

        struct expression *f = prefix_function();
        if (f->name == NULL)
                error("anonymous function definition used in statement context");

        if (s->type == STATEMENT_FUN_MACRO_DEFINITION) {
                VInsert(f->params, "raw", 0);
                VInsert(f->dflts, NULL, 0);
                VInsert(f->constraints, NULL, 0);
                if (f->rest != -1) {
                        f->rest += 1;
                }
                if (f->ikwargs != -1) {
                        f->ikwargs += 1;
                }
        }

        struct expression *target = mkexpr();
        target->type = EXPRESSION_IDENTIFIER;
        target->identifier = f->name;
        target->module = NULL;
        target->start = target_start;
        target->end = target_end;

        s->target = target;
        s->value = f;
        s->pub = false;

        return s;
}

static struct statement *
parse_operator_directive(void)
{
        setctx(LEX_INFIX);

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

        if (tok()->type != TOKEN_NEWLINE) {
                struct expression *e = parse_expr(0);
                table_put(&uopcs, uop, PTR(e));
        }

        consume(TOKEN_NEWLINE);

        return NULL;
}

static struct statement *
parse_return_statement(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);

        consume_keyword(KEYWORD_RETURN);

        if (tok()->start.line != s->start.line) {
                return s;
        }

        VPush(s->returns, parse_expr(0));

        while (tok()->type == ',') {
                next();
                VPush(s->returns, parse_expr(0));
        }

        if (tok()->type == ';')
                next();

        return s;
}

static struct statement *
parse_let_definition(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_DEFINITION;
        s->pub = false;

        consume_keyword(KEYWORD_LET);

        s->target = parse_definition_lvalue(LV_LET);
        if (s->target == NULL) {
                error("failed to parse lvalue in 'let' definition");
        }

        consume(TOKEN_EQ);

        s->value = parse_expr(-1);

        s->end = End;

        if (tok()->type == ';')
                next();

        return s;
}

static struct statement *
parse_defer_statement(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_DEFER;

        consume_keyword(KEYWORD_DEFER);

        s->expression = mkfunc();
        s->expression->body = parse_statement(-1);

        if (tok()->type == ';')
                next();

        return s;
}

inline static struct statement *
try_conditional_from(struct statement *s)
{
        if (tok()->start.line == End.line && have_keyword(KEYWORD_IF)) {
                next();

                struct statement *if_ = mkstmt();
                if_->type = STATEMENT_IF;
                if_->iff.neg = have_keyword(KEYWORD_NOT);

                if (if_->iff.neg) {
                        next();
                }

                if_->iff.parts = parse_condparts(if_->iff.neg);
                if_->iff.then = s;
                if_->iff.otherwise = NULL;

                s = if_;
        }

        return s;
}

static struct statement *
parse_break_statement(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_BREAK;

        s->depth = 0;

        while (have_keyword(KEYWORD_BREAK)) {
                next();
                s->depth += 1;
        }

        if (tok()->start.line == s->start.line &&
            get_prefix_parser() != NULL &&
            (!have_keyword(KEYWORD_IF) || tok()->type == '(')) {
                s->expression = parse_expr(0);
        } else {
                s->expression = NULL;
        }

        s = try_conditional_from(s);

        if (tok()->type == ';')
                consume(';');

        return s;
}

static struct statement *
parse_continue_statement(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_CONTINUE;
        s->depth = 0;

        while (have_keyword(KEYWORD_CONTINUE)) {
                next();
                s->depth += 1;
        }

        s = try_conditional_from(s);

        if (tok()->type == ';')
                next();

        return s;
}

static struct statement *
parse_null_statement()
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_NULL;

        consume(';');

        return s;
}

inline static bool
should_split(void)
{
        if (tok()->start.line == End.line) {
                return false;
        }

        switch (tok()->type) {
        case '(':
        case '[':
                return true;
        }

        return false;
}

static struct expression *
parse_expr(int prec)
{
        struct expression *e;

        if (++depth > 256)
                error("exceeded maximum recursion depth of 256");

        parse_fn *f = get_prefix_parser();
        if (f == NULL) {
                error(
                        "expected expression but found %s%s%s",
                        TERM(34),
                        token_show(tok()),
                        TERM(0)
                );
        }

        e = f();

        while (!should_split() && prec < get_infix_prec()) {
                f = get_infix_parser();
                if (f == NULL) {
                        error("unexpected token after expression: %s", token_show(tok()));
                }
                if ((token(1)->type == ']' || (have_not_in() && token(2)->type == ']')) && !is_postfix(tok())) {
                        // Special case for operator slices. Very based!
                        goto End;
                }
                e = f(e);
        }
End:
        --depth;

        return e;
}

static struct statement *
parse_block(void)
{
        struct statement *block = mkstmt();

        consume('{');

        block->type = STATEMENT_BLOCK;
        vec_init(block->statements);

        while (tok()->type != '}') {
                struct statement *s = parse_statement(-1);
                s->end = End;
                VPush(block->statements, s);
        }

        consume('}');

        return block;
}

static struct statement *
mktagdef(char *name)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_TAG_DEFINITION;
        s->tag.pub = false;
        s->tag.name = name;
        vec_init(s->tag.methods);
        vec_init(s->tag.getters);
        vec_init(s->tag.setters);
        vec_init(s->tag.statics);
        return s;
}

static struct statement *
parse_class_definition(void)
{
        bool tag = tok()->keyword == KEYWORD_TAG;

        consume_keyword(tag ? KEYWORD_TAG : KEYWORD_CLASS);

        expect(TOKEN_IDENTIFIER);

        struct statement *s = mktagdef(tok()->identifier);
        if (!tag)
                s->type = STATEMENT_CLASS_DEFINITION;

        next();

        if (tok()->type == ':') {
                next();

                int start_index = TokenIndex;

                while (tok()->type == TOKEN_IDENTIFIER && token(1)->type == '.') {
                        next();
                        next();
                }

                expect(TOKEN_IDENTIFIER);
                next();

                expect('{');

                TokenIndex = start_index;

                s->tag.super = parse_expr(0);
        } else {
                s->tag.super = NULL;
        }

        /* Hack to allow comma-separated tag declarations */
        if (tag && tok()->type == ',') {
                struct statement *tags = mkstmt();
                tags->type = STATEMENT_MULTI;
                vec_init(tags->statements);
                VPush(tags->statements, s);
                while (tok()->type == ',') {
                        next();
                        expect(TOKEN_IDENTIFIER);
                        VPush(tags->statements, mktagdef(tok()->identifier));
                        next();
                }
                s = tags;
        }

        if (tag && tok()->type == ';') {
                next();
        } else {
                consume('{');
                setctx(LEX_INFIX);
                while (tok()->type != '}') {
                        parse_sync_lex();

                        char const *doc = NULL;
                        lex_keep_comments(true);
                        if (tok()->type == TOKEN_COMMENT) {
                                doc = tok()->comment;
                                next();
                        }
                        lex_keep_comments(false);

                        /*
                         * Lol.
                         */
                        switch (tok()->type) {
                        case TOKEN_DBL_EQ:      tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "==";   break;
                        case TOKEN_CMP:         tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "<=>";  break;
                        case TOKEN_PLUS:        tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "+";    break;
                        case TOKEN_DIV:         tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "/";    break;
                        case TOKEN_MINUS:       tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "-";    break;
                        case TOKEN_STAR:        tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "*";    break;
                        case TOKEN_PERCENT:     tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "%";    break;
                        case TOKEN_INC:         tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "++";   break;
                        case TOKEN_DEC:         tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "--";   break;
                        case TOKEN_PLUS_EQ:     tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "+=";   break;
                        case TOKEN_STAR_EQ:     tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "*=";   break;
                        case TOKEN_MINUS_EQ:    tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "-=";   break;
                        case TOKEN_DIV_EQ:      tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "/=";   break;
                        case '&':               tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "&";    break;
                        case '|':               tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "|";    break;
                        case '^':               tok()->type = TOKEN_IDENTIFIER; tok()->identifier = "^";    break;
                        case TOKEN_USER_OP:     tok()->type = TOKEN_IDENTIFIER;                             break;
                        case '~':               next();
                        case TOKEN_IDENTIFIER:                                                              break;
                        default: if (!have_keyword(KEYWORD_STATIC)) expect(TOKEN_IDENTIFIER);               break;
                        }
                        struct location start = tok()->start;
                        if (have_keyword(KEYWORD_STATIC)) {
                                next();
                                expect(TOKEN_IDENTIFIER);
                                unconsume(TOKEN_KEYWORD);
                                tok()->keyword = KEYWORD_FUNCTION;
                                VPush(s->tag.statics, prefix_function());
                                (*vec_last(s->tag.statics))->doc = doc;
                                (*vec_last(s->tag.statics))->start = start;
                                (*vec_last(s->tag.statics))->start = End;
                        } else if (token(1)->type == TOKEN_EQ) {
                                struct token t = *tok();
                                skip(2);
                                unconsume(TOKEN_IDENTIFIER);
                                *tok() = t;
                                unconsume(TOKEN_KEYWORD);
                                tok()->keyword = KEYWORD_FUNCTION;
                                VPush(s->tag.setters, prefix_function());
                                (*vec_last(s->tag.setters))->doc = doc;
                                (*vec_last(s->tag.setters))->start = start;
                                (*vec_last(s->tag.setters))->start = End;

                        } else if (token(1)->type == '{') {
                                struct token t = *tok();
                                next();
                                unconsume(')');
                                unconsume('(');
                                unconsume(TOKEN_IDENTIFIER);
                                *tok() = t;
                                unconsume(TOKEN_KEYWORD);
                                tok()->keyword = KEYWORD_FUNCTION;
                                VPush(s->tag.getters, prefix_function());
                                (*vec_last(s->tag.getters))->doc = doc;
                                (*vec_last(s->tag.getters))->start = start;
                                (*vec_last(s->tag.getters))->start = End;
                        } else {
                                unconsume(TOKEN_KEYWORD);
                                tok()->keyword = KEYWORD_FUNCTION;
                                VPush(s->tag.methods, prefix_function());
                                (*vec_last(s->tag.methods))->doc = doc;
                                (*vec_last(s->tag.methods))->start = start;
                                (*vec_last(s->tag.methods))->start = End;
                        }
                }
                setctx(LEX_PREFIX);
                consume('}');
        }

        return s;
}

static struct statement *
parse_throw(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_THROW;

        consume_keyword(KEYWORD_THROW);

        s->throw = parse_expr(0);

        if (tok()->type == ';')
                next();

        s->end = End;

        return s;
}

static struct statement *
parse_try(void)
{
        consume_keyword(KEYWORD_TRY);

        struct statement *s = mkstmt();
        s->type = STATEMENT_TRY;

        vec_init(s->try.patterns);
        vec_init(s->try.handlers);

        if (tok()->type != '{') {
                s->try.s = mkstmt();
                s->try.s->type = STATEMENT_IF;
                s->try.s->iff.neg = true;
                s->try.s->iff.parts = parse_condparts(false);

                while (have_keyword(KEYWORD_CATCH)) {
                        next();
                        SAVE_NE(true);
                        VPush(s->try.patterns, parse_expr(0));
                        LOAD_NE();
                        VPush(s->try.handlers, parse_statement(-1));
                }

                struct statement *otherwise;

                if (have_keywords(KEYWORD_OR, KEYWORD_ELSE)) {
                        skip(2);
                        otherwise = parse_statement(-1);
                } else {
                        otherwise = mkstmt();
                        otherwise->type = STATEMENT_NULL;
                }

                s->try.s->iff.then = otherwise;
                s->try.s->iff.otherwise = NULL;

                VPush(s->try.patterns, &WildCard);
                VPush(s->try.handlers, otherwise);

                s->try.finally = NULL;

                return s;
        }

        s->try.s = parse_statement(-1);

        while (have_keyword(KEYWORD_CATCH)) {
                next();
                SAVE_NE(true);
                VPush(s->try.patterns, parse_expr(0));
                LOAD_NE();
                VPush(s->try.handlers, parse_statement(-1));
        }

        if (have_keyword(KEYWORD_FINALLY)) {
                next();
                s->try.finally = parse_statement(-1);
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
                VPush(s->exports, tok()->identifier);
                next();
                if (tok()->type == ',') {
                        next();
                } else {
                        expect(TOKEN_NEWLINE);
                }
        }

        consume(TOKEN_NEWLINE);

        return s;
}

static struct statement *
parse_import(void)
{
        struct statement *s = mkstmt();
        s->type = STATEMENT_IMPORT;

        if (have_keyword(KEYWORD_PUB)) {
                s->import.pub = true;
                next();
        } else {
                s->import.pub = false;
        }

        consume_keyword(KEYWORD_IMPORT);

        expect(TOKEN_IDENTIFIER);
        char *mod = tok()->module;
        char *id = tok()->identifier;
        next();

        static vec(char) module;
        module.count = 0;

        if (mod != NULL) {
                VPushN(module, mod, strlen(mod));
                VPush(module, '/');
        }

        VPushN(module, id, strlen(id));

        while (tok()->type == '.') {
                next();
                expect(TOKEN_IDENTIFIER);
                VPush(module, '/');
                VPushN(module, tok()->identifier, strlen(tok()->identifier));
                next();
        }

        VPush(module, '\0');

        s->import.module = sclonea(module.items);

        if (tok()->type == TOKEN_IDENTIFIER && strcmp(tok()->identifier, "as") == 0) {
                next();
                expect(TOKEN_IDENTIFIER);
                s->import.as = tok()->identifier;
                next();
        } else {
                s->import.as = s->import.module;
        }

        vec_init(s->import.identifiers);

        if (tok()->type == '(') {
                next();
                if (tok()->type == TOKEN_DOT_DOT) {
                        next();
                        VPush(s->import.identifiers, "..");
                } else while (tok()->type == TOKEN_IDENTIFIER) {
                        VPush(s->import.identifiers, tok()->identifier);
                        next();
                        if (tok()->type == ',')
                                next();
                        else
                                expect(')');
                }
                consume(')');
        }

        s->end = End;

        consume(TOKEN_NEWLINE);

        return s;
}

static struct statement *
parse_statement(int prec)
{
        struct statement *s;

        setctx(LEX_PREFIX);

        switch (tok()->type) {
        case TOKEN_AT:
                if (token(1)->type == '[')
                        return parse_function_definition();
                else
                        goto Expression;
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
        case KEYWORD_WHILE:    return parse_while();
        case KEYWORD_IF:       return parse_if();
        case KEYWORD_FUNCTION: return parse_function_definition();
        case KEYWORD_MACRO:    return parse_function_definition();
        case KEYWORD_OPERATOR: return parse_operator_directive();
        case KEYWORD_MATCH:    return parse_match_statement();
        case KEYWORD_RETURN:   return parse_return_statement();
        case KEYWORD_DEFER:    return parse_defer_statement();
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
        s->expression = parse_expr(prec);
        s->end = s->expression->end;

        if (s->expression->type == EXPRESSION_STATEMENT) {
                s = s->expression->statement;
        }

        if (tok()->type == ';') {
                consume(';');
        }

        return s;
}

char const *
parse_error(void)
{
        return ERR;
}

static void
define_top(struct statement *s, char const *doc)
{
        switch (s->type) {
        case STATEMENT_FUN_MACRO_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
                s->doc = doc;
                define_macro(s, s->type == STATEMENT_FUN_MACRO_DEFINITION);
                break;
        case STATEMENT_FUNCTION_DEFINITION:
                s->doc = doc;
                s->value->doc = doc;
                define_function(s);
                break;
        case STATEMENT_CLASS_DEFINITION:
                s->class.doc = doc;
                define_class(s);
                break;
        case STATEMENT_MULTI:
                for (int i = 0; i < s->statements.count; ++i) {
                        define_top(s->statements.items[i], doc);
                }
                break;
        case STATEMENT_DEFINITION:
                s->doc = doc;
                break;
        default:
                break;
        }
}

struct statement **
parse(char const *source, char const *file)
{
        volatile vec(struct statement *) program;
        vec_init(program);

        depth = 0;
        filename = file;

        TokenIndex = 0;
        vec_init(tokens);

        lex_init(file, source);
        lex_keep_comments(true);

        lex_save(&CtxCheckpoint);
        setctx(LEX_PREFIX);

        if (setjmp(jb) != 0) {
                return NULL;
        }

        while (tok()->type == TOKEN_NEWLINE) {
                next();
        }

        while (
                have_keywords(KEYWORD_PUB, KEYWORD_IMPORT)
             || have_keyword(KEYWORD_IMPORT)
             || tok()->type == TOKEN_COMMENT
        ) {
                if (tok()->type == TOKEN_COMMENT) {
                        next();
                } else {
                        VPush(program, parse_import());
                        if (vec_last(program)[0]->type != STATEMENT_IMPORT) {
                                puts("Oh no!!");
                        }
                }
        }

        int TokenIndex_ = TokenIndex;
        TokenVector tokens_ = tokens;
        LexState CtxCheckpoint_ = CtxCheckpoint;
        char const *filename_ = filename;
        jmp_buf jb_;
        struct location EStart_ = EStart;
        struct location EEnd_ = EEnd;
        memcpy(&jb_, &jb, sizeof jb);

        lex_save(&CtxCheckpoint);
        lex_start(&CtxCheckpoint);

        for (int i = 0; i < program.count; ++i) {
                import_module(program.items[i]);
        }

        lex_end();

        memcpy(&jb, &jb_, sizeof jb);
        CtxCheckpoint = CtxCheckpoint_;
        TokenIndex = TokenIndex_;
        tokens = tokens_;
        filename = filename_;
        EStart = EStart_;
        EEnd = EEnd_;

        setctx(LEX_INFIX);
        setctx(LEX_PREFIX);

        program.count = 0;

        while (have_keyword(KEYWORD_EXPORT) || tok()->type == TOKEN_COMMENT) {
                if (tok()->type == TOKEN_COMMENT)
                        next();
                else
                        VPush(program, parse_export());
        }

        while (TokenIndex > 0 && token(-1)->type == TOKEN_COMMENT) {
                TokenIndex -= 1;
        }

        while (tok()->type != TOKEN_END) {
                char const *doc = NULL;

                parse_sync_lex();
                lex_keep_comments(true);

                if (tok()->type == TOKEN_COMMENT) {
                        doc = tok()->comment;
                        next();
                }

                bool pub = have_keyword(KEYWORD_PUB);

                if (pub) {
                        next();
                        if (!have_keyword(KEYWORD_FUNCTION) &&
                            !have_keyword(KEYWORD_MACRO) &&
                            !have_keyword(KEYWORD_CLASS) &&
                            !have_keyword(KEYWORD_TAG)) {

                                unconsume(TOKEN_KEYWORD);
                                tok()->keyword = KEYWORD_LET;
                        }
                }

                lex_keep_comments(false);
                struct statement *s = parse_statement(-1);
                if (s == NULL) {
                        break;
                }


                // TODO: figure out if this is necessary
                while (s->type == STATEMENT_EXPRESSION && s->expression->type == EXPRESSION_STATEMENT) {
                        s = s->expression->statement;
                }

                s->end = End;

                if (s->type != STATEMENT_MACRO_DEFINITION) {
                        VPush(program, s);
                }

                if (pub) switch (s->type) {
                case STATEMENT_DEFINITION:
                case STATEMENT_FUNCTION_DEFINITION:
                case STATEMENT_MACRO_DEFINITION:
                case STATEMENT_FUN_MACRO_DEFINITION:
                        s->pub = true;
                        break;
                case STATEMENT_TAG_DEFINITION:
                case STATEMENT_CLASS_DEFINITION:
                        s->class.pub = true;
                        break;
                default:
                        error("This shouldn't happen.");
                }

                define_top(s, doc);
        }

        VPush(program, NULL);

        return program.items;
}

struct value
parse_get_token(int i)
{
        bool keep_comments = lex_keep_comments(true);
        char *type = NULL;

        if (lex_pos().s > vec_last(tokens)->end.s) {
                tokens.count = TokenIndex;
                VPush(tokens, ((struct token) {
                        .ctx = lctx,
                        .type = TOKEN_EXPRESSION,
                        .start = lex_pos(),
                        .end = lex_pos()
                }));
                next();
        } else {
                tokens.count = TokenIndex;
                lex_rewind(&token(-1)->end);
        }

        struct token *t = token(i);

        lex_keep_comments(keep_comments);


#define T(name) (STRING_NOGC(#name, strlen(#name)))

        switch (t->type) {
        case TOKEN_IDENTIFIER:
                return value_named_tuple(
                        "type", T(id),
                        "id", STRING_NOGC(t->identifier, strlen(t->identifier)),
                        "module", t->module == NULL ? NIL : STRING_NOGC(t->module, strlen(t->module)),
                        NULL
                );
        case TOKEN_INTEGER:
                return value_named_tuple(
                        "type", T(int),
                        "int", INTEGER(t->integer),
                        NULL
                );
        case TOKEN_STRING:
                return value_named_tuple(
                        "type", T(string),
                        "str", STRING_NOGC(t->string, strlen(t->string)),
                        NULL
                );
        case TOKEN_COMMENT:
                return value_named_tuple(
                        "type", T(comment),
                        "comment", STRING_NOGC(t->comment, strlen(t->comment)),
                        NULL
                );
        case TOKEN_END:
                return NIL;
        case TOKEN_DOT_DOT:
                type = "..";
                break;
        case TOKEN_DOT_DOT_DOT:
                type = "...";
                break;
        case TOKEN_AT:
                type = "@";
                break;
        case TOKEN_INC:
                type = "++";
                break;
        case TOKEN_BANG:
                type = "!";
                break;
        case TOKEN_EQ:
                type = "=";
                break;
        case TOKEN_NOT_EQ:
                type = "!=";
                break;
        case TOKEN_STAR:
                type = "*";
                break;
        case TOKEN_LT:
                type = "<";
                break;
        case TOKEN_GT:
                type = ">";
                break;
        case TOKEN_LEQ:
                type = "<=";
                break;
        case TOKEN_GEQ:
                type = ">=";
                break;
        case TOKEN_CMP:
                type = "<=>";
                break;
        case TOKEN_WTF:
                type = "??";
                break;
        case TOKEN_ARROW:
                type = "->";
                break;
        case TOKEN_FAT_ARROW:
                type = "=>";
                break;
        case TOKEN_SQUIGGLY_ARROW:
                type = "~>";
                break;
        case TOKEN_KEYWORD:
                type = (char *)keyword_show(t->keyword);
                break;
        }

#undef T

        if (type == NULL) {
                type = sclonea((char const []){(char)t->type, '\0'});
        }

        return value_named_tuple(
                "type", STRING_NOGC(type, strlen(type)),
                NULL
        );
}

void
parse_next(void)
{
        next();
}

struct value
parse_get_expr(int prec, bool resolve)
{
        int save = TokenIndex;

        jmp_buf jb_save;
        memcpy(&jb_save, &jb, sizeof jb);

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(false);

        struct value v;

        if (setjmp(jb) != 0) {
                v = NIL;
                seek(save);
        } else {
                struct expression *e = parse_expr(prec);
                if (!resolve) {
                        v = tyexpr(e);
                } else {
                        compiler_symbolize_expression(e, NULL);
                        v = PTR(e);
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(0, TyExpr);
                }
        }

        LOAD_NE();
        LOAD_NI();

        memcpy(&jb, &jb_save, sizeof jb);

        lex_keep_comments(keep_comments);

        return v;
}

struct value
parse_get_stmt(int prec, bool want_raw)
{
        int save = TokenIndex;

        jmp_buf jb_save;
        memcpy(&jb_save, &jb, sizeof jb);

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(false);

        struct value v;

        if (setjmp(jb) != 0) {
                v = NIL;
                seek(save);
        } else {
                struct statement *s = parse_statement(prec);
                if (want_raw) {
                        v = value_tuple(2);
                        v.items[0] = PTR(s);
                        v.items[1] = tystmt(s);
                } else {
                        v = tystmt(s);
                }
        }

        LOAD_NE();
        LOAD_NI();

        memcpy(&jb, &jb_save, sizeof jb);

        lex_keep_comments(keep_comments);

        return v;
}

noreturn void
parse_fail(char const *s, size_t n)
{
        error("%.*s", (int)n, s);
}

/* vim: set sts=8 sw=8 expandtab: */
