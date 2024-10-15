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
#include "parse.h"
#include "ty.h"

#define BINARY_OPERATOR(name, t, prec, right_assoc) \
        static Expr * \
        infix_ ## name(Ty *ty, Expr *left) \
        { \
                Expr *e = mkexpr(ty); \
                next(); \
                e->type = EXPRESSION_ ## t; \
                e->left = left; \
                e->right = parse_expr(ty, prec - (right_assoc ? 1 : 0)); \
                e->start = left->start; \
                e->end = token(-1)->end; \
                return e; \
        } \

#define BINARY_LVALUE_OPERATOR(name, t, prec, right_assoc) \
        static Expr * \
        infix_ ## name(Ty *ty, Expr *left) \
        { \
                Expr *e = mkexpr(ty); \
                consume(TOKEN_ ## t); \
                e->type = EXPRESSION_ ## t; \
                e->target = assignment_lvalue(ty, left); \
                e->value = parse_expr(ty, prec - (right_assoc ? 1 : 0)); \
                e->start = e->target->start; \
                e->end = e->value->end; \
                return e; \
        } \

#define PREFIX_OPERATOR(name, token, prec) \
        static Expr * \
        prefix_ ## name(Ty *ty) \
        { \
                Expr *e = mkexpr(ty); \
                consume(TOKEN_ ## token); \
                e->type = EXPRESSION_PREFIX_ ## token; \
                e->operand = parse_expr(ty, prec); \
                e->end = e->operand->end; \
                return e; \
        } \

#define PREFIX_LVALUE_OPERATOR(name, token, prec) \
        static Expr * \
        prefix_ ## name(Ty *ty) \
        { \
                Expr *e = mkexpr(ty); \
                consume(TOKEN_ ## token); \
                e->type = EXPRESSION_PREFIX_ ## token; \
                e->operand = assignment_lvalue(ty, parse_expr(ty, prec)); \
                e->end = End; \
                return e; \
        } \

#define          tok()  (tok         )(ty)
#define        token(i) (token       )(ty, i)
#define         next()  (next        )(ty)
#define      consume(t) (consume     )(ty, t)
#define       expect(t) (expect      )(ty, t)
#define         skip(n) (skip        )(ty, n)
#define have_keyword(k) (have_keyword)(ty, k)
#define    unconsume(t) (unconsume   )(ty, t)

typedef Expr *
prefix_parse_fn(Ty *ty);

typedef Expr *
infix_parse_fn(Ty *ty, Expr *);

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

static struct table uops;
static struct table uopcs;

static LexState CtxCheckpoint;
static TokenVector tokens;

static expression_vector TemplateExprs;

static Namespace *CurrentNamespace = NULL;

static int TokenIndex = 0;
LexContext lctx = LEX_PREFIX;

static struct location EStart;
static struct location EEnd;

static struct location End;

static int depth;
static bool NoEquals = false;
static bool NoIn = false;
static bool NoAndOr = false;
static bool NoPipe = false;

static Expr WildCard = {
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
#define SAVE_NA(b) bool NASave = NoAndOr; NoAndOr = (b);

#define LOAD_NE() NoEquals = NESave;
#define LOAD_NC() NoConstraint = NCSave;
#define LOAD_NI() NoIn = NISave;
#define LOAD_NP() NoPipe = NPSave;
#define LOAD_NA() NoAndOr = NASave;

static char const *filename;

noreturn static void
error(Ty *ty, char const *fmt, ...);

static void
logctx(Ty *ty);

static infix_parse_fn *
get_infix_parser(Ty *ty);

static prefix_parse_fn *
get_prefix_parser(Ty *ty);

static Stmt *
parse_statement(Ty *ty, int);

static Expr *
parse_expr(Ty *ty, int);

static Stmt *
parse_match_statement(Ty *ty);

static Stmt *
parse_if(Ty *ty);

static Stmt *
parse_while(Ty *ty);

static Stmt *
parse_try(Ty *ty);

static Stmt *
parse_for_loop(Ty *ty);

static Stmt *
parse_let_definition(Ty *ty);

static Expr *
parse_target_list(Ty *ty);

static Stmt *
parse_block(Ty *ty);

static condpart_vector
parse_condparts(Ty *ty, bool neg);

static Expr *
assignment_lvalue(Ty *ty, Expr *e);

static Expr *
definition_lvalue(Ty *ty, Expr *e);

static Expr *
infix_member_access(Ty *ty, Expr *e);

static Expr *
infix_function_call(Ty *ty, Expr *left);

static Expr *
prefix_parenthesis(Ty *ty);

static Expr *
prefix_function(Ty *ty);

static Expr *
prefix_percent(Ty *ty);

static Expr *
prefix_implicit_lambda(Ty *ty);

static Expr *
prefix_identifier(Ty *ty);

inline static struct token *
(tok)(Ty *ty);

inline static struct token *
(token)(Ty *ty, int i);

Expr *
mkcall(Ty *ty, Expr *func);

static Expr *
mkpartial(Ty *ty, Expr *sugared);

char *
mksym(Ty *ty, int s)
{
        char b[32];

        snprintf(b, sizeof b, ":%d", s);
        return sclonea(ty, b);
}

/*
 * Get a unique identifier name.
 * This sucks.
 */
char *
gensym(Ty *ty)
{
        static int sym = 0;
        return mksym(ty, sym++);
}

inline static Expr *
mkexpr(Ty *ty)
{
        Expr *e = amA0(sizeof *e);
        e->arena = GetArenaAlloc(ty);
        e->origin = NULL;
        e->constraint = NULL;
        e->is_method = false;
        e->symbolized = false;
        e->has_resources = false;
        e->filename = filename;
        e->start = tok()->start;
        e->end = tok()->end;
        return e;
}

inline static Expr *
mkfunc(Ty *ty)
{
        Expr *f = mkexpr(ty);

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

inline static Stmt *
mkstmt(Ty *ty)
{
        Stmt *s = amA(sizeof *s);
        s->arena = GetArenaAlloc(ty);
        s->origin = NULL;
        s->filename = filename;
        s->start = tok()->start;
        s->end = tok()->start;
        return s;
}

inline static Stmt *
mkret(Ty *ty, Expr *value)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);
        avP(s->returns, value);
        return s;
}

inline static Stmt *
mkdef(Ty *ty, Expr *lvalue, char *name)
{
        Expr *value = mkexpr(ty);
        value->type = EXPRESSION_IDENTIFIER;
        value->identifier = name;
        value->module = NULL;

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_DEFINITION;
        s->pub = false;
        s->target = lvalue;
        s->value = value;

        return s;
}

inline static struct token *
(token)(Ty *ty, int i)
{
        struct token t;
        while (tokens.count <= i + TokenIndex) {
                if (tokens.count == TokenIndex) {
                        lex_save(ty, &CtxCheckpoint);
                }
                t = lex_token(ty, lctx);
                LOG("Adding tokens[%d] = %s", (int)tokens.count, token_show(ty, &t));
                avP(tokens, t);
        }

        LOG("tokens[%d] = %s", TokenIndex + i, token_show(ty, &tokens.items[TokenIndex + i]));

        return &tokens.items[TokenIndex + i];
}

inline static struct token *
(tok)(Ty *ty)
{
        return token(0);
}

inline static void
(skip)(Ty *ty, int n)
{
        TokenIndex += n;
        End = token(-1)->end;
        EStart = tok()->start;
        EEnd = tok()->end;
}

inline static void
(next)(Ty *ty)
{
        skip(1);
}

inline static void
seek(Ty *ty, int i)
{
        TokenIndex = i;
        skip(0);
}

void
parse_sync_lex(Ty *ty)
{
        if (TokenIndex > 0 && TokenIndex < tokens.count) {
                tokens.count = TokenIndex;
                lex_rewind(ty, &token(-1)->end);
        }
}

inline static void
setctx(Ty *ty, int ctx)
{
        if (lctx == ctx)
                return;

        if (tok()->ctx == LEX_FAKE)
                return;

        lctx = ctx;

        bool next_nl = tok()->type == TOKEN_NEWLINE;

        LOG("Rewinding to: %.*s...  TokenIndex=%d\n", (int)strcspn(tok()->start.s, "\n"), tok()->start.s, TokenIndex);

        struct location start = tok()->start;
        lex_rewind(ty, &start);

        if (next_nl)
                lex_need_nl(ty, true);

        // TODO: Should we be discarding LEX_FAKE tokens? (i.e. tokens that were unconsume()d)

        while (tokens.count > TokenIndex) {
                LOG("Popping tokens[%zu]: %s\n", tokens.count - 1, token_show(ty, vvL(tokens)));
                tokens.count -= 1;
        }

        while (tokens.count > 0 && vvL(tokens)->start.s == start.s) {
                LOG("Popping tokens[%zu]: %s\n", tokens.count - 1, token_show(ty, vvL(tokens)));
                tokens.count -= 1;
        }

        // TODO: ???
        if (TokenIndex > tokens.count) {
                TokenIndex = tokens.count;
        }

        logctx(ty);
}

static void
logctx(Ty *ty)
{
#if 0
        tok();

        int lo = max(0, TokenIndex - 3);
        int hi = tokens.count - 1;

        fprintf(stderr, "Lex context: %-6s    ", lctx == LEX_PREFIX ? "prefix" : "infix");

        for (int i = lo; i <= hi; ++i) {
                if (i == TokenIndex) {
                        fprintf(stderr, "  %s[%s]%s", TERM(92), token_show(ty, &tokens.items[i]), TERM(0));
                } else {
                        fprintf(stderr, "  [%s]", token_show(ty, &tokens.items[i]));
                }
        }

        char const *ahead = lex_pos(ty).s;

        fprintf(stderr, ": %.*s\n\n", (int)strcspn(ahead, "\n"), ahead);
#endif
}


/*
 * Push a token into the token stream, so that it will be returned by the next call
 * to tok().
 */
inline static void
(unconsume)(Ty *ty, int type)
{
        struct token t = {
                .type = type,
                .start = End,
                .end = End,
                .ctx = LEX_FAKE
        };

        LOG("Inserting tokens[%d] = %s", TokenIndex, token_show(ty, &t));

        logctx(ty);

        avI(tokens, t, TokenIndex);
}

inline static void
putback(Ty *ty, Token t)
{
        unconsume(TOKEN_ERROR);
        *tok() = t;
        tok()->ctx = LEX_FAKE;
}

noreturn static void
error(Ty *ty, char const *fmt, ...)
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

inline static Namespace *
PushNS(Ty *ty, char *id, bool pub)
{
        Namespace *ns = amA(sizeof *ns);
        ns->id = id;
        ns->pub = pub;
        ns->braced = true;
        ns->next = CurrentNamespace;
        return CurrentNamespace = ns;
}

inline static void
PopNS(Ty *ty)
{
        CurrentNamespace = CurrentNamespace->next;
}

inline static bool
(have_keyword)(Ty *ty, int kw)
{
        return tok()->type == TOKEN_KEYWORD && tok()->keyword == kw;
}

inline static bool
have_keywords(Ty *ty, int kw1, int kw2)
{
        return tok()->type == TOKEN_KEYWORD && tok()->keyword == kw1 &&
               token(1)->type == TOKEN_KEYWORD && token(1)->keyword == kw2;
}

inline static bool
have_without_nl(Ty *ty, int t)
{
        return tok()->type == t && tok()->start.line == End.line;
}

inline static bool
next_without_nl(Ty *ty, int t)
{
        return token(1)->type == t && token(1)->start.line == tok()->end.line;
}

inline static bool
kw_without_nl(Ty *ty, int t)
{
        return have_without_nl(ty, TOKEN_KEYWORD) && tok()->keyword == t;
}

static bool
have_not_in(Ty *ty)
{
        return tok()->type == TOKEN_KEYWORD &&
               tok()->keyword == KEYWORD_NOT &&
               token(1)->type == TOKEN_KEYWORD &&
               token(1)->keyword == KEYWORD_IN;
}

inline static bool
no_rhs(Ty *ty, int i)
{
        return token(i)->type == ']' ||
               token(i)->type == ')' ||
               token(i)->type == '}';
}

static void
(expect)(Ty *ty, int type)
{
        if (tok()->type != type) {
                error(
                        ty,
                        "expected %s but found %s%s%s",
                        token_show_type(ty, type),
                        TERM(34),
                        token_show(ty, tok()),
                        TERM(0)
                );
        }
}


static void
expect_keyword(Ty *ty, int type)
{
        if (tok()->type != TOKEN_KEYWORD || tok()->keyword != type) {
                error(
                        ty,
                        "expected %s but found %s%s%s",
                        token_show(ty, &(struct token){ .type = TOKEN_KEYWORD, .keyword = type }),
                        TERM(34),
                        token_show(ty, tok()),
                        TERM(0)
                );
        }
}

inline static void
(consume)(Ty *ty, int type)
{
        expect(type);
        next();
}

inline static void
consume_keyword(Ty *ty, int type)
{
        expect_keyword(ty, type);
        next();
}

inline static Expr *
try_cond(Ty *ty)
{
        if (have_keyword(KEYWORD_IF)) {
                next();
                return parse_expr(ty, 0);
        } else {
                return NULL;
        }
}

inline static void
op_fixup(Ty *ty)
{
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
        }
}

Expr *
parse_decorator_macro(Ty *ty)
{
        setctx(ty, LEX_PREFIX);

        if (token(1)->type == '}') {
                struct token id = *tok();

                next();
                unconsume(')');
                unconsume('(');

                putback(ty, id);
        }

        Expr *m = parse_expr(ty, 0);

        if (
                (
                        m->type != EXPRESSION_FUNCTION_CALL ||
                        m->function->type != EXPRESSION_IDENTIFIER
                )
                // TODO: allow . for module access here
        ) {
                EStart = m->start;
                EEnd = m->end;
                error(ty, "expected function-like macro invocation inside @{...}");
        }

        return m;
}


static expression_vector
parse_decorators(Ty *ty)
{
        expression_vector decorators = {0};

        consume(TOKEN_AT);
        consume('[');

        while (tok()->type != ']') {
                Expr *f = parse_expr(ty, 0);
                if (f->type != EXPRESSION_FUNCTION_CALL && f->type != EXPRESSION_METHOD_CALL) {
                        Expr *call = mkexpr(ty);
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
                        vvP(decorators, call);
                } else {
                        vvP(decorators, f);
                }

                if (tok()->type == ',') {
                        next();
                }
        }

        consume(']');

        return decorators;
}


/* * * * | prefix parsers | * * * */
static Expr *
prefix_integer(Ty *ty)
{
        expect(TOKEN_INTEGER);

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_INTEGER;
        e->integer = tok()->integer;

        consume(TOKEN_INTEGER);

        return e;
}

static Expr *
prefix_real(Ty *ty)
{
        expect(TOKEN_REAL);

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_REAL;
        e->real = tok()->real;

        consume(TOKEN_REAL);

        return e;
}

static char *
astrcat(Ty *ty, char const *s1, char const *s2)
{
        size_t n1 = strlen(s1);
        size_t n2 = strlen(s2);

        char *s = amA(n1 + n2 + 1);

        memcpy(s, s1, n1);
        memcpy(s + n1, s2, n2);
        s[n1 + n2] = '\0';

        return s;
}

static void
merge_strings(Ty *ty, Expr *s1, Expr *s2)
{
        if (s1->type == EXPRESSION_STRING && s2->type == EXPRESSION_STRING) {
                s1->string = astrcat(ty, s1->string, s2->string);
                return;
        }

        if (s2->type == EXPRESSION_STRING) {
                char **last = &s1->strings.items[s1->strings.count - 1];
                *last = astrcat(ty, *last, s2->string);
                return;
        }

        if (s1->type == EXPRESSION_STRING) {
                char **first = &s2->strings.items[0];
                *first = astrcat(ty, s1->string, *first);
                *s1 = *s2;
                return;
        }

        /*
         *      As1  Ae1  As2  Ae2  As3
         *
         *      Bs1  Be1  Bs2  Be2  Bs3  Be3  Bs4
         *
         *              vvvv
         *
         *      As1 Ae1 As2 Ae2 As3_Bs1 Be1 Bs2 Be2 Bs3 Be3 Bs4
         */
        char **last = vvL(s1->strings);
        *last = astrcat(ty, *last, s2->strings.items[0]);
        avPn(s1->expressions, s2->expressions.items, s2->expressions.count);
        avPn(s1->fmts, s2->fmts.items, s2->fmts.count);
        avPn(s1->widths, s2->widths.items, s2->widths.count);
        avPn(s1->strings, s2->strings.items + 1, s2->strings.count - 1);
}

Expr *
extend_string(Ty *ty, Expr *s)
{
        while (
                tok()->type == TOKEN_STRING ||
                tok()->type == TOKEN_SPECIAL_STRING ||
                (
                        tok()->type == TOKEN_IDENTIFIER &&
                        is_macro(ty, tok()->module, tok()->identifier)
                )
        ) {
                Expr *s2 = parse_expr(ty, 999);

                if (s2->type != EXPRESSION_STRING && s2->type != EXPRESSION_SPECIAL_STRING) {
                        EStart = s2->start;
                        EEnd = s2->end;
                        error(ty, "string-adjacent macro expanded to non-string: %s", ExpressionTypeName(s2));
                }

                merge_strings(ty, s, s2);
        }

        return s;
}

static Expr *
prefix_string(Ty *ty)
{
        expect(TOKEN_STRING);

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_STRING;
        e->string = tok()->string;

        consume(TOKEN_STRING);

        return extend_string(ty, e);
}

static Expr *
prefix_special_string(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_SPECIAL_STRING;
        vec_init(e->expressions);
        vec_init(e->fmts);
        vec_init(e->widths);

        vec(LexState) exprs = {
                .items = tok()->expressions.items,
                .count = tok()->expressions.count
        };

        e->strings = tok()->strings;

        next();

        int ti = TokenIndex;
        LexState cp = CtxCheckpoint;
        TokenVector ts = tokens;

        for (int i = 0; i < exprs.count;) {
                TokenIndex = 0;
                vec_init(tokens);

                lex_start(ty, &exprs.items[i]);
                lex_save(ty, &CtxCheckpoint);

                if (tok()->type == TOKEN_END) {
                        char *left = e->strings.items[i];
                        char *right = e->strings.items[i + 1];

                        char *merged = amA(strlen(left) + strlen(right) + 1);

                        strcpy(merged, left);
                        strcat(merged, right);

                        e->strings.items[i] = merged;

                        vvXi(exprs, i);
                        vvXi(e->strings, i + 1);
                } else {
                        avP(e->expressions, parse_expr(ty, 0));
                        (*vvL(e->expressions))->end = End;

                        avP(e->widths, exprs.items[i].end - exprs.items[i].loc.s + 2);

                        setctx(ty, LEX_FMT);
                        if (tok()->type == TOKEN_STRING) {
                                avP(e->fmts, tok()->string);
                                next();
                        } else {
                                avP(e->fmts, NULL);
                        }

                        i += 1;
                }

                consume(TOKEN_END);

                lex_end(ty);
        }

        TokenIndex = ti;
        CtxCheckpoint = cp;
        tokens = ts;

        // Force lexer reset
        setctx(ty, LEX_PREFIX);
        setctx(ty, LEX_INFIX);

        return extend_string(ty, e);
}

static Expr *
prefix_fun_special_string(Ty *ty)
{
        Token t = *tok();
        Expr *s = prefix_special_string(ty);
        Expr *f = mkfunc(ty);

        for (int i = 0; i < s->expressions.count; ++i) {
                Expr *p = s->expressions.items[i];

                if (!t.e_is_param.items[i]) {
                        continue;
                }

                if (p->type != EXPRESSION_IDENTIFIER) {
                        EStart = p->start;
                        EEnd = p->end;
                        error(ty, "invalid parameter in $\"\" string");
                }

                if (strcmp(p->identifier, "_") == 0) {
                        p->identifier = gensym(ty);
                }

                if (!search_str(&f->params, p->identifier)) {
                        avP(f->params, p->identifier);
                        avP(f->dflts, NULL);
                        avP(f->constraints, NULL);
                }
        }

        f->body = mkstmt(ty);
        f->body->type = STATEMENT_EXPRESSION;
        f->body->expression = s;

        return f;
}

static Expr *
prefix_hash(Ty *ty)
{
        Expr *e = mkexpr(ty);

        consume('#');

        e->type = EXPRESSION_PREFIX_HASH;
        e->operand = parse_expr(ty, 10);
        e->end = End;

        return e;
}

static Expr *
prefix_slash(Ty *ty)
{
        Location start = tok()->start;

        next();

        Expr *body = parse_expr(ty, 99);

        Expr *nil = mkexpr(ty);
        nil->type = EXPRESSION_NIL;
        nil->start = start;

        Expr *f = mkcall(ty, nil);
        avP(f->args, body);
        avP(f->fconds, NULL);

        nil->end = f->end = End;

        return mkpartial(ty, f);
}

static Expr *
prefix_dollar(Ty *ty)
{
        if (token(1)->type == '{') {
                return prefix_implicit_lambda(ty);
        }

        Expr *e = mkexpr(ty);

        consume('$');
        setctx(ty, LEX_INFIX);

        expect(TOKEN_IDENTIFIER);

        e->type = EXPRESSION_MATCH_NOT_NIL;
        e->identifier = tok()->identifier;
        e->module = tok()->module;

        if (e->module != NULL)
                error(ty, "unpexpected module in lvalue");

        consume(TOKEN_IDENTIFIER);

        e->end = End;

        return e;
}

static Expr *
prefix_identifier(Ty *ty)
{
        expect(TOKEN_IDENTIFIER);

        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_IDENTIFIER;
        e->identifier = tok()->identifier;
        e->module = tok()->module;

        consume(TOKEN_IDENTIFIER);

        if (true && is_macro(ty, e->module, e->identifier)) {
                return typarse(ty, e, &e->start, &token(-1)->end);
        }

        // Is this a macro invocation?
        if (strchr(e->identifier, '$') != NULL) {
                e->identifier = sclonea(ty, e->identifier);
                *strchr(e->identifier, '$') = '\0';
                Expr *call = infix_function_call(ty, e);
                Expr *f = mkfunc(ty);
                f->type = EXPRESSION_IMPLICIT_FUNCTION;
                f->body = mkstmt(ty);
                f->body->type = STATEMENT_EXPRESSION;
                f->body->expression = call;
                return f;
        }

        // TODO: maybe get rid of this
        if (NoEquals && tok()->type == ':') {
                next();
                e->constraint = parse_expr(ty, 0);
        } else {
                e->constraint = NULL;
        }

        e->end = End;

        return e;
}

static Expr *
prefix_eval(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_EVAL;
        next();
        consume('(');
        e->operand = parse_expr(ty, 0);
        consume(')');
        e->end = End;
        return e;
}

static Expr *
prefix_defined(Ty *ty)
{
        Expr *e;
        struct location start = tok()->start;

        next();
        consume('(');

        if (tok()->type != TOKEN_IDENTIFIER || token(1)->type != ')') {
                consume(TOKEN_IDENTIFIER);
                consume(')');
                // unreachable
        }

        e = parse_expr(ty, 0);
        e->type = EXPRESSION_DEFINED;

        consume(')');

        e->start = start;
        e->end = End;

        return e;
}

static Expr *
prefix_function(Ty *ty)
{
        Expr *e = mkfunc(ty);

        bool sugared_generator = false;

        if (tok()->type == TOKEN_AT) {
                e->decorators = parse_decorators(ty);
        }

        if (tok()->keyword == KEYWORD_GENERATOR) {
                e->type = EXPRESSION_GENERATOR;
        } else {
                e->type = EXPRESSION_FUNCTION;
        }

        next();

        if (e->type == EXPRESSION_GENERATOR)
                goto Body;

        op_fixup(ty);

        if (tok()->type == TOKEN_IDENTIFIER || tok()->type == TOKEN_USER_OP) {
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
                setctx(ty, LEX_PREFIX);

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
                avP(e->params, tok()->identifier);
                next();

                if (!special && tok()->type == ':') {
                        next();
                        avP(e->constraints, parse_expr(ty, 0));
                        (*vvL(e->constraints))->end = End;
                } else {
                        avP(e->constraints, NULL);
                }

                if (!special && tok()->type == TOKEN_EQ) {
                        next();
                        avP(e->dflts, parse_expr(ty, 0));
                        (*vvL(e->dflts))->end = End;
                } else {
                        avP(e->dflts, NULL);
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
                e->return_type = parse_expr(ty, 0);
        }

        char const *proto_end = End.s;
        size_t proto_len = proto_end - proto_start;
        char *proto = amA(proto_len + 1);
        memcpy(proto, proto_start, proto_len);
        proto[proto_len] = '\0';
        e->proto = proto;

        if (sugared_generator) {
                unconsume(TOKEN_KEYWORD);
                tok()->keyword = KEYWORD_GENERATOR;
        }

Body:
        e->body = parse_statement(ty, -1);

        if (sugared_generator) {
                char name[256];
                snprintf(name, sizeof name, "<%s:generator>", e->name);
                e->body->expression->name = sclonea(ty, name);
        }

        return e;
}

/* rewrite [ op ] as ((a, b) -> a op b) */
static Expr *
opfunc(Ty *ty)
{
        struct location start = tok()->start;

        consume('[');

        struct token t = *tok();
        next();

        consume(']');

        char *a = gensym(ty);
        char *b = gensym(ty);

        unconsume(')');

        unconsume(TOKEN_IDENTIFIER);
        tok()->module = NULL;
        tok()->identifier = b;

        putback(ty, t);

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

        Expr *e = parse_expr(ty, 0);
        e->start = start;

        return e;
}

static Expr *
prefix_at(Ty *ty)
{
        if (token(1)->type == '[')
                return prefix_function(ty);

        Location start = tok()->start;
        Location end = tok()->end;

        next();

        if (tok()->type == '{') {
                next();

                Expr *m = parse_decorator_macro(ty);

                consume('}');

                Expr *stmt = mkexpr(ty);
                stmt->type = EXPRESSION_STATEMENT;
                stmt->statement = parse_statement(ty, -1);

                avI(m->args, stmt, 0);
                avI(m->fconds, NULL, 0);

                return m;
        } else {
                unconsume('.');
                tok()->start = start;
                tok()->end = end;

                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = "self";
                tok()->module = NULL;
                tok()->start = start;
                tok()->end = end;

                return prefix_identifier(ty);
        }
}



static Expr *
prefix_star(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_MATCH_REST;
        e->module = NULL;

        consume(TOKEN_STAR);

        if (tok()->type == TOKEN_IDENTIFIER) {
                e->identifier = tok()->identifier;

                if (tok()->module != NULL)
                        error(ty, "unexpected module qualifier in lvalue");

                next();
        } else {
                e->identifier = "_";
        }

        e->end = End;

        return e;
}

static Expr *
prefix_statement(Ty *ty)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_STATEMENT;
        e->statement = parse_statement(ty, -1);
        e->end = e->statement->end;

        return e;
}

static Expr *
prefix_record(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->only_identifiers = false;
        e->type = EXPRESSION_TUPLE;
        vec_init(e->es);
        vec_init(e->names);
        vec_init(e->required);
        vec_init(e->tconds);

        consume('{');

        while (tok()->type != '}') {
                setctx(ty, LEX_PREFIX);

                if (tok()->type == TOKEN_QUESTION) {
                        next();
                        avP(e->required, false);
                } else {
                        avP(e->required, true);
                }

                if (tok()->type == TOKEN_STAR) {
                        Expr *item = mkexpr(ty);
                        next();
                        if (tok()->type == '}') {
                                item->type = EXPRESSION_MATCH_REST;
                                item->identifier = "_";
                                item->module = NULL;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                                item->value = parse_expr(ty, 0);
                                item->end = End;
                        }
                        avP(e->names, "*");
                        avP(e->es, item);
                        goto Next;
                }

                expect(TOKEN_IDENTIFIER);
                avP(e->names, tok()->identifier);

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

                avP(e->es, parse_expr(ty, 0));

Next:
                if (have_keyword(KEYWORD_IF)) {
                        next();
                        avP(e->tconds, parse_expr(ty, 0));
                } else {
                        avP(e->tconds, NULL);
                }
                if (tok()->type == ',') {
                        next();
                }
        }

        consume('}');

        e->end = End;

        return e;
}

static Expr *
patternize(Ty *ty, Expr *e);

static Expr *
next_pattern(Ty *ty)
{
        SAVE_NE(true);

        Expr *p = parse_expr(ty, 0);
        p->end = End;

        if (false && p->type == EXPRESSION_IDENTIFIER && tok()->type == ':') {
                next();
                p->constraint = parse_expr(ty, 0);
                p->constraint->end = End;
        }

        LOAD_NE();

        return patternize(ty, p);
}

static Expr *
parse_pattern(Ty *ty)
{
        Expr *pattern = next_pattern(ty);

        if (tok()->type == ',') {
                Expr *p = mkexpr(ty);

                p->type = EXPRESSION_LIST;
                p->start = pattern->start;

                vec_init(p->es);
                avP(p->es, pattern);

                while (tok()->type == ',') {
                        next();
                        avP(p->es, next_pattern(ty));
                }

                p->end = (*vvL(p->es))->end;

                pattern = p;
        }

        return pattern;
}

void
make_with(Ty *ty, Expr *e, statement_vector defs, Stmt *body)
{
        e->type = EXPRESSION_WITH;

        e->with.defs = defs;

        Stmt *try = mkstmt(ty);
        try->type = STATEMENT_TRY;
        vec_init(try->try.patterns);
        vec_init(try->try.handlers);
        try->try.s = body;

        try->try.finally = mkstmt(ty);
        try->try.finally->type = STATEMENT_DROP;
        vec_init(try->try.finally->drop);

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_MULTI;
        vec_init(s->statements);
        avPn(s->statements, defs.items, defs.count);
        avP(s->statements, try);
        e->with.block = s;

        try->start = e->start;
        try->end = body->end;
}

static Expr *
prefix_do(Ty *ty)
{
        // do
        next();
        return prefix_statement(ty);
}

static Expr *
prefix_with(Ty *ty)
{
        Expr *with = mkexpr(ty);
        statement_vector defs = {0};

        // with / use
        next();

        for (;;) {
            SAVE_NE(true);
            Expr *e = parse_expr(ty, 0);
            LOAD_NE();

            Stmt *def = mkstmt(ty);
            def->type = STATEMENT_DEFINITION;
            def->pub = false;

            if (tok()->type == TOKEN_EQ) {
                    next();
                    def->target = definition_lvalue(ty, e);
                    def->value = parse_expr(ty, 0);
            } else {
                    Expr *t = mkexpr(ty);
                    t->type = EXPRESSION_IDENTIFIER;
                    t->identifier = gensym(ty);
                    t->module = NULL;
                    def->target = t;
                    def->value = e;
            }

            avP(defs, def);

            if (tok()->type == ',') {
                    next();
            } else {
                break;
            }
        }

        make_with(ty, with, defs, parse_statement(ty, 0));

        with->end = End;

        return with;
}

static Expr *
prefix_throw(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_THROW;

        consume_keyword(ty, KEYWORD_THROW);

        e->throw = parse_expr(ty, 0);

        if (tok()->type == ';')
                next();

        e->end = End;

        return e;
}

static Expr *
prefix_yield(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_YIELD;
        vec_init(e->es);

        consume_keyword(ty, KEYWORD_YIELD);

        avP(e->es, parse_expr(ty, 1));
        while (tok()->type == ',') {
                next();
                avP(e->es, parse_expr(ty, 1));
        }

        e->end = End;

        return e;
}

static Expr *
prefix_match(Ty *ty)
{
        char *id = NULL;

        if (token(1)->type == '{') {
                Token kw = *tok();
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = id = gensym(ty);
                putback(ty, kw);
        }

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_MATCH;

        consume_keyword(ty, KEYWORD_MATCH);

        vec_init(e->patterns);
        vec_init(e->thens);

        e->subject = parse_expr(ty, -1);
        e->end = e->subject->end = End;

        SAVE_NA(false);

        if (tok()->type == TOKEN_FAT_ARROW) {
                next();
                avP(e->patterns, patternize(ty, e->subject));
                e->subject = mkexpr(ty);
                e->subject->type = EXPRESSION_IDENTIFIER;
                e->subject->identifier = id = gensym(ty);
                avP(e->thens, parse_expr(ty, 0));
                if (have_keyword(KEYWORD_ELSE)) {
                        next();
                        Expr *alt = parse_expr(ty, 0);
                        Expr *any = mkexpr(ty);
                        ZERO_EXPR(any);
                        any->type = EXPRESSION_MATCH_ANY;
                        any->identifier = "_";
                        avP(e->patterns, any);
                        avP(e->thens, alt);
                }
                goto End;
        }

        consume('{');

        avP(e->patterns, parse_pattern(ty));

        consume(TOKEN_FAT_ARROW);
        avP(e->thens, parse_expr(ty, 0));

        while (tok()->type != '}') {
                if (tok()->type == ',') {
                        next();
                }

                // Trailing comma is allowed
                if (tok()->type == '}') {
                        break;
                }

                avP(e->patterns, parse_pattern(ty));
                consume(TOKEN_FAT_ARROW);
                avP(e->thens, parse_expr(ty, 0));
        }

        consume('}');

End:
        LOAD_NA();

        if (id != NULL) {
                Expr *f = mkfunc(ty);
                avP(f->params, id);
                avP(f->dflts, NULL);
                avP(f->constraints, NULL);
                f->body = mkstmt(ty);
                f->body->type = STATEMENT_EXPRESSION;
                f->body->expression = e;
                e = f;
        }

        return e;
}

static Expr *
gencompr(Ty *ty, Expr *e)
{
        next();
        Expr *target = parse_target_list(ty);
        consume_keyword(ty, KEYWORD_IN);
        Expr *iter = parse_expr(ty, 0);
        Expr *g = mkfunc(ty);
        g->start = e->start;
        g->type = EXPRESSION_GENERATOR;
        g->body = mkstmt(ty);
        g->body->type = STATEMENT_EACH_LOOP;
        if (have_keyword(KEYWORD_IF)) {
                next();
                g->body->each.cond = parse_expr(ty, 0);
        } else {
                g->body->each.cond = NULL;
        }
        if (have_keyword(KEYWORD_WHILE)) {
                next();
                g->body->each.stop = parse_expr(ty, 0);
        } else {
                g->body->each.stop = NULL;
        }
        g->body->each.target = target;
        g->body->each.array = iter;
        g->body->each.body = mkstmt(ty);
        g->body->each.body->type = STATEMENT_EXPRESSION;
        g->body->each.body->expression = mkexpr(ty);
        g->body->each.body->expression->type = EXPRESSION_YIELD;
        vec_init(g->body->each.body->expression->es);
        avP(g->body->each.body->expression->es, e);
        g->end = End;
        return g;
}

static bool
try_parse_flag(Ty *ty, expression_vector *kwargs, StringVector *kws, expression_vector *kwconds)
{
        if (tok()->type != ':' && (tok()->type != TOKEN_BANG || !next_without_nl(ty, ':'))) {
                return false;
        }

        bool flag = (tok()->type == ':') || (next(), false);
        next();

        expect(TOKEN_IDENTIFIER);

        Expr *arg = mkexpr(ty);
        arg->type = EXPRESSION_BOOLEAN;
        arg->boolean = flag;

        avP(*kwargs, arg);
        avP(*kws, tok()->identifier);

        next();

        if (kwconds != NULL) {
                avP(*kwconds, try_cond(ty));
        }

        return true;
}

static void
next_arg(
        Ty *ty,
        expression_vector *args,
        expression_vector *conds,
        expression_vector *kwargs,
        StringVector *kws,
        expression_vector *kwconds
)
{
        if (try_parse_flag(ty, kwargs, kws, kwconds)) {
                return;
        }

        if (tok()->type == TOKEN_STAR) {
                Expr *arg = mkexpr(ty);

                next();

                if (tok()->type == TOKEN_STAR) {
                        next();
                        arg->type = EXPRESSION_SPLAT;
                } else {
                        arg->type = EXPRESSION_SPREAD;
                }

                if (
                        tok()->type == ',' ||
                        tok()->type == ')' ||
                        have_keyword(KEYWORD_IF)
                ) {
                        arg->value = mkexpr(ty);
                        arg->value->type = EXPRESSION_IDENTIFIER;
                        arg->value->module = NULL;
                        arg->value->identifier = "**" + (arg->type == EXPRESSION_SPREAD);
                        arg->end = End;
                        arg->value->start = arg->start;
                        arg->value->end = arg->end;
                } else {
                        arg->value = parse_expr(ty, 0);
                        arg->end = arg->value->end;
                }

                if (arg->type == EXPRESSION_SPLAT) {
                        avP(*kwargs, arg);
                        avP(*kws, "*");
                        if (kwconds != NULL) {
                                avP(*kwconds, try_cond(ty));
                        }
                } else {
                        avP(*args, arg);
                        avP(*conds, try_cond(ty));
                }
        } else if (
                 tok()->type == TOKEN_IDENTIFIER &&
                 (
                         token(1)->type == ':' ||
                         token(1)->type == TOKEN_EQ
                 )
        ) {
                avP(*kws, tok()->identifier);
                next();
                next();
                avP(*kwargs, parse_expr(ty, 0));
                if (kwconds != NULL) {
                        avP(*kwconds, try_cond(ty));
                }
        } else {
                avP(*args, parse_expr(ty, 0));
                avP(*conds, try_cond(ty));
        }
}

static void
parse_method_args(Ty *ty, Expr *e)
{
        vec_init(e->method_args);
        vec_init(e->mconds);
        vec_init(e->method_kwargs);
        vec_init(e->method_kws);

        consume('(');

        setctx(ty, LEX_PREFIX);

        Location start = tok()->start;

        if (tok()->type == ')') {
                goto End;
        } else {
                next_arg(
                        ty,
                        &e->method_args,
                        &e->mconds,
                        &e->method_kwargs,
                        &e->method_kws,
                        NULL
                );
        }

        if (have_keyword(KEYWORD_FOR)) {
                if (e->method_args.count > 0) {
                        *vvL(e->method_args) = gencompr(ty, *vvL(e->method_args));
                } else {
                        EStart = start;
                        EEnd = tok()->end;
                        error(ty, "malformed generator comprehension argument");
                }
        }

        while (tok()->type == ',') {
                next();
                setctx(ty, LEX_PREFIX);
                next_arg(
                        ty,
                        &e->method_args,
                        &e->mconds,
                        &e->method_kwargs,
                        &e->method_kws,
                        NULL
                );
        }

End:
        consume(')');

        e->end = End;
}

static Expr *
parse_method_call(Ty *ty, Expr *e)
{
        vec_init(e->method_args);
        vec_init(e->mconds);
        vec_init(e->method_kws);
        vec_init(e->method_kwargs);

        switch (tok()->type) {
        case '(':
                parse_method_args(ty, e);
                e->end = End;
                return e;
        case TOKEN_AT:
                next();
                parse_method_args(ty, e);
                e->end = End;
                return mkpartial(ty, e);
        case '\\':
                next();
                break;
        default:
                return e;
        }

        next();
        Expr *body = parse_expr(ty, 0);
        next();

        Expr *nil = mkexpr(ty);
        nil->type = EXPRESSION_NIL;

        Expr *f = mkcall(ty, nil);
        avP(f->args, body);
        avP(f->fconds, NULL);

        avP(e->method_args, mkpartial(ty, f));
        avP(e->mconds, NULL);

        e->end = End;

        return e;
}

inline static bool
has_names(Expr const *e)
{
        for (int i = 0; e->names.count; ++i) {
                if (e->names.items[i] != NULL) {
                        return true;
                }
        }

        return false;
}

static Expr *
prefix_parenthesis(Ty *ty)
{
        /*
         * This can either be a plain old parenthesized expression, e.g., (4 + 4)
         * or it can be an identifier list for an arrow function, e.g., (a, b, c).
         */

        struct location start = tok()->start;
        Expr *e;

        consume('(');

        /*
         * () is an empty identifier list.
         */
        if (tok()->type == ')') {
                next();
                e = mkexpr(ty);
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
        if (get_infix_parser(ty) != NULL && get_prefix_parser(ty) == NULL) {
                e = mkfunc(ty);
                avP(e->params, gensym(ty));
                avP(e->dflts, NULL);
                avP(e->constraints, NULL);

                Expr *t = mkexpr(ty);
                t->type = EXPRESSION_IDENTIFIER;
                t->identifier = e->params.items[0];
                t->module = NULL;

                e->body = mkstmt(ty);
                e->body->type = STATEMENT_EXPRESSION;
                e->body->expression = get_infix_parser(ty)(ty, t);

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
        e = parse_expr(ty, 0);
        LOAD_NE();

        if (e->type == EXPRESSION_EQ || e->type == EXPRESSION_MAYBE_EQ) {
                expect(')');
        }

        if (tok()->type == ',' || tok()->type == ':') {
                Expr *list = mkexpr(ty);
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
                        avP(list->names, e->identifier);
                        e = parse_expr(ty, 0);
                } else {
                        avP(list->names, NULL);
                }

                e->end = End;
                avP(list->es, e);
                avP(list->required, true);

                if (have_keyword(KEYWORD_IF)) {
                        next();
                        avP(list->tconds, parse_expr(ty, 0));
                } else {
                        avP(list->tconds, NULL);
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
                                avP(list->required, false);
                        } else {
                                avP(list->required, true);
                        }

                        if (tok()->type == TOKEN_IDENTIFIER && token(1)->type == ':') {
                                avP(list->names, tok()->identifier);
                                next();
                                next();
                        } else {
                                avP(list->names, NULL);
                        }

                        Expr *e = parse_expr(ty, 0);
                        e->end = tok()->end;
                        if (e->type == EXPRESSION_MATCH_REST) {
                                expect(')');
                        } else if (e->type != EXPRESSION_IDENTIFIER) {
                                list->only_identifiers = false;
                        }

                        avP(list->es, e);

                        if (have_keyword(KEYWORD_IF)) {
                                next();
                                avP(list->tconds, parse_expr(ty, 0));
                        } else {
                                avP(list->tconds, NULL);
                        }
                }

                consume(')');

                list->end = End;

                return list;
        } else if (have_keyword(KEYWORD_FOR)) {
                e = gencompr(ty, e);
                consume(')');
                return e;
        } else {
                consume(')');

                if (e->type == EXPRESSION_TUPLE && !has_names(e)) {
                        Expr *list = mkexpr(ty);
                        list->start = start;
                        list->only_identifiers = false;
                        list->type = EXPRESSION_TUPLE;
                        vec_init(list->names);
                        vec_init(list->es);
                        vec_init(list->tconds);
                        vec_init(list->required);
                        avP(list->names, NULL);
                        avP(list->required, true);
                        avP(list->es, e);
                        avP(list->tconds, NULL);
                        return list;
                } else {
                        e->start = start;
                        e->end = End;
                        return e;
                }
        }
}

static Expr *
prefix_true(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_BOOLEAN;
        e->boolean = true;

        consume_keyword(ty, KEYWORD_TRUE);

        return e;
}

static Expr *
prefix_false(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_BOOLEAN;
        e->boolean = false;

        consume_keyword(ty, KEYWORD_FALSE);

        return e;
}

static Expr *
prefix_self(Ty *ty)
{

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_SELF;

        consume_keyword(ty, KEYWORD_SELF);

        return e;
}

static Expr *
prefix_nil(Ty *ty)
{

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_NIL;

        consume_keyword(ty, KEYWORD_NIL);

        return e;
}

static Expr *
prefix_regex(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_REGEX;
        e->regex = tok()->regex;

        consume(TOKEN_REGEX);

        return e;
}


static Expr *
prefix_array(Ty *ty)
{
        setctx(ty, LEX_INFIX);

        if (token(2)->type == ']') switch (token(1)->type) {
        case TOKEN_USER_OP:
        case TOKEN_PERCENT:
        case TOKEN_PLUS:
        case TOKEN_MINUS:
        //case TOKEN_STAR:
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
                return opfunc(ty);
        default: break;
        }

        Expr *e, *f;

        struct location start = tok()->start;

        int in_type = EXPRESSION_IN;

        if (token(1)->type == TOKEN_KEYWORD) switch (token(1)->keyword) {
        case KEYWORD_IN:
        InSection:
                next();
                next();
                e = parse_expr(ty, 0);
                consume(']');
                f = mkfunc(ty);
                avP(f->params, gensym(ty));
                avP(f->dflts, NULL);
                avP(f->constraints, NULL);
                f->body = mkstmt(ty);
                f->body->type = STATEMENT_EXPRESSION;
                f->body->expression = mkexpr(ty);
                f->body->expression->type = in_type;
                f->body->expression->left = mkexpr(ty);
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

        e = mkexpr(ty);
        e->type = EXPRESSION_ARRAY;
        vec_init(e->elements);
        vec_init(e->aconds);
        vec_init(e->optional);

        consume('[');

        while (tok()->type != ']') {
                setctx(ty, LEX_PREFIX);
                if (tok()->type == TOKEN_STAR) {
                        Expr *item = mkexpr(ty);
                        next();

                        item->type = EXPRESSION_SPREAD;
                        if (tok()->type == ']' || tok()->type == ',') {
                                item->value = mkexpr(ty);
                                item->value->type = EXPRESSION_IDENTIFIER;
                                item->value->module = NULL;
                                item->value->identifier = "*";
                                item->value->start = item->start;
                                item->value->end = item->end = End;
                        } else {
                                item->value = parse_expr(ty, 0);
                        }

                        item->end = End;

                        avP(e->elements, item);
                        avP(e->optional, false);
                } else {
                        if (tok()->type == TOKEN_QUESTION) {
                                next();
                                avP(e->optional, true);
                        } else {
                                avP(e->optional, false);
                        }
                        avP(e->elements, parse_expr(ty, 0));
                }

                if (have_keyword(KEYWORD_IF)) {
                        next();
                        avP(e->aconds, parse_expr(ty, 0));
                } else {
                        avP(e->aconds, NULL);
                }

                if (have_keyword(KEYWORD_FOR)) {
                        next();
                        e->type = EXPRESSION_ARRAY_COMPR;
                        e->compr.pattern = parse_target_list(ty);
                        consume_keyword(ty, KEYWORD_IN);
                        e->compr.iter = parse_expr(ty, 0);
                        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IF) {
                                next();
                                e->compr.cond = parse_expr(ty, 0);
                        } else {
                                e->compr.cond = NULL;
                        }
                        expect(']');
                } else if (tok()->type == ',') {
                        next();
                } else if (
                        e->elements.count == 1 &&
                        get_infix_parser(ty) != NULL &&
                        (token(1)->type == ']' || (have_not_in(ty) && token(2)->type == ']'))
                ) {
                        f = mkfunc(ty);
                        avP(f->params, gensym(ty));
                        avP(f->dflts, NULL);
                        avP(f->constraints, NULL);
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
                                putback(ty, t2);
                        }
                        putback(ty, t);
                        f->body = mkstmt(ty);
                        f->body->type = STATEMENT_EXPRESSION;
                        f->body->expression = get_infix_parser(ty)(ty, e->elements.items[0]);
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

static Expr *
prefix_template(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_TEMPLATE;

        next();

        expression_vector TESave = TemplateExprs;
        vec_init(TemplateExprs);
        vec_init(e->template.stmts);

        while (tok()->type != TOKEN_TEMPLATE_END) {
                avP(e->template.stmts, parse_statement(ty, 0));
        }

        next();

        e->end = End;

        e->template.exprs = TemplateExprs;
        TemplateExprs = TESave;

        return e;
}

static Expr *
prefix_template_expr(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_TEMPLATE_HOLE;
        e->integer = TemplateExprs.count;

        next();

        if (tok()->type == '(') {
                next();
                avP(TemplateExprs, parse_expr(ty, 0));
                consume(')');
        } else if (tok()->type == '{') {
                e->type = EXPRESSION_TEMPLATE_VHOLE;
                next();
                avP(TemplateExprs, parse_expr(ty, 0));
                consume('}');
        } else {
                avP(TemplateExprs, parse_expr(ty, 99));
        }

        e->end = End;

        return e;
}

static Expr *
prefix_carat(Ty *ty)
{
        consume('^');
        Expr *id = prefix_identifier(ty);
        id->type = EXPRESSION_RESOURCE_BINDING;
        return id;
}

static Expr *
prefix_tick(Ty *ty)
{
        Expr *e;
        struct location start = tok()->start;

        next();

        if (tok()->type != TOKEN_IDENTIFIER || token(1)->type != '`') {
                consume(TOKEN_IDENTIFIER);
                consume('`');
                // unreachable
        }

        e = parse_expr(ty, 0);
        e->type = EXPRESSION_IFDEF;

        consume('`');

        e->start = start;
        e->end = End;

        return e;
}

static Expr *
prefix_incrange(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_DOT_DOT_DOT;

        Expr *zero = mkexpr(ty);
        zero->type = EXPRESSION_INTEGER;
        zero->integer = 0;

        consume(TOKEN_DOT_DOT_DOT);

        e->left = zero;
        e->right = parse_expr(ty, 7);
        e->end = e->right->end;

        return e;
}

static Expr *
prefix_range(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_DOT_DOT;

        Expr *zero = mkexpr(ty);
        zero->type = EXPRESSION_INTEGER;
        zero->integer = 0;

        consume(TOKEN_DOT_DOT);

        e->left = zero;
        e->right = no_rhs(ty, 0) ? NULL : parse_expr(ty, 7);
        e->end = End;

        return e;
}

static Expr *
implicit_subscript(Ty *ty, Expr *o)
{
        consume('[');

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_SUBSCRIPT;
        e->sc = NULL;
        e->container = o;

        setctx(ty, LEX_PREFIX);
        e->subscript = parse_expr(ty, 0);

        consume(']');

        Expr *f = mkfunc(ty);
        f->body = mkret(ty, e);

        avP(f->params, o->identifier);
        avP(f->dflts, NULL);
        avP(f->constraints, NULL);

        return f;
}

static Expr *
prefix_implicit_method(Ty *ty)
{
        Location start = tok()->start;

        consume('&');

        if (tok()->type == '{') {
                return prefix_implicit_lambda(ty);
        }

        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_NOT) {
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = "__not__";
                tok()->module = NULL;
        }

        Expr *o = mkexpr(ty);
        o->type = EXPRESSION_IDENTIFIER;
        o->identifier = gensym(ty);
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
                return implicit_subscript(ty, o);
        }

        bool maybe = false;
        if (tok()->type == TOKEN_QUESTION) {
                next();
                maybe = true;
        }

        Expr *e = mkexpr(ty);
        e->maybe = false;
        e->start = start;

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
                e->maybe = maybe;
                e->object = o;
                e->method_name = tok()->identifier;
                next();

                e = parse_method_call(ty, e);
        }

        Expr *f = mkfunc(ty);
        f->body = mkret(ty, e);
        f->start = start;
        f->end = End;

        avP(f->params, o->identifier);
        avP(f->dflts, NULL);
        avP(f->constraints, NULL);

        return f;
}

static Expr *
prefix_colon(Ty *ty)
{
        tok()->type = '&';
        return prefix_implicit_method(ty);
}

static Expr *
prefix_implicit_lambda(Ty *ty)
{
        consume('$');
        consume('{');

        Expr *e = parse_expr(ty, 0);

        consume('}');


        Expr *f = mkfunc(ty);
        f->type = EXPRESSION_IMPLICIT_FUNCTION;
        f->body = mkstmt(ty);
        f->body->type = STATEMENT_EXPRESSION;
        f->body->expression = e;

        return f;
}

static Expr *
prefix_bit_or(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_LIST;
        e->only_identifiers = true;
        vec_init(e->es);

        next();

        SAVE_NE(true);
        SAVE_NP(true);
        for (int i = 0; tok()->type != '|'; ++i) {
                Expr *item = parse_expr(ty, 1);
                e->only_identifiers &= (item->type == EXPRESSION_IDENTIFIER);
                avP(e->es, item);
                if (tok()->type != '|')
                        consume(',');
        }
        LOAD_NE();
        LOAD_NP();

        consume('|');

        e->end = End;

        return e;
}

static Expr *
prefix_arrow(Ty *ty)
{
        Location start = tok()->start;

        unconsume(')');
        unconsume('(');

        Expr *f = parse_expr(ty, 0);
        f->type = EXPRESSION_IMPLICIT_FUNCTION;
        f->start = start;
        f->end = End;

        return f;
}

static Expr *
prefix_expr(Ty *ty)
{
        Expr *e = tok()->e;
        next();
        return e;
}

static Expr *
prefix_percent(Ty *ty)
{
        Expr *e = mkexpr(ty);
        consume(TOKEN_PERCENT);

        if (tok()->type == TOKEN_IDENTIFIER) {
                if (tok()->module != NULL && *tok()->module != '\0') {
                        next();
                        EStart = e->start;
                        EEnd = End;
                        error(ty, "unexpected module qualifier in tag binding pattern");
                }
                if (token(1)->type != '(') {
                        next();
                        consume('(');
                }
                Expr *call = parse_expr(ty, 10);
                call->type = EXPRESSION_TAG_PATTERN_CALL;
                call->start = e->start;
                call->end = End;
                return call;
        }

        e->type = EXPRESSION_DICT;
        e->dflt = NULL;

        consume('{');

        vec_init(e->keys);
        vec_init(e->values);

        while (tok()->type != '}') {
                if (tok()->type == TOKEN_STAR && token(1)->type == ':') {
                        struct location start = tok()->start;
                        next();
                        next();
                        unconsume(TOKEN_ARROW);
                        e->dflt = parse_expr(ty, 0);
                        e->dflt->start = start;
                        e->dflt->end = End;
                } else if (tok()->type == TOKEN_STAR) {
                        Expr *item = mkexpr(ty);
                        next();
                        if (tok()->type == TOKEN_STAR) {
                                next();
                                item->type = EXPRESSION_SPLAT;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                        }

                        if (tok()->type == ',' || tok()->type == '}') {
                                item->value = mkexpr(ty);
                                item->value->type = EXPRESSION_IDENTIFIER;
                                item->value->module = NULL;
                                item->value->identifier = "**" + (item->type == EXPRESSION_SPREAD);
                                item->value->start = item->start;
                                item->value->end = item->end = End;
                        } else {
                                item->value = parse_expr(ty, 0);
                                item->end = End;
                        }

                        avP(e->keys, item);
                        avP(e->values, NULL);
                } else {
                        Expr *key = parse_expr(ty, 0);
                        avP(e->keys, key);
                        if (key->type == EXPRESSION_IDENTIFIER) {
                                avP(e->values, key->constraint);
                                key->constraint = NULL;
                        } else {
                                avP(e->values, NULL);
                        }
                        if (tok()->type == ':') {
                                next();
                                *vvL(e->values) = parse_expr(ty, 0);
                        }
                }

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_FOR) {
                        next();
                        e->type = EXPRESSION_DICT_COMPR;
                        e->dcompr.pattern = parse_target_list(ty);
                        consume_keyword(ty, KEYWORD_IN);
                        e->dcompr.iter = parse_expr(ty, 0);
                        if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IF) {
                                next();
                                e->dcompr.cond = parse_expr(ty, 0);
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

Expr *
mkcall(Ty *ty, Expr *func)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_FUNCTION_CALL;
        e->function = func;
        e->start = func->start;
        vec_init(e->args);
        vec_init(e->kws);
        vec_init(e->kwargs);
        vec_init(e->fconds);
        vec_init(e->fkwconds);

        return e;
}

static Expr *
mkpartial(Ty *ty, Expr *sugared)
{
        Expr *fun = mkexpr(ty);
        fun->type = EXPRESSION_IDENTIFIER;
        fun->identifier = "__desugar_partial__";
        fun->module = NULL;

        Expr *call = mkcall(ty, fun);
        avP(call->args, sugared);
        avP(call->fconds, NULL);

        call->start = sugared->start;
        call->end = sugared->end;

        return call;
}

/* * * * | infix parsers | * * * */
static Expr *
infix_function_call(Ty *ty, Expr *left)
{
        Expr *e = mkcall(ty, left);

        consume('(');

        setctx(ty, LEX_PREFIX);

        Location start = tok()->start;

        if (tok()->type == ')') {
                next();
                e->end = End;
                return e;
        }

        next_arg(
                ty,
                &e->args,
                &e->fconds,
                &e->kwargs,
                &e->kws,
                &e->fkwconds
        );

        if (have_keyword(KEYWORD_FOR)) {
                if (e->args.count > 0) {
                        *vvL(e->args) = gencompr(ty, *vvL(e->args));
                } else {
                        EStart = start;
                        EEnd = tok()->end;
                        error(ty, "malformed generator comprehension argument");
                }
        }

        while (tok()->type == ',') {
                next();
                setctx(ty, LEX_PREFIX);
                next_arg(
                        ty,
                        &e->args,
                        &e->fconds,
                        &e->kwargs,
                        &e->kws,
                        &e->fkwconds
                );
        }

        consume(')');

        e->end = End;

        return e;
}

static Expr *
infix_eq(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = tok()->type == TOKEN_EQ ? EXPRESSION_EQ : EXPRESSION_MAYBE_EQ;
        next();

        e->start = left->start;
        e->target = assignment_lvalue(ty, left);

        if (left->type == EXPRESSION_LIST) {
                e->value = parse_expr(ty, -1);
        } else {
                e->value = parse_expr(ty, 1);
        }

        e->end = e->value->end;

        return e;
}

static Expr *
prefix_user_op(Ty *ty)
{
        error(ty, "not implemented");
}

static Expr *
infix_user_op(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_USER_OP;
        e->start = left->start;
        e->left = left;
        e->op_name = tok()->identifier;
        consume(TOKEN_USER_OP);

        int prec = 8;

        struct value *p = table_look(ty, &uops, e->op_name);
        if (p != NULL) {
                prec = (p->integer > 0) ? p->integer : llabs(p->integer) - 1;
        }

        struct value *sc = table_look(ty, &uopcs, e->op_name);
        if (sc != NULL) {
                e->sc = sc->ptr;
        } else {
                e->sc = NULL;
        }

        e->right = parse_expr(ty, prec);
        e->end = End;

        return e;
}

static Expr *
infix_list(Ty *ty, Expr *left)
{

        Expr *e = mkexpr(ty);
        e->start = left->start;
        e->type = EXPRESSION_LIST;
        vec_init(e->es);
        avP(e->es, left);

        bool ne = NoEquals;
        NoEquals = true;

        while (tok()->type == ',') {
                next();
                avP(e->es, parse_expr(ty, 1));
        }

        NoEquals = ne;

        e->end = End;

        return e;
}

static Expr *
infix_count_from(Ty *ty, Expr *left)
{
        next();

        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_DOT_DOT;
        e->start = left->start;
        e->left = left;
        e->right = NULL;
        e->end = End;

        return e;
}

static Expr *
infix_subscript(Ty *ty, Expr *left)
{

        Expr *e = mkexpr(ty);

        consume('[');

        Expr *i;
        if (tok()->type == ';') {
                i = NULL;
        } else {
                i = parse_expr(ty, 0);
        }

        if (tok()->type == ']' && i != NULL) {
                e->type = EXPRESSION_SUBSCRIPT;
                e->container = left;
                e->subscript = i;
                goto End;
        }

        consume(';');

        e->type = EXPRESSION_SLICE;
        e->slice.e = left;
        e->slice.i = i;
        e->slice.j = NULL;
        e->slice.k = NULL;

        if (tok()->type != ']' && tok()->type != ';') {
                e->slice.j = parse_expr(ty, 0);
        }

        if (tok()->type == ']') {
                goto End;
        }

        consume(';');

        if (tok()->type != ']') {
                e->slice.k = parse_expr(ty, 0);
        }

End:
        consume(']');

        e->end = End;

        return e;
}

static Expr *
infix_alias(Ty *ty, Expr *left)
{
        consume_keyword(ty, KEYWORD_AS);

        Expr *alias = parse_expr(ty, 0);

        if (alias->type != EXPRESSION_IDENTIFIER) {
                EStart = alias->start;
                EEnd = alias->end;
                error(ty, "pattern alias must be an identifier");
        }

        alias->type = EXPRESSION_ALIAS_PATTERN;
        alias->aliased = left;

        return alias;
}

static Expr *
infix_member_access(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->start = left->start;
        e->maybe = tok()->type == TOKEN_DOT_MAYBE;

        next();

        /*
         * xs.N is syntactic sugar for xs[N]
         */
        if (tok()->type == TOKEN_INTEGER) {
                e->type = EXPRESSION_SUBSCRIPT;
                e->container = left;
                e->subscript = mkexpr(ty);
                e->subscript->type = EXPRESSION_INTEGER;
                e->subscript->integer = tok()->integer;
                next();
                e->start = left->start;
                e->end = End;
                return e;
        }

        e->object = left;

        expect(TOKEN_IDENTIFIER);
        char *id = tok()->identifier;
        consume(TOKEN_IDENTIFIER);

        if (!have_without_nl(ty, '(') && !have_without_nl(ty, '$') && !have_without_nl(ty, TOKEN_AT)) {
                e->type = EXPRESSION_MEMBER_ACCESS;
                e->member_name = id;
                e->end = End;
                return e;
        }

        e->method_name = id;
        e->type = EXPRESSION_METHOD_CALL;

        return parse_method_call(ty, e);
}

static Expr *
infix_squiggly_not_nil_arrow(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_NOT_NIL_VIEW_PATTERN;

        consume('$~>');

        e->left = left;
        e->right = parse_expr(ty, 0);
        e->start = left->start;
        e->end = End;

        return e;
}

static Expr *
infix_squiggly_arrow(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_VIEW_PATTERN;

        consume(TOKEN_SQUIGGLY_ARROW);

        e->left = left;
        e->right = parse_expr(ty, 0);
        e->start = left->start;
        e->end = End;

        return e;
}

static Expr *
infix_arrow_function(Ty *ty, Expr *left)
{

        consume(TOKEN_ARROW);

        Expr *e = mkfunc(ty);
        e->start = left->start;

        if (left->type != EXPRESSION_LIST && (left->type != EXPRESSION_TUPLE || !left->only_identifiers)) {
                Expr *l = mkexpr(ty);
                l->type = EXPRESSION_LIST;
                vec_init(l->es);
                avP(l->es, left);
                left = l;
        } else {
                left->type = EXPRESSION_LIST;
        }

        Stmt *body = mkstmt(ty);
        body->type = STATEMENT_BLOCK;
        vec_init(body->statements);

        for (int i = 0; i < left->es.count; ++i) {
                Expr *p = left->es.items[i];
                if (p->type == EXPRESSION_IDENTIFIER) {
                        avP(e->params, p->identifier);
                } else if (p->type == EXPRESSION_MATCH_REST) {
                        avP(e->params, p->identifier);
                        e->rest = i;
                } else {
                        char *name = gensym(ty);
                        avP(e->params, name);
                        avP(body->statements, mkdef(ty, definition_lvalue(ty, p), name));
                }
                avP(e->dflts, NULL);
                avP(e->constraints, NULL);
        }

        Stmt *ret = mkret(ty, parse_expr(ty, 0));

        if (body->statements.count == 0) {
                e->body = ret;
        } else {
                avP(body->statements, ret);
                e->body = body;
        }

        e->end = End;

        return e;
}

static Expr *
infix_kw_or(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_LIST;
        vec_init(e->es);

        avP(e->es, left);

        do {
                next();
                avP(e->es, parse_expr(ty, 1));
        } while (have_keyword(KEYWORD_OR));

        e->start = left->start;
        e->end = End;

        return e;
}

static Expr *
infix_kw_and(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_KW_AND;
        e->left = left;
        e->start = left->start;

        consume_keyword(ty, KEYWORD_AND);

        e->p_cond = parse_condparts(ty, false);

        e->end = End;

        return e;
}

static Expr *
infix_kw_in(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->left = left;
        e->start = left->start;

        if (tok()->keyword == KEYWORD_NOT) {
                next();
                e->type = EXPRESSION_NOT_IN;
        } else {
                e->type = EXPRESSION_IN;
        }

        consume_keyword(ty, KEYWORD_IN);

        e->right = parse_expr(ty, 3);
        e->end = e->right->end;

        return e;
}

static Expr *
infix_at(Ty *ty, Expr *left)
{
        next();
        return mkpartial(ty, infix_function_call(ty, left));
}

static Expr *
infix_slash(Ty *ty, Expr *left)
{
        next();
        next();

        Expr *body = parse_expr(ty, 0);

        next();

        Expr *nil = mkexpr(ty);
        nil->type = EXPRESSION_NIL;

        Expr *f = mkcall(ty, nil);
        avP(f->args, body);
        avP(f->fconds, NULL);

        Expr *call = mkcall(ty, left);
        avP(call->args, mkpartial(ty, f));
        avP(call->fconds, NULL);

        return call;
}

static Expr *
infix_conditional(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_CONDITIONAL;

        e->cond = left;

        consume(TOKEN_QUESTION);

        e->then = parse_expr(ty, 2);

        consume(':');

        e->otherwise = parse_expr(ty, 2);

        return e;
}

static Expr *
postfix_inc(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->start = left->start;

        consume(TOKEN_INC);

        e->type = EXPRESSION_POSTFIX_INC;
        e->operand = assignment_lvalue(ty, left);
        e->end = End;

        return e;
}

static Expr *
postfix_dec(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->start = left->start;

        consume(TOKEN_DEC);

        e->type = EXPRESSION_POSTFIX_DEC;
        e->operand = assignment_lvalue(ty, left);
        e->end = End;

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

static prefix_parse_fn *
get_prefix_parser(Ty *ty)
{
        setctx(ty, LEX_PREFIX);

        switch (tok()->type) {
        case TOKEN_INTEGER:            return prefix_integer;
        case TOKEN_REAL:               return prefix_real;
        case TOKEN_STRING:             return prefix_string;
        case TOKEN_SPECIAL_STRING:     return prefix_special_string;
        case TOKEN_FUN_SPECIAL_STRING: return prefix_fun_special_string;
        case TOKEN_REGEX:              return prefix_regex;

        case TOKEN_IDENTIFIER:         return prefix_identifier;
        case TOKEN_KEYWORD:            goto Keyword;

        case '&':                      return prefix_implicit_method;
        case TOKEN_PERCENT:            return prefix_percent;
        case '#':                      return prefix_hash;

        case '(':                      return prefix_parenthesis;
        case '[':                      return prefix_array;
        case '{':                      return prefix_record;

        case '\\':                     return prefix_slash;
        case '$':                      return prefix_dollar;
        case '`':                      return prefix_tick;
        case '^':                      return prefix_carat;

        case TOKEN_TEMPLATE_BEGIN:     return prefix_template;
        case '$$':                     return prefix_template_expr;

        case TOKEN_DOT_DOT:            return prefix_range;
        case TOKEN_DOT_DOT_DOT:        return prefix_incrange;

        case TOKEN_QUESTION:           return prefix_is_nil;
        case TOKEN_BANG:               return prefix_bang;
        case TOKEN_AT:                 return prefix_at;
        case TOKEN_MINUS:              return prefix_minus;
        case TOKEN_INC:                return prefix_inc;
        case TOKEN_DEC:                return prefix_dec;
        case TOKEN_USER_OP:            return prefix_user_op;

        case TOKEN_ARROW:              return prefix_arrow;

        case '|':                      return prefix_bit_or;

        case TOKEN_STAR:               return prefix_star;

        case TOKEN_EXPRESSION:         return prefix_expr;

        default:                       return NULL;
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
        case KEYWORD_THROW:     return prefix_throw;
        case KEYWORD_WITH:      return prefix_with;
        case KEYWORD_DO:        return prefix_do;

        case KEYWORD_IF:
        case KEYWORD_FOR:
        case KEYWORD_WHILE:
        case KEYWORD_TRY:
                return prefix_statement;

        default:                return NULL;
        }
}

static infix_parse_fn *
get_infix_parser(Ty *ty)
{
        setctx(ty, LEX_INFIX);

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

        case TOKEN_DOT_DOT:        return no_rhs(ty, 1) ? infix_count_from : infix_range;
        case TOKEN_DOT_DOT_DOT:    return no_rhs(ty, 1) ? infix_count_from : infix_incrange;

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

        case '\\':     return next_without_nl(ty, '(') ? infix_slash  : NULL;
        case TOKEN_AT: return next_without_nl(ty, '(') ? infix_at     : NULL;

        default:                   return NULL;
        }

Keyword:

        switch (tok()->keyword) {
        case KEYWORD_AND: return infix_kw_and;
        case KEYWORD_OR:  return infix_kw_or;
        case KEYWORD_NOT:
        case KEYWORD_IN:  return infix_kw_in;
        case KEYWORD_AS:  return infix_alias;
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
get_infix_prec(Ty *ty)
{
        struct value *p;
        setctx(ty, LEX_INFIX);

        switch (tok()->type) {
        case '.':                  return 12;
        case TOKEN_DOT_MAYBE:      return 12;

        case '[':                  return 11;
        case '(':                  return 11;
        case '\\': case TOKEN_AT:  return next_without_nl(ty, '(') ? 11 : -3;

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
        case KEYWORD_OR: return NoAndOr ? -3 : 1;

        case KEYWORD_AND: return NoAndOr ? -3 : 4;

        case KEYWORD_NOT:
        case KEYWORD_IN:  return NoIn ? -3 : 6;

        case KEYWORD_AS:  return 1;

        default:          return -3;
        }

UserOp:
        p = table_look(ty, &uops, tok()->identifier);
        return (p != NULL) ? llabs(p->integer) : 8;
}

static Expr *
definition_lvalue(Ty *ty, Expr *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") == 0 && e->module == NULL) {
                        e->type = EXPRESSION_MATCH_ANY;
                }
                /* fallthrough */
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_TAG_PATTERN_CALL:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_SPREAD:
        case EXPRESSION_TEMPLATE_HOLE:
                return e;
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        e->es.items[i] = definition_lvalue(ty, e->es.items[i]);
                }
                return e;
        case EXPRESSION_FUNCTION_CALL:
                for (int i = 0; i < e->args.count; ++i) {
                        e->args.items[i] = definition_lvalue(ty, e->args.items[i]);
                }
                return e;
        case EXPRESSION_METHOD_CALL:
                if (e->object->type != EXPRESSION_IDENTIFIER) {
                        break;
                }
                for (int i = 0; i < e->method_args.count; ++i) {
                        e->method_args.items[i] = definition_lvalue(ty, e->method_args.items[i]);
                }
                for (int i = 0; i < e->method_kwargs.count; ++i) {
                        e->method_kwargs.items[i] = definition_lvalue(ty, e->method_kwargs.items[i]);
                }
                return e;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                e->right = definition_lvalue(ty, e->right);
                return e;
        case EXPRESSION_ARRAY:
                if (e->elements.count == 0)
                        break;
                for (size_t i = 0; i < e->elements.count; ++i)
                        e->elements.items[i] = assignment_lvalue(ty, e->elements.items[i]);
                return e;
        case EXPRESSION_DICT:
                if (e->keys.count == 0)
                        break;
                for (size_t i = 0; i < e->elements.count; ++i) {
                        if (e->values.items[i] == NULL) {
                                Expr *key = mkexpr(ty);
                                if (e->keys.items[i]->type != EXPRESSION_IDENTIFIER) {
                                        EStart = e->keys.items[i]->start;
                                        EEnd = e->keys.items[i]->end;
                                        error(ty, "short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = assignment_lvalue(ty, e->values.items[i]);
                }
                return e;
        }

        error(ty, "expression is not a valid definition lvalue: %s", ExpressionTypeName(e));
}

static Expr *
patternize(Ty *ty, Expr *e)
{
        try_symbolize_application(ty, NULL, e);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") == 0 && e->module == NULL) {
                        e->type = EXPRESSION_MATCH_ANY;
                }
                return e;
        case EXPRESSION_TAG_APPLICATION:
                e->tagged = patternize(ty, e->tagged);
                return e;
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        e->es.items[i] = patternize(ty, e->es.items[i]);
                }
                return e;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i)
                        e->elements.items[i] = patternize(ty, e->elements.items[i]);
                return e;
        case EXPRESSION_DICT:
                for (size_t i = 0; i < e->keys.count; ++i) {
                        if (e->values.items[i] == NULL) {
                                Expr *key = mkexpr(ty);
                                if (e->keys.items[i]->type != EXPRESSION_IDENTIFIER) {
                                        EStart = key->start;
                                        EEnd = key->end;
                                        error(ty, "short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = patternize(ty, e->values.items[i]);
                }
                return e;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                e->right = patternize(ty, e->right);
                return e;
        case EXPRESSION_ALIAS_PATTERN:
                e->aliased = patternize(ty, e->aliased);
                return e;
        default:
                return e;
        }
}

static Expr *
assignment_lvalue(Ty *ty, Expr *e)
{
        Expr *v;

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") == 0 && e->module == NULL) {
                        //e->type = EXPRESSION_MATCH_ANY;
                }
                /* fallthrough */
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_SUBSCRIPT:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_FUNCTION_CALL:
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
        case EXPRESSION_SPREAD:
                return e;
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < e->es.count; ++i) {
                        e->es.items[i] = assignment_lvalue(ty, e->es.items[i]);
                }
                return e;
        case EXPRESSION_ARRAY:
                for (size_t i = 0; i < e->elements.count; ++i)
                        e->elements.items[i] = assignment_lvalue(ty, e->elements.items[i]);
                return e;
        case EXPRESSION_DICT:
                for (size_t i = 0; i < e->keys.count; ++i) {
                        if (e->values.items[i] == NULL) {
                                Expr *key = mkexpr(ty);
                                if (e->keys.items[i]->type != EXPRESSION_IDENTIFIER) {
                                        EStart = key->start;
                                        EEnd = key->end;
                                        error(ty, "short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = assignment_lvalue(ty, e->values.items[i]);
                }
                return e;
        default:
                error(ty, "expression is not a valid assignment lvalue: %s", ExpressionTypeName(e));
        }
}

/*
 * This is kind of a hack.
 */
static Expr *
parse_definition_lvalue(Ty *ty, int context)
{
        Expr *e;
        int save = TokenIndex;

        SAVE_NI(true);
        SAVE_NE(true);
        e = parse_expr(ty, 1);
        EStart = e->start;
        EEnd = e->end;
        e = definition_lvalue(ty, e);
        LOAD_NE();
        LOAD_NI();

        if (context == LV_LET && tok()->type == ',') {
                Expr *l = mkexpr(ty);
                l->type = EXPRESSION_LIST;
                vec_init(l->es);
                avP(l->es, e);
                while (tok()->type == ',') {
                        next();
                        Expr *e = parse_definition_lvalue(ty, LV_SUB);
                        if (e == NULL) {
                                error(ty, "expected lvalue but found %s", token_show(ty, tok()));
                        }
                        avP(l->es, e);
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
        seek(ty, save);
        return NULL;
}

static Expr *
parse_target_list(Ty *ty)
{
        Expr *e = mkexpr(ty);
        e->type = EXPRESSION_LIST;
        vec_init(e->es);
        avP(e->es, parse_definition_lvalue(ty, LV_EACH));

        if (e->es.items[0] == NULL) {
        Error:
                error(ty, "expected lvalue in for-each loop");
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
                avP(e->es, parse_definition_lvalue(ty, LV_EACH));
                if (*vvL(e->es) == NULL) {
                        goto Error;
                }
        }

        return e;
}

static Stmt *
parse_for_loop(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_FOR_LOOP;

        consume_keyword(ty, KEYWORD_FOR);

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
                        parse_expr(ty, 0);
                        cloop = tok()->type == ';';
                }
                LOAD_NI();
                memcpy(&jb, &jb_save, sizeof jb);
                seek(ty, save);
        }

        if (!cloop) {
                s->type = STATEMENT_EACH_LOOP;

                if (match) {
                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_IN;

                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = gensym(ty);
                        tok()->module = NULL;
                }

                s->each.target = parse_target_list(ty);

                consume_keyword(ty, KEYWORD_IN);

                s->each.array = parse_expr(ty, 0);

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_IF) {
                        next();
                        s->each.cond = parse_expr(ty, 0);
                } else {
                        s->each.cond = NULL;
                }

                if (tok()->type == TOKEN_KEYWORD && tok()->keyword == KEYWORD_WHILE) {
                        next();
                        s->each.stop = parse_expr(ty, 0);
                } else {
                        s->each.stop = NULL;
                }

                if (match) {
                        unconsume(TOKEN_EXPRESSION);
                        tok()->e = s->each.target->es.items[0];

                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_MATCH;
                }

                s->each.body = parse_statement(ty, -1);

                return s;
        }

        if (tok()->type == ';') {
                next();
                s->for_loop.init = NULL;
        } else {
                s->for_loop.init = parse_statement(ty, -1);
        }

        if (tok()->type == ';') {
                s->for_loop.cond = NULL;
        } else {
                s->for_loop.cond = parse_expr(ty, 0);
        }

        consume(';');

        if (tok()->type == ')') {
                s->for_loop.next = NULL;
        } else {
                s->for_loop.next = parse_expr(ty, 0);
        }

        s->end = End;

        expect('{');

        s->for_loop.body = parse_statement(ty, -1);

        return s;
}

static struct condpart *
parse_condpart(Ty *ty)
{
        struct condpart *p = amA(sizeof *p);
        p->e = NULL;
        p->target = NULL;
        p->def = false;

        if (have_keyword(KEYWORD_LET)) {
                next();
                p->def = true;
                p->target = parse_definition_lvalue(ty, LV_LET);
                consume(TOKEN_EQ);
                p->e = parse_expr(ty, -1);
                return p;
        }

        SAVE_NE(true);
        Expr *e = parse_expr(ty, 0);
        LOAD_NE();

        if (tok()->type == TOKEN_EQ) {
                next();
                p->target = e;
                p->e = parse_expr(ty, -1);
        } else {
                p->e = e;
        }

        return p;
}

static condpart_vector
parse_condparts(Ty *ty, bool neg)
{
        condpart_vector parts;
        vec_init(parts);

        SAVE_NA(true);

        avP(parts, parse_condpart(ty));

        while ((!neg && have_keyword(KEYWORD_AND)) ||
               (neg && have_keyword(KEYWORD_OR))) {

                next();

                bool not = have_keyword(KEYWORD_NOT);
                if (not) {
                        next();
                }

                struct condpart *part = parse_condpart(ty);

                if (part->target != NULL && neg != not) {
                        error(ty, "illegal condition used as controlling expression of if statement");
                }

                if (not && part->target == NULL) {
                        Expr *not = mkexpr(ty);
                        not->type = EXPRESSION_PREFIX_BANG;
                        not->operand = part->e;
                        part->e = not;
                }

                avP(parts, part);
        }

        LOAD_NA();

        return parts;
}

static Stmt *
parse_while(Ty *ty)
{
        Location start = tok()->start;

        /*
         * Maybe it's a while-match loop.
         */
        if (have_keywords(ty, KEYWORD_WHILE, KEYWORD_MATCH)) {
                next();
                Stmt *m = parse_match_statement(ty);
                m->type = STATEMENT_WHILE_MATCH;
                m->start = start;
                return m;
        }

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_WHILE;

        consume_keyword(ty, KEYWORD_WHILE);

        vec_init(s->While.parts);

        SAVE_NA(true);

        avP(s->While.parts, parse_condpart(ty));

        while (have_keyword(KEYWORD_AND)) {
                next();
                avP(s->While.parts, parse_condpart(ty));
        }

        LOAD_NA();

        s->While.block = parse_block(ty);

        s->end = End;

        return s;
}

static Stmt *
parse_if(Ty *ty)
{

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_IF;

        consume_keyword(ty, KEYWORD_IF);

        s->iff.neg = have_keyword(KEYWORD_NOT);
        if (s->iff.neg) {
                next();
        }

        s->iff.parts = parse_condparts(ty, s->iff.neg);

        s->iff.then = parse_statement(ty, -1);

        if (have_keyword(KEYWORD_ELSE)) {
                next();
                s->iff.otherwise = parse_statement(ty, -1);
        } else {
                s->iff.otherwise = NULL;
        }

        s->end = End;

        return s;
}

static Stmt *
parse_match_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_MATCH;

        consume_keyword(ty, KEYWORD_MATCH);

        s->match.e = parse_expr(ty, -1);

        consume('{');

        vec_init(s->match.patterns);
        vec_init(s->match.statements);

        SAVE_NA(false);

        avP(s->match.patterns, parse_pattern(ty));

        consume(TOKEN_FAT_ARROW);
        avP(s->match.statements, parse_statement(ty, 0));

        while (tok()->type != '}') {
                if (tok()->type == ',') {
                        next();
                }

                if (tok()->type == '}') {
                        break;
                }

                avP(s->match.patterns, parse_pattern(ty));
                consume(TOKEN_FAT_ARROW);
                avP(s->match.statements, parse_statement(ty, 0));
        }

        LOAD_NA();

        consume('}');

        return s;
}

static Stmt *
parse_function_definition(Ty *ty)
{
        Stmt *s = mkstmt(ty);

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
                putback(ty, name);
                putback(ty, kw);
        } else {
                s->type = STATEMENT_FUNCTION_DEFINITION;

        }

        Location target_start = tok()->start;
        Location target_end = tok()->end;

        // FIXME: Hack to skip decorators and find the function name
        for (int i = 0; i < 128; ++i) {
                if (token(i)->type == TOKEN_KEYWORD && token(i)->keyword == KEYWORD_FUNCTION) {
                        target_start = token(i + 1)->start;
                        target_end = token(i + 1)->end;
                        break;
                }
        }

        Expr *f = prefix_function(ty);
        if (f->name == NULL)
                error(ty, "anonymous function definition used in statement context");

        if (s->type == STATEMENT_FUN_MACRO_DEFINITION) {
                avI(f->params, "raw", 0);
                avI(f->dflts, NULL, 0);
                avI(f->constraints, NULL, 0);
                if (f->rest != -1) {
                        f->rest += 1;
                }
                if (f->ikwargs != -1) {
                        f->ikwargs += 1;
                }
        }

        if (contains(OperatorCharset, f->name[0])) {
                s->type = STATEMENT_OPERATOR_DEFINITION;
        }

        Expr *target = mkexpr(ty);
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

static Stmt *
parse_operator_directive(Ty *ty)
{
        setctx(ty, LEX_INFIX);

        if (token(1)->type != TOKEN_USER_OP) {
                consume_keyword(ty, KEYWORD_OPERATOR);
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
                table_put(ty, &uops, uop, INTEGER(p));
        } else if (strcmp(assoc, "right") == 0) {
                table_put(ty, &uops, uop, INTEGER(-p));
        } else {
                error(ty, "expected 'left' or 'right' in operator directive");
        }

        if (tok()->type != TOKEN_NEWLINE) {
                Expr *e = parse_expr(ty, 0);
                table_put(ty, &uopcs, uop, PTR(e));
        }

        consume(TOKEN_NEWLINE);

        return NULL;
}

static Stmt *
parse_return_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);

        consume_keyword(ty, KEYWORD_RETURN);

        if (tok()->start.line != s->start.line || get_prefix_parser(ty) == NULL) {
                return s;
        }

        avP(s->returns, parse_expr(ty, 0));

        while (tok()->type == ',') {
                next();
                avP(s->returns, parse_expr(ty, 0));
        }

        if (tok()->type == ';')
                next();

        return s;
}

static Stmt *
parse_let_definition(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_DEFINITION;
        s->pub = false;

        consume_keyword(ty, KEYWORD_LET);

        s->target = parse_definition_lvalue(ty, LV_LET);
        if (s->target == NULL) {
                error(ty, "failed to parse lvalue in 'let' definition");
        }

        consume(TOKEN_EQ);

        s->value = parse_expr(ty, -1);

        s->end = End;

        if (tok()->type == ';')
                next();

        return s;
}

static Stmt *
parse_defer_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_DEFER;

        consume_keyword(ty, KEYWORD_DEFER);

        s->expression = mkfunc(ty);
        s->expression->body = parse_statement(ty, -1);

        if (tok()->type == ';')
                next();

        return s;
}

inline static Stmt *
try_conditional_from(Ty *ty, Stmt *s)
{
        if (tok()->start.line == End.line && have_keyword(KEYWORD_IF)) {
                next();

                Stmt *if_ = mkstmt(ty);
                if_->type = STATEMENT_IF;
                if_->iff.neg = have_keyword(KEYWORD_NOT);

                if (if_->iff.neg) {
                        next();
                }

                if_->iff.parts = parse_condparts(ty, if_->iff.neg);
                if_->iff.then = s;
                if_->iff.otherwise = NULL;

                s = if_;
        }

        return s;
}

static Stmt *
parse_break_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_BREAK;

        s->depth = 0;

        while (have_keyword(KEYWORD_BREAK)) {
                next();
                s->depth += 1;
        }

        if (tok()->start.line == s->start.line &&
            get_prefix_parser(ty) != NULL &&
            (!have_keyword(KEYWORD_IF) || tok()->type == '(')) {
                s->expression = parse_expr(ty, 0);
        } else {
                s->expression = NULL;
        }

        s = try_conditional_from(ty, s);

        if (tok()->type == ';')
                consume(';');

        return s;
}

static Stmt *
parse_continue_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_CONTINUE;
        s->depth = 0;

        while (have_keyword(KEYWORD_CONTINUE)) {
                next();
                s->depth += 1;
        }

        s = try_conditional_from(ty, s);

        if (tok()->type == ';')
                next();

        return s;
}

static Stmt *
parse_null_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_NULL;

        consume(';');

        return s;
}

inline static bool
should_split(Ty *ty)
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

static Expr *
parse_expr(Ty *ty, int prec)
{
        Expr *e;

        if (++depth > 256)
                error(ty, "exceeded maximum recursion depth of 256");

        prefix_parse_fn *f = get_prefix_parser(ty);
        if (f == NULL) {
                error(
                        ty,
                        "expected expression but found %s%s%s",
                        TERM(34),
                        token_show(ty, tok()),
                        TERM(0)
                );
        }

        e = f(ty);

        while (!should_split(ty) && prec < get_infix_prec(ty)) {
                infix_parse_fn *f = get_infix_parser(ty);
                if (f == NULL) {
                        error(ty, "unexpected token after expression: %s", token_show(ty, tok()));
                }
                if ((token(1)->type == ']' || (have_not_in(ty) && token(2)->type == ']')) && !is_postfix(tok())) {
                        // Special case for operator slices. Very based!
                        goto End;
                }
                e = f(ty, e);
        }

End:
        --depth;

        return e;
}

static Stmt *
parse_block(Ty *ty)
{
        Stmt *block = mkstmt(ty);

        consume('{');

        block->type = STATEMENT_BLOCK;
        vec_init(block->statements);

        while (tok()->type != '}') {
                Stmt *s = parse_statement(ty, -1);
                s->end = End;
                avP(block->statements, s);
        }

        consume('}');

        block->end = End;

        return block;
}

static Stmt *
mktagdef(Ty *ty, char *name)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_TAG_DEFINITION;
        s->tag.pub = false;
        s->tag.name = name;
        vec_init(s->tag.methods);
        vec_init(s->tag.getters);
        vec_init(s->tag.setters);
        vec_init(s->tag.statics);
        vec_init(s->tag.fields);
        return s;
}

static Expr *
parse_method(Ty *ty, Location start, Expr *decorator_macro, char const *doc, expression_vector decorators)
{
        unconsume(TOKEN_KEYWORD);
        tok()->keyword = KEYWORD_FUNCTION;

        Expr *func = prefix_function(ty);
        func->start = start;
        func->end = End;
        func->doc = doc;
        func->decorators = decorators;

        if (decorator_macro == NULL) {
                return func;
        } else {
                avI(decorator_macro->args, func, 0);
                avI(decorator_macro->fconds, NULL, 0);
                return decorator_macro;
        }
}

static Stmt *
parse_class_definition(Ty *ty)
{
        Location start = tok()->start;

        bool tag = tok()->keyword == KEYWORD_TAG;

        consume_keyword(ty, tag ? KEYWORD_TAG : KEYWORD_CLASS);

        expect(TOKEN_IDENTIFIER);

        Stmt *s = mktagdef(ty, tok()->identifier);
        if (!tag)
                s->type = STATEMENT_CLASS_DEFINITION;

        next();

        s->start = start;

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

                s->tag.super = parse_expr(ty, 0);
        } else {
                s->tag.super = NULL;
        }

        /* Hack to allow comma-separated tag declarations */
        if (tag && tok()->type == ',') {
                Stmt *tags = mkstmt(ty);
                tags->type = STATEMENT_MULTI;
                vec_init(tags->statements);
                avP(tags->statements, s);
                while (tok()->type == ',') {
                        next();
                        expect(TOKEN_IDENTIFIER);
                        avP(tags->statements, mktagdef(ty, tok()->identifier));
                        next();
                }
                s = tags;
        }

        if (tag && tok()->type == ';') {
                next();
        } else {
                consume('{');
                setctx(ty, LEX_INFIX);
                while (tok()->type != '}') {
                        parse_sync_lex(ty);

                        char const *doc = NULL;
                        lex_keep_comments(ty, true);
                        if (tok()->type == TOKEN_COMMENT) {
                                doc = tok()->comment;
                                next();
                        }
                        lex_keep_comments(ty, false);

                        /*
                         * Lol.
                         */
                        op_fixup(ty);

                        Expr *decorator_macro = NULL;
                        if (tok()->type == TOKEN_AT && token(1)->type == '{') {
                                next();
                                next();
                                decorator_macro = parse_decorator_macro(ty);
                                consume('}');
                        }
                        expression_vector decorators = {0};
                        if (tok()->type == TOKEN_AT) {
                                decorators = parse_decorators(ty);
                        }
                        if (!have_keyword(KEYWORD_STATIC)) {
                                expect(TOKEN_IDENTIFIER);
                        }
                        struct location start = tok()->start;

                        /*
                         * This is pretty ugly but we use whitespace to differentiate between a setter:
                         *
                         *      onClick= {
                         *              ...
                         *      }
                         *
                         * and a field assignment:
                         *
                         *      onClick = foo
                         */
                        if (
                                tok()->type == TOKEN_IDENTIFIER &&
                                (
                                        (
                                                token(1)->type == TOKEN_EQ &&
                                                (
                                                        token(1)->start.col > tok()->end.col ||
                                                        token(1)->start.line != tok()->end.line
                                                )
                                        ) ||
                                        token(1)->type == ':'
                                )
                        ) {
                                SAVE_NE(true);
                                Expr *field = parse_expr(ty, 0);
                                LOAD_NE();

                                if (tok()->type == TOKEN_EQ) {
                                        field = infix_eq(ty, field);
                                }

                                if (field->type != EXPRESSION_IDENTIFIER && field->type != EXPRESSION_EQ) {
                                        EStart = field->start;
                                        EEnd = field->end;
                                        error(ty, "expected a field definition");
                                }

                                avP(s->tag.fields, field);
                        } else if (have_keyword(KEYWORD_STATIC)) {
                                next();
                                expect(TOKEN_IDENTIFIER);
                                avP(
                                        s->tag.statics,
                                        parse_method(
                                                ty,
                                                start,
                                                decorator_macro,
                                                doc,
                                                decorators
                                        )
                                );
                        } else if (token(1)->type == TOKEN_EQ) {
                                struct token t = *tok();
                                skip(2);
                                putback(ty, t);
                                avP(
                                        s->tag.setters,
                                        parse_method(
                                                ty,
                                                start,
                                                decorator_macro,
                                                doc,
                                                decorators
                                        )
                                );
                        } else if (token(1)->type == '{') {
                                struct token t = *tok();
                                next();
                                unconsume(')');
                                unconsume('(');
                                putback(ty, t);
                                avP(
                                        s->tag.getters,
                                        parse_method(
                                                ty,
                                                start,
                                                decorator_macro,
                                                doc,
                                                decorators
                                        )
                                );
                        } else {
                                avP(
                                        s->tag.methods,
                                        parse_method(
                                                ty,
                                                start,
                                                decorator_macro,
                                                doc,
                                                decorators
                                        )
                                );
                        }
                }
                setctx(ty, LEX_PREFIX);
                consume('}');
        }

        s->end = End;

        return s;
}

static Stmt *
parse_try(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_TRY;

        consume_keyword(ty, KEYWORD_TRY);

        vec_init(s->try.patterns);
        vec_init(s->try.handlers);

        if (tok()->type != '{') {
                s->try.s = mkstmt(ty);
                s->try.s->type = STATEMENT_IF;
                s->try.s->iff.neg = true;
                s->try.s->iff.parts = parse_condparts(ty, false);

                while (have_keyword(KEYWORD_CATCH)) {
                        next();
                        SAVE_NE(true);
                        avP(s->try.patterns, parse_expr(ty, 0));
                        LOAD_NE();
                        avP(s->try.handlers, parse_statement(ty, -1));
                }

                Stmt *otherwise;

                if (have_keywords(ty, KEYWORD_OR, KEYWORD_ELSE)) {
                        skip(2);
                        otherwise = parse_statement(ty, -1);
                } else {
                        otherwise = mkstmt(ty);
                        otherwise->type = STATEMENT_NULL;
                }

                s->try.s->iff.then = otherwise;
                s->try.s->iff.otherwise = NULL;

                avP(s->try.patterns, &WildCard);
                avP(s->try.handlers, otherwise);

                s->try.finally = NULL;

                return s;
        }

        s->try.s = parse_statement(ty, -1);

        while (have_keyword(KEYWORD_CATCH)) {
                next();
                SAVE_NE(true);
                avP(s->try.patterns, parse_expr(ty, 0));
                LOAD_NE();
                avP(s->try.handlers, parse_statement(ty, -1));
        }

        if (have_keyword(KEYWORD_FINALLY)) {
                next();
                s->try.finally = parse_statement(ty, -1);
        } else {
                s->try.finally = NULL;
        }

        s->end = End;

        return s;
}

static Stmt *
parse_import(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_IMPORT;

        s->import.pub = have_keyword(KEYWORD_PUB) && (next(), true);

        consume_keyword(ty, KEYWORD_IMPORT);

        expect(TOKEN_IDENTIFIER);
        char *mod = tok()->module;
        char *id = tok()->identifier;
        next();

        static vec(char) module;
        module.count = 0;

        if (mod != NULL) {
                avPn(module, mod, strlen(mod));
                avP(module, '/');
        }

        avPn(module, id, strlen(id));

        while (tok()->type == '.') {
                next();
                expect(TOKEN_IDENTIFIER);
                avP(module, '/');
                avPn(module, tok()->identifier, strlen(tok()->identifier));
                next();
        }

        avP(module, '\0');

        s->import.module = sclonea(ty, module.items);

        if (have_keyword(KEYWORD_AS)) {
                next();
                expect(TOKEN_IDENTIFIER);
                s->import.as = tok()->identifier;
                next();
        } else {
                s->import.as = s->import.module;
        }

        if (tok()->type == TOKEN_IDENTIFIER && strcmp(tok()->identifier, "hiding") == 0) {
                next();
                s->import.hiding = true;
        } else {
                s->import.hiding = false;
        }

        vec_init(s->import.identifiers);
        vec_init(s->import.aliases);

        if (tok()->type == '(') {
                next();
                if (tok()->type == TOKEN_DOT_DOT) {
                        next();
                        avP(s->import.identifiers, "..");
                        avP(s->import.aliases, "..");
                } else while (tok()->type == TOKEN_IDENTIFIER) {
                        avP(s->import.identifiers, tok()->identifier);
                        next();
                        if (have_keyword(KEYWORD_AS)) {
                                next();
                                expect(TOKEN_IDENTIFIER);
                                avP(s->import.aliases, tok()->identifier);
                                next();
                        } else {
                                avP(s->import.aliases, *vvL(s->import.identifiers));
                        }
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

static Stmt *
parse_statement(Ty *ty, int prec)
{
        Stmt *s;

        setctx(ty, LEX_PREFIX);

        switch (tok()->type) {
        case TOKEN_AT:
                if (token(1)->type == '[')
                        return parse_function_definition(ty);
                else
                        goto Expression;
        case '{':            return parse_block(ty);
        case ';':            return parse_null_statement(ty);
        case TOKEN_KEYWORD:  goto Keyword;
        default:             goto Expression;
        }

Keyword:

        switch (tok()->keyword) {
        case KEYWORD_CLASS:    return parse_class_definition(ty);
        case KEYWORD_TAG:      return parse_class_definition(ty);
        case KEYWORD_FOR:      return parse_for_loop(ty);
        case KEYWORD_WHILE:    return parse_while(ty);
        case KEYWORD_IF:       return parse_if(ty);
        case KEYWORD_FUNCTION: return parse_function_definition(ty);
        case KEYWORD_MACRO:    return parse_function_definition(ty);
        case KEYWORD_OPERATOR: return parse_operator_directive(ty);
        case KEYWORD_MATCH:    return parse_match_statement(ty);
        case KEYWORD_RETURN:   return parse_return_statement(ty);
        case KEYWORD_DEFER:    return parse_defer_statement(ty);
        case KEYWORD_LET:      return parse_let_definition(ty);
        case KEYWORD_BREAK:    return parse_break_statement(ty);
        case KEYWORD_CONTINUE: return parse_continue_statement(ty);
        case KEYWORD_TRY:      return parse_try(ty);
        default:               goto Expression;
        }

Expression:

        s = mkstmt(ty);
        s->type = STATEMENT_EXPRESSION;
        s->expression = parse_expr(ty, prec);
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
parse_error(Ty *ty)
{
        return ERR;
}

static void
define_top(Ty *ty, Stmt *s, char const *doc)
{
        switch (s->type) {
        case STATEMENT_FUN_MACRO_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
                s->doc = doc;
                define_macro(ty, s, s->type == STATEMENT_FUN_MACRO_DEFINITION);
                break;
        case STATEMENT_FUNCTION_DEFINITION:
                s->doc = doc;
                s->value->doc = doc;
                define_function(ty, s);
                break;
        case STATEMENT_CLASS_DEFINITION:
                s->class.doc = doc;
                define_class(ty, s);
                break;
        case STATEMENT_TAG_DEFINITION:
                s->tag.doc = doc;
                define_tag(ty, s);
                break;
        case STATEMENT_MULTI:
                for (int i = 0; i < s->statements.count; ++i) {
                        define_top(ty, s->statements.items[i], doc);
                }
                break;
        case STATEMENT_DEFINITION:
                s->doc = doc;
                break;
        default:
                break;
        }
}

#ifdef TY_DEBUG_NAMES
static void
pns(Namespace const *ns, bool end)
{
        if (ns == NULL)
                return;

        pns(ns->next, false);

        printf("%s[pub=%d, braced=%d]", ns->id, (int)ns->pub, (int)ns->braced);

        putchar(end ? '\n' : '.');
}
#endif

bool
parse_ex(
        Ty *ty,
        char const *source,
        char const *file,
        Stmt ***prog_out,
        Location *err_loc,
        TokenVector *tok_out
)
{
        volatile vec(Stmt *) program;
        vec_init(program);

        depth = 0;
        filename = file;

        TokenIndex = 0;
        vec_init(tokens);

        NoEquals = false;
        NoIn = false;
        NoPipe = false;

        lex_init(ty, file, source);
        lex_keep_comments(ty, true);

        Namespace *saved_namespace = CurrentNamespace;
        CurrentNamespace = NULL;

        lex_save(ty, &CtxCheckpoint);
        setctx(ty, LEX_PREFIX);

        if (setjmp(jb) != 0) {
        Error:
                avP(program, NULL);
                *err_loc = tok()->start;
                *prog_out = program.items;
                if (tok_out != NULL) {
                        *tok_out = tokens;
                }
                CurrentNamespace = saved_namespace;
                return false;
        }

        while (tok()->type == TOKEN_NEWLINE) {
                next();
        }

        while (
                have_keywords(ty, KEYWORD_PUB, KEYWORD_IMPORT)
             || have_keyword(KEYWORD_IMPORT)
             || tok()->type == TOKEN_COMMENT
        ) {
                if (tok()->type == TOKEN_COMMENT) {
                        next();
                } else {
                        avP(program, parse_import(ty));
                        if (vvL(program)[0]->type != STATEMENT_IMPORT) {
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

        lex_save(ty, &CtxCheckpoint);
        lex_start(ty, &CtxCheckpoint);

        for (int i = 0; i < program.count; ++i) {
                if (!compiler_import_module(ty, program.items[i])) {
                        goto Error;
                }
        }

        lex_end(ty);

        memcpy(&jb, &jb_, sizeof jb);
        CtxCheckpoint = CtxCheckpoint_;
        TokenIndex = TokenIndex_;
        tokens = tokens_;
        filename = filename_;
        EStart = EStart_;
        EEnd = EEnd_;

        setctx(ty, LEX_INFIX);
        setctx(ty, LEX_PREFIX);
        program.count = 0;

        while (TokenIndex > 0 && token(-1)->type == TOKEN_COMMENT) {
                TokenIndex -= 1;
        }

        while (tok()->type != TOKEN_END) {
                char const *doc = NULL;

                while (have_keyword(KEYWORD_NAMESPACE) || have_keywords(ty, KEYWORD_PUB, KEYWORD_NAMESPACE)) {
                        bool pub = have_keyword(KEYWORD_PUB) && (next(), true);

                        next();

                        expect(TOKEN_IDENTIFIER);
                        Namespace *ns = PushNS(ty, tok()->identifier, pub);
                        next();

                        while (tok()->type == '.') {
                                next();
                                expect(TOKEN_IDENTIFIER);
                                PushNS(ty, tok()->identifier, true);
                                CurrentNamespace->braced = false;
                                next();
                        }

                        if (tok()->type == TOKEN_NEWLINE) {
                                next();
                                ns->pub |= (ns->next == NULL);
                                ns->braced = false;
                        } else {
                                lex_need_nl(ty, false);
                                consume('{');
                        }
                }

                parse_sync_lex(ty);
                lex_keep_comments(ty, true);

                while (tok()->type == TOKEN_COMMENT) {
                        doc = tok()->comment;
                        next();
                }

                if (tok()->type == TOKEN_END) {
                        break;
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

                lex_keep_comments(ty, false);
                Stmt *s = parse_statement(ty, -1);
                if (s == NULL) {
                        break;
                }


                // TODO: figure out if this is necessary
                while (s->type == STATEMENT_EXPRESSION && s->expression->type == EXPRESSION_STATEMENT) {
                        s = s->expression->statement;
                }

                s->end = End;

                if (s->type != STATEMENT_MACRO_DEFINITION) {
                        avP(program, s);
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
                        error(ty, "This shouldn't happen.");
                }

                s->ns = CurrentNamespace;

                define_top(ty, s, doc);

#ifdef TY_DEBUG_NAMES
                pns(s->ns, true);
#endif

                while (tok()->type == '}' && CurrentNamespace != NULL) {
                        while (CurrentNamespace != NULL && !CurrentNamespace->braced) {
                                PopNS(ty);
                        }
                        if (CurrentNamespace != NULL) {
                                PopNS(ty);
                                next();
                        }
                }
        }

        avP(program, NULL);
        *prog_out = program.items;

        if (tok_out != NULL) {
                *tok_out = tokens;
        }

        CurrentNamespace = saved_namespace;

        return true;
}

Stmt **
parse(Ty *ty, char const *source, char const *file)
{
        Stmt **prog;
        Location loc;

        if (!parse_ex(ty, source, file, &prog, &loc, NULL)) {
                return NULL;
        }

        return prog;
}

Token
parse_get_token(Ty *ty, int i)
{
        bool keep_comments = lex_keep_comments(ty, true);

        if (lex_pos(ty).s > vvL(tokens)->end.s) {
                tokens.count = TokenIndex;
                avP(tokens, ((struct token) {
                        .ctx = lctx,
                        .type = TOKEN_EXPRESSION,
                        .start = lex_pos(ty),
                        .end = lex_pos(ty)
                }));
                next();
        } else {
                tokens.count = TokenIndex;
                lex_rewind(ty, &token(-1)->end);
        }

        struct token *t = token(i);

        lex_keep_comments(ty, keep_comments);

        return *t;
}

void
parse_next(Ty *ty)
{
        next();
}

struct value
parse_get_expr(Ty *ty, int prec, bool resolve, bool want_raw)
{
        int save = TokenIndex;

        jmp_buf jb_save;
        memcpy(&jb_save, &jb, sizeof jb);

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(ty, false);

        Value v;
        Expr *e;

        if (setjmp(jb) != 0) {
                v = NIL;
                seek(ty, save);
        } else {
                e = parse_expr(ty, prec);
                if (!resolve) {
                        v = CToTyExpr(ty, e);
                } else {
                        compiler_symbolize_expression(ty, e, NULL);
                        v = PTR(e);
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyExpr);
                }
        }

        LOAD_NE();
        LOAD_NI();

        memcpy(&jb, &jb_save, sizeof jb);

        lex_keep_comments(ty, keep_comments);

        if (want_raw) {
                Value pair = vT(2);
                pair.items[0] = PTR(e);
                pair.items[1] = v;
                return pair;
        } else {
                return v;
        }
}

struct value
parse_get_stmt(Ty *ty, int prec, bool want_raw)
{
        int save = TokenIndex;

        jmp_buf jb_save;
        memcpy(&jb_save, &jb, sizeof jb);

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(ty, false);

        struct value v;

        if (setjmp(jb) != 0) {
                v = NIL;
                seek(ty, save);
        } else {
                Stmt *s = parse_statement(ty, prec);
                if (want_raw) {
                        v = vT(2);
                        v.items[0] = PTR(s);
                        v.items[1] = tystmt(ty, s);
                } else {
                        v = tystmt(ty, s);
                }
        }

        LOAD_NE();
        LOAD_NI();

        memcpy(&jb, &jb_save, sizeof jb);

        lex_keep_comments(ty, keep_comments);

        return v;
}

noreturn void
parse_fail(Ty *ty, char const *s, size_t n)
{
        error(ty, "%.*s", (int)n, s);
}

/* vim: set sts=8 sw=8 expandtab: */
