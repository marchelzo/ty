#include <stdarg.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <assert.h>
#include <stdnoreturn.h>

#include "alloc.h"
#include "ast.h"
#include "compiler.h"
#include "lex.h"
#include "log.h"
#include "operators.h"
#include "parse.h"
#include "scope.h"
#include "table.h"
#include "token.h"
#include "ty.h"
#include "util.h"
#include "value.h"
#include "vec.h"
#include "vm.h"

#define BINARY_OPERATOR(name, t, prec, right_assoc)                        \
        static Expr *                                                      \
        infix_ ## name(Ty *ty, Expr *left)                                 \
        {                                                                  \
                Expr *e = mkexpr(ty);                                      \
                next();                                                    \
                e->type = EXPRESSION_ ## t;                                \
                e->left = left;                                            \
                e->right = parse_expr(ty, prec - (right_assoc ? 1 : 0));   \
                e->start = left->start;                                    \
                e->end = token(-1)->end;                                   \
                return e;                                                  \
        }                                                                  \

#define BINARY_LVALUE_OPERATOR(name, t, prec, right_assoc)                 \
        static Expr *                                                      \
        infix_ ## name(Ty *ty, Expr *left)                                 \
        {                                                                  \
                Expr *e = mkexpr(ty);                                      \
                consume(TOKEN_ ## t);                                      \
                e->type = EXPRESSION_ ## t;                                \
                e->target = assignment_lvalue(ty, left);                   \
                e->value = parse_expr(ty, prec - (right_assoc ? 1 : 0));   \
                e->start = e->target->start;                               \
                e->end = e->value->end;                                    \
                return e;                                                  \
        }                                                                  \

#define PREFIX_OPERATOR(name, token, prec)                                 \
        static Expr *                                                      \
        prefix_ ## name(Ty *ty)                                            \
        {                                                                  \
                Expr *e = mkexpr(ty);                                      \
                consume(TOKEN_ ## token);                                  \
                e->type = EXPRESSION_PREFIX_ ## token;                     \
                e->operand = parse_expr(ty, prec);                         \
                e->end = e->operand->end;                                  \
                return e;                                                  \
        }                                                                  \

#define PREFIX_LVALUE_OPERATOR(name, token, prec)                          \
        static Expr *                                                      \
        prefix_ ## name(Ty *ty)                                            \
        {                                                                  \
                Expr *e = mkexpr(ty);                                      \
                consume(TOKEN_ ## token);                                  \
                e->type = EXPRESSION_PREFIX_ ## token;                     \
                e->operand = assignment_lvalue(ty, parse_expr(ty, prec));  \
                e->end = TEnd;                                              \
                return e;                                                  \
        }                                                                  \

#define T0 (token(0)->type)
#define T1 (token(1)->type)
#define T2 (token(2)->type)
#define T3 (token(3)->type)

#define K0 ((T0 == TOKEN_KEYWORD) ? token(0)->keyword : -1)
#define K1 ((T1 == TOKEN_KEYWORD) ? token(1)->keyword : -1)
#define K2 ((T2 == TOKEN_KEYWORD) ? token(2)->keyword : -1)
#define K3 ((T3 == TOKEN_KEYWORD) ? token(3)->keyword : -1)
#define KW(i) ((token(i)->type == TOKEN_KEYWORD) ? token(i)->keyword : -1)


#define SAVE_JB                        \
        jmp_buf jb_;                   \
        memcpy(&jb_, &JB, sizeof JB);  \
        SetJmpDepth += 1

#define RESTORE_JB do { memcpy(&JB, &jb_, sizeof JB); SetJmpDepth -= 1; } while (0)


#if 0
#define PLOGX(fmt, ...) (                       \
        EnableLogging                           \
     && fprintf(                                \
                stderr,                         \
                "(%s) %*s" fmt,                 \
                (lxst->need_nl ? "\\n" : "  "), \
                ParseDepth * 8,                 \
                "",                             \
                __VA_ARGS__                     \
        )                                       \
)

#define PLOG(fmt, ...) PLOGX(fmt "\n", __VA_ARGS__)

#define PLOGC(c) (EnableLogging && fputc((c), stderr))

#define next() (                                         \
        PLOG(                                            \
                "%snext()%s :: %s%4d   %s%s%s",          \
                TERM(31;1;4),                            \
                TERM(0),                                 \
                TERM(92),                                \
                __LINE__,                                \
                TERM(96;1),                              \
                __func__,                                \
                TERM(0)                                  \
        ),                                               \
        ((next)(ty))                                     \
)

#define consume(t) do {                                  \
        PLOG(                                            \
                "%sconsume%s(%s%s%s) :: %s%4d   %s%s%s", \
                TERM(33;1;4),                            \
                TERM(0),                                 \
                TERM(34;3),                              \
                #t,                                      \
                TERM(0),                                 \
                TERM(92),                                \
                __LINE__,                                \
                TERM(96;1),                              \
                __func__,                                \
                TERM(0)                                  \
        );                                               \
        (consume)(ty, (t));                              \
} while (0)

#define consume_keyword(t) (                                \
        PLOG(                                               \
                "%sconsume_kw%s(%s%s%s) :: %s%4d   %s%s%s", \
                TERM(35;1;4),                               \
                TERM(0),                                    \
                TERM(34;3),                                 \
                #t,                                         \
                TERM(0),                                    \
                TERM(92),                                   \
                __LINE__,                                   \
                TERM(96;1),                                 \
                __func__,                                   \
                TERM(0)                                     \
        ),                                                  \
        ((consume_keyword)(ty, (t))),                       \
        0                                                   \
)

#define expect(t) (                                      \
        PLOG(                                            \
                "%sexpect%s(%s%s%s) :: %s%4d   %s%s%s",  \
                TERM(35;1;4),                            \
                TERM(0),                                 \
                TERM(34;3),                              \
                #t,                                      \
                TERM(0),                                 \
                TERM(92),                                \
                __LINE__,                                \
                TERM(96;1),                              \
                __func__,                                \
                TERM(0)                                  \
        ),                                               \
        ((expect)(ty, (t)))                              \
)

#define setctx(ctx) (                                    \
        PLOG(                                            \
                "%ssetctx%s(%s%s%s) :: %s%4d   %s%s%s",  \
                TERM(35;1;4),                            \
                TERM(0),                                 \
                TERM(34;3),                              \
                #ctx,                                    \
                TERM(0),                                 \
                TERM(92),                                \
                __LINE__,                                \
                TERM(96;1),                              \
                __func__,                                \
                TERM(0)                                  \
        ),                                               \
        ((setctx)(ty, (ctx))),                           \
        0                                                \
)
#else
#define               next()                  ((next)(ty))
#define           consume(t)          ((consume)(ty, (t)))
#define   consume_keyword(t)  ((consume_keyword)(ty, (t)))
#define            expect(t)           ((expect)(ty, (t)))
#define          setctx(ctx)         ((setctx)(ty, (ctx)))
#define PLOGX(...) ((void)0)
#define  PLOG(...) ((void)0)
#define PLOGC(...) ((void)0)
#endif

#define                 tok()                            ((tok)(ty))
#define              token(i)                     ((token)(ty, (i)))
#define               skip(n)                      ((skip)(ty, (n)))
#define        try_consume(t)               ((try_consume)(ty, (t)))
#define       have_keyword(k)              ((have_keyword)(ty, (k)))
#define have_keywords(k0, k1)      ((have_keywords)(ty, (k0), (k1)))
#define          unconsume(t)                 ((unconsume)(ty, (t)))
#define    expect_one_of(...) ((expect_one_of)(ty, __VA_ARGS__, -1))

#define with_fun_subscope(...)                                          \
        if (1) {                                                        \
                Scope *_saved__scope = ty->pscope;                      \
                ty->pscope = scope_new(ty, "(p)", ty->pscope, true);    \
                __VA_ARGS__                                             \
                ty->pscope = _saved__scope;                             \
        } else if (0)                                                   \

#define with_subscope(...)                                              \
        if (1) {                                                        \
                Scope *_saved__scope = ty->pscope;                      \
                ty->pscope = scope_new(ty, "(p)", ty->pscope, false);   \
                __VA_ARGS__                                             \
                ty->pscope = _saved__scope;                             \
        } else if (0)                                                   \


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

typedef struct ParserState {
        TokenVector tokens;
        int TokenIndex;

        int depth;

        LexState CtxCheckpoint;
        LexContext lctx;

        Namespace *CurrentNamespace;

        Expr *CurrentTemplate;

        jmp_buf jb;
        JmpBufVector SavePoints;
        int SetJmpDepth;

        Location EEnd;
        Location EStart;
        Location TEnd;

        char const *filename;

        bool NoEquals;
        bool NoConstraint;
        bool NoIn;
        bool NoAndOr;
        bool NoPipe;
        bool TypeContext;
        //bool LValueContext;
} ParserState;

Expr *LastParsedExpr;

static ParserState state;

struct table uops;
struct table uopcs;

static Expr BlankID = {
        .type = EXPRESSION_IDENTIFIER,
        .identifier = ""
};

static Expr WildCard = {
        .type = EXPRESSION_IDENTIFIER,
        .identifier = "_"
};

static Stmt NullStatement = {
        .type = STATEMENT_NULL
};

static Expr NullExpr = {
        .type = EXPRESSION_STATEMENT,
        .statement = &NullStatement
};

#define CtxCheckpoint     (state.CtxCheckpoint)
#define CurrentNamespace  (state.CurrentNamespace)
#define CurrentTemplate   (state.CurrentTemplate)
#define TEnd              (state.TEnd)
#define EEnd              (state.EEnd)
#define EStart            (state.EStart)
#define FileName          (state.filename)
#define JB                (state.jb)
#define LCTX              (state.lctx)
#define NoAndOr           (state.NoAndOr)
#define NoConstraint      (state.NoConstraint)
#define NoEquals          (state.NoEquals)
#define NoIn              (state.NoIn)
#define NoPipe            (state.NoPipe)
#define ParseDepth        (state.depth)
#define SavePoints        (state.SavePoints)
#define SetJmpDepth       (state.SetJmpDepth)
#define TokenIndex        (state.TokenIndex)
#define TypeContext       (state.TypeContext)
#define LValueContext     (state.LValueContext)
#define tokens            (state.tokens)
#define uopcs             (uopcs)
#define uops              (uops)

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
#define SAVE_TC(b) bool TCSave = TypeContext; TypeContext = (b);
#define SAVE_LC(b) 0 // bool LCSave = LValueContext; LValueContext = (b);

#define LOAD_NE() NoEquals = NESave;
#define LOAD_NC() NoConstraint = NCSave;
#define LOAD_NI() NoIn = NISave;
#define LOAD_NP() NoPipe = NPSave;
#define LOAD_NA() NoAndOr = NASave;
#define LOAD_TC() TypeContext = TCSave;
#define LOAD_LC() 0 // LValueContext = LCSave;

noreturn void
ParseError(Ty *ty, char const *fmt, ...);

char *
show_expr(Expr const *e);

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
infix_eq(Ty *ty, Expr *left);

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
gensym(void)
{
        static u64 sym = 0;
        return (char *)ifmt("#%u", sym++);
}

inline static Expr *
mkexpr(Ty *ty)
{
        Expr *e = amA0(sizeof *e);
        e->arena = GetArenaAlloc(ty);
        e->mod = CompilerCurrentModule(ty);
        e->start = tok()->start;
        e->end = tok()->end;
        return e;
}

#define mkxpr(t) (mkxpr)(ty, EXPRESSION_##t)
inline static Expr *
(mkxpr)(Ty *ty, int type)
{
        Expr *e = amA0(sizeof *e);
        e->type = type;
        e->arena = GetArenaAlloc(ty);
        e->mod = CompilerCurrentModule(ty);
        e->start = tok()->start;
        e->end = tok()->end;
        return e;
}

#define mkid(id) ((mkid)(ty, (id)))
inline static Expr *
(mkid)(Ty *ty, char *id)
{
        Expr *e = mkxpr(IDENTIFIER);
        e->identifier = id;
        return e;
}

inline static Expr *
mkfunc(Ty *ty)
{
        Expr *f = mkexpr(ty);

        static volatile int t = -1;

        f->type = EXPRESSION_FUNCTION;
        f->rest = -1;
        f->ikwargs = -1;
        f->class = -1;
        f->ftype = FT_NONE;
        f->t = ++t;

        return f;
}

inline static Stmt *
mkstmt(Ty *ty)
{
        Stmt *s = amA0(sizeof *s);
        s->ns = CurrentNamespace;
        s->arena = GetArenaAlloc(ty);
        s->mod = CompilerCurrentModule(ty);
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
        Expr *value = mkxpr(IDENTIFIER);
        value->identifier = name;
        value->module = NULL;

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_DEFINITION;
        s->pub = false;
        s->target = lvalue;
        s->value = value;

        return s;
}

#define to_expr(e) ((to_expr)(ty, (e)))
inline static Expr *
(to_expr)(Ty *ty, Stmt *s)
{
        Expr *e = mkxpr(STATEMENT);
        e->start = s->start;
        e->end = s->end;
        e->statement = s;
        return e;
}

#define to_stmt(e) ((to_stmt)(ty, (e)))
inline static Stmt *
(to_stmt)(Ty *ty, Expr *e)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_EXPRESSION;
        s->start = e->start;
        s->end = e->end;
        s->expression = e;
        return s;
}

inline static Token *
(tokenxx)(Ty *ty, int i)
{
        Token t;

        while (vN(tokens) <= i + TokenIndex) {
                if (vN(tokens) == TokenIndex) {
                        lex_save(ty, &CtxCheckpoint);
                }

                t = lex_token(ty, LCTX);

                //if (vN(tokens) > 0 && vvL(tokens)->start.s == t.start.s) {
                //        *vvL(tokens) = t;
                //        return vvL(tokens);
                //}

                PLOG(
                        "%sAdd tokens%s[%d]: %s",
                        TERM(92;),
                        TERM(0),
                        (int)vN(tokens),
                        token_show(ty, &t)
                );

                avP(tokens, t);
        }

#if 0
        static int64_t last_index = -1;
        static int64_t last_count = -1;

        if (TokenIndex + i != last_index || vN(tokens) != last_count) {
                PLOG(
                        "%s[%d]%stokenxx%s(% -2d)%s = %s",
                        TERM(95),
                        TokenIndex + i,
                        TERM(92),
                        TERM(93),
                        i,
                        TERM(0),
                        token_show(ty, v_(tokens, TokenIndex + i))
                );
                last_index = TokenIndex + i;
                last_count = vN(tokens);
        }
#endif

        return v_(tokens, TokenIndex + i);
}

#define tokenx(i) ((tokenx)(ty, (i)))
inline static Token *
(tokenx)(Ty *ty, int i)
{
        int n    = abs(i);
        int step = (i >= 0) ? 1 : -1;

        if (i >= 0) while (tokenxx(ty, 0)->ctx == LEX_HIDDEN) {
                TokenIndex += 1;
        }

        for (;;) {
                while (
                        (i + TokenIndex >= 0)
                     && (tokenxx(ty, i)->ctx == LEX_HIDDEN)
                ) {
                        i += step;
                }

                if (i + TokenIndex < 0) {
                        step = 1;
                        i += 1;
                        continue;
                }

                if (n == 0) {
                        return tokenxx(ty, i);
                }

                n -= 1;
        }
}

#define nextx() ((skipx)(ty, 1))
#define skipx(n) ((skipx)(ty, (n)))
inline static void
(skipx)(Ty *ty, int n)
{
        TokenIndex += n;
        TEnd = tokenx(-1)->end;
        EStart = tokenx(0)->start;
        EEnd = tokenx(0)->end;
}

inline static void
(skip)(Ty *ty, int n)
{
        Token *t = token(n);

        TokenIndex = t - v_(tokens, 0);

        TEnd = tokenx(-1)->end;
        EStart = tokenx(0)->start;
        EEnd = tokenx(0)->end;
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

static void pp_if(Ty *ty);
static void pp_while(Ty *ty);

inline static Token *
(token)(Ty *ty, int i)
{
        Token *t;

        for (;;) {
                t = tokenx(i);

                if (
                        LIKELY(t->type != TOKEN_DIRECTIVE)
                     || tokenx(i + 1)->type != TOKEN_KEYWORD
                     || t->pp
                ) {
                        goto End;
                }

                int save = TokenIndex;

                switch (tokenx(i + 1)->keyword) {
                case KEYWORD_IF:    skipx(i); pp_if(ty);    break;
                case KEYWORD_WHILE: skipx(i); pp_while(ty); break;
                default:            goto End;
                }

                TokenIndex = save;
        }
End:
        PLOG(
                "%stoken(%s%d=%td%s)%s => (%s)",
                TERM(34;4),
                TERM(93;1),
                i,
                t - v_(tokens, 0),
                TERM(34;4),
                TERM(0),
                token_show(ty, t)
        );

        return t;
}

inline static struct token *
(tok)(Ty *ty)
{
        return token(0);
}

void
parse_sync_lex(Ty *ty)
{
        Token t;

        if (
                (TokenIndex == 0)
             || (TokenIndex >= vN(tokens))
             || (t = *token(-1)).pp
             || v_(tokens, TokenIndex - 1)->pp
        ) {
                return;
        }

        PLOG(
                "%sparse_sync_lex()%s:  %spre%s: [%s] | [%s]",
                TERM(34),
                TERM(0),
                TERM(92;1),
                TERM(0),
                token_show(ty, v_(tokens, TokenIndex - 1)),
                token_showx(ty, v_(tokens, TokenIndex), TERM(93;1))
        );

        vN(tokens) = TokenIndex;
        lex_need_nl(ty, t.nl);
        lex_rewind(ty, &t.end);

        PLOG(
                "%sparse_sync_lex()%s: %spost%s: [%s] | [%s]",
                TERM(34),
                TERM(0),
                TERM(91;1),
                TERM(0),
                token_show(ty, v_(tokens, TokenIndex - 1)),
                token_showx(ty, v_(tokens, TokenIndex), TERM(93;1))
        );
}

inline static void
(setctx)(Ty *ty, int ctx)
{
        if (
                   (LCTX == ctx)
                || ((LCTX = ctx) && 0)
                || (tok()->ctx == LEX_FAKE)
                || tok()->pp
        ) {
                return;
        }

        LCTX = ctx;

        Location seek = (ctx == LEX_FMT) ? token(-1)->end : tok()->start;
        bool nl = tok()->nl;

        PLOGC('\n');

        PLOG(
                "%sRewind:%s %s[%5d]%s: %s%.*s%s~%s",
                TERM(91),
                TERM(0),
                TERM(95),
                TokenIndex,
                TERM(0),
                TERM(97;3;1),
                (seek.s == NULL) ? 0 : (int)strcspn(seek.s, "\n"),
                seek.s,
                TERM(91;1),
                TERM(0)
        );

        lex_rewind(ty, &seek);
        lex_need_nl(ty, nl);

        // TODO: Should we be discarding LEX_FAKE tokens? (i.e. tokens that were unconsume()d)

        while (vN(tokens) > TokenIndex && v_(tokens, TokenIndex)->ctx != LEX_FMT) {
                PLOG("  Pop tokens[%zu]: %s", vN(tokens) - 1, token_show(ty, vvL(tokens)));
                vN(tokens) -= 1;
        }

        while (vN(tokens) > 0 && vvL(tokens)->start.s == seek.s) {
                PLOG("  Pop tokens[%zu]: %s", vN(tokens) - 1, token_show(ty, vvL(tokens)));
                vN(tokens) -= 1;
        }

        PLOGC('\n');

        // TODO: ???
        if (TokenIndex > vN(tokens)) {
                TokenIndex = vN(tokens);
        }

        logctx(ty);
}

static void
logctx(Ty *ty)
{
#if 1
        tok();

        int lo = max(0, TokenIndex - 3);
        int hi = vN(tokens) - 1;

        PLOG(
                "%sContext:%s",
                TERM(94),
                TERM(0)
        );

        for (int i = lo; i <= hi; ++i) {
                char const *c = (i == TokenIndex) ? TERM(92;1) : "";
                PLOG(
                        "    %s(% -2d)%s %s[%s%s]%s",
                        TERM(95),
                        i - TokenIndex,
                        TERM(0),
                        c,
                        token_showx(ty, &tokens.items[i], c),
                        c,
                        TERM(0)
                );
        }

        char const *ahead = lex_pos(ty).s;

        PLOG(
                "    next: %s%.*s%s~%s",
                TERM(97;1;3),
                (int)strcspn(ahead, "\n"),
                ahead,
                TERM(91),
                TERM(0)
        );
#endif
}

inline static jmp_buf *
NewSavePoint(void)
{
        usize n = vN(SavePoints);

        if (n == vC(SavePoints)) {
                do xvP(SavePoints, mrealloc(NULL, sizeof (jmp_buf)));
                while (vN(SavePoints) < vC(SavePoints));
        }

        vN(SavePoints) = n + 1;

        return *vvL(SavePoints);
}

#define CatchError() (AllowErrors && setjmp(*NewSavePoint()) != 0)

/*
 * Push a token into the token stream, so that it will be returned by the next call
 * to tok().
 */
inline static void
(unconsume)(Ty *ty, int type)
{
        struct token t = {
                .type = type,
                .start= TEnd,
                .end = TEnd,
                .ctx = LEX_FAKE
        };

        PLOG("Inserting tokens[%d] = %s", TokenIndex, token_show(ty, &t));

        logctx(ty);

        avI(tokens, t, TokenIndex);
}

#define putback(t) ((putback)(ty, (t)))
inline static void
(putback)(Ty *ty, Token t)
{
        unconsume(TOKEN_ERROR);
        *tok() = t;
        tok()->ctx = LEX_FAKE;
}

noreturn void
ParseError(Ty *ty, char const *fmt, ...)
{
        if (fmt == NULL) {
                goto End;
        }

        if (tokenx(0)->type == TOKEN_ERROR) {
                /*
                 * The lexer already wrote us a nice error message :)
                 */
                goto End;
        }

        ErrorBuffer.count = 0;

        va_list ap;
        va_start(ap, fmt);

        dump(&ErrorBuffer, "%s%sParseError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        vdump(&ErrorBuffer, fmt, ap);

        va_end(ap);

        Location start = EStart;
        Location end = EEnd;

        char buffer[1024];

        snprintf(
                buffer,
                sizeof buffer - 1,
                "%36s %s%s%s:%s%d%s:%s%d%s",
                "at",
                TERM(34),
                CompilerCurrentModule(ty)->name,
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

        dump(
                &ErrorBuffer,
                "\n\n%s near: ",
                where
        );

        if (start.s == NULL) {
                goto End;
        }

        if (tokenx(0)->type == TOKEN_END) {
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

        dump(
                &ErrorBuffer,
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

        dump(
                &ErrorBuffer,
                "\n\t%*s%s%s",
                before + 35,
                "",
                TERM(1),
                TERM(91)
        );

        for (int i = 0; i < length; ++i) {
                dump(&ErrorBuffer, "^");
        }

        dump(
                &ErrorBuffer,
                "%s%s",
                TERM(39),
                TERM(22)
        );

        LOG("Parse Error: %s", TyError(ty));
End:
        if (AllowErrors && SetJmpDepth == 0 && vN(SavePoints) > 0) {
                longjmp(**vvX(SavePoints), 1);
        } else {
                longjmp(JB, 1);
        }
}

#define die(...) ParseError(ty, __VA_ARGS__)
#define die_at(e, ...)                     \
        do {                               \
                EStart = (e)->start;       \
                EEnd   = (e)->end;         \
                die(__VA_ARGS__);          \
        } while (0)

inline static Namespace *
PushNS(Ty *ty, char *id, bool pub)
{
        Namespace *ns = amA(sizeof *ns);
        ns->id = id;
        ns->pub = pub;
        ns->braced = true;
        ns->next = CurrentNamespace;

        (void)GetNamespace(ty, ns);

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
        return T0 == TOKEN_KEYWORD && K0 == kw;
}

inline static bool
(have_keywords)(Ty *ty, int kw1, int kw2)
{
        return T0 == TOKEN_KEYWORD && K0 == kw1 &&
               T1 == TOKEN_KEYWORD && K1 == kw2;
}

inline static bool
have_without_nl(Ty *ty, int t)
{
        return T0 == t && tok()->start.line == TEnd.line;
}

inline static bool
next_without_nl(Ty *ty, int t)
{
        return T1 == t && token(1)->start.line == tok()->end.line;
}

inline static bool
kw_without_nl(Ty *ty, int t)
{
        return have_without_nl(ty, TOKEN_KEYWORD) && K0 == t;
}

static bool
have_not_in(Ty *ty)
{
        return T0 == TOKEN_KEYWORD &&
               K0 == KEYWORD_NOT &&
               T1 == TOKEN_KEYWORD &&
               K1 == KEYWORD_IN;
}

inline static bool
no_rhs(Ty *ty, int i)
{
        return token(i)->type == ']' ||
               token(i)->type == ')' ||
               token(i)->type == '}';
}

static bool
(expect)(Ty *ty, int type)
{
        if (T0 == type) {
                return true;
        }

        if (AllowErrors) {
                switch (type) {
                case ']':
                case ')':
                case '}':
                        return false;
                }
        }

        die(
                "expected %s but found %s%s%s",
                token_show_type(ty, type),
                TERM(34),
                token_show(ty, tok()),
                TERM(0)
        );
}

static bool
(expect_one_of)(Ty *ty, ...)
{
        va_list ap;
        int tt;
        int n = 0;

        va_start(ap, ty);
        while ((tt = va_arg(ap, int)) != -1) {
                if (T0 == tt || K0 == tt) {
                        va_end(ap);
                        return true;
                }
                n += 1;
        }
        va_end(ap);

        byte_vector msg = {0};
        int i = 0;

        adump(&msg, "expected ");

        va_start(ap, ty);
        while ((tt = va_arg(ap, int)) != -1) {
                if (++i == 1) {
                        adump(&msg, "%s", token_show_type(ty, tt));
                } else if (i == n) {
                        adump(
                                &msg,
                                "%sor %s",
                                (i == 2) ? " " : ", ",
                                token_show_type(ty, tt)
                        );
                } else {
                        adump(&msg, ", %s", token_show_type(ty, tt));
                }
        }
        va_end(ap);

        adump(&msg, " but found %s%s%s", TERM(34), token_show(ty, tok()), TERM(0));

        die("%s", v_(msg, 0));
}


static void
expect_keyword(Ty *ty, int type)
{
        if (K0 != type) {
                die(
                        "expected %s but found %s%s%s",
                        token_show(ty, &(struct token){ .type = TOKEN_KEYWORD, .keyword = type }),
                        TERM(34),
                        token_show(ty, tok()),
                        TERM(0)
                );
        }
}

inline static bool
(try_consume)(Ty *ty, int t)
{
        return (T0 == t || K0 == t)
             ? (next(), true)
             : false
             ;
}

inline static void
(consume)(Ty *ty, int type)
{
        if (expect(type)) {
                next();
        }
}

inline static void
(consume_keyword)(Ty *ty, int type)
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
iter_sugar(Ty *ty, Expr **target, Expr **iterable)
{
        Expr *it = mkxpr(IDENTIFIER);
        it->identifier = "it";

        (*iterable) = mkexpr(ty);
        (*iterable)->type = EXPRESSION_LIST;
        avP((*iterable)->es, it);

        SWAP(Expr *, *target, *iterable);
}

inline static bool
op_fixup(Ty *ty, int i)
{
        setctx(LEX_INFIX);

        switch (token(i)->type) {
        default:                return false;
        case TOKEN_DBL_EQ:      token(i)->identifier = "==";   break;
        case TOKEN_MAYBE_EQ:    token(i)->identifier = "?=";   break;
        case TOKEN_CMP:         token(i)->identifier = "<=>";  break;
        case TOKEN_LEQ:         token(i)->identifier = "<=";   break;
        case TOKEN_LT:          token(i)->identifier = "<";    break;
        case TOKEN_GEQ:         token(i)->identifier = ">=";   break;
        case TOKEN_GT:          token(i)->identifier = ">";    break;
        case TOKEN_PLUS:        token(i)->identifier = "+";    break;
        case TOKEN_DIV:         token(i)->identifier = "/";    break;
        case TOKEN_MINUS:       token(i)->identifier = "-";    break;
        case TOKEN_STAR:        token(i)->identifier = "*";    break;
        case TOKEN_PERCENT:     token(i)->identifier = "%";    break;
        case TOKEN_INC:         token(i)->identifier = "++";   break;
        case TOKEN_DEC:         token(i)->identifier = "--";   break;
        case TOKEN_PLUS_EQ:     token(i)->identifier = "+=";   break;
        case TOKEN_STAR_EQ:     token(i)->identifier = "*=";   break;
        case TOKEN_MINUS_EQ:    token(i)->identifier = "-=";   break;
        case TOKEN_DIV_EQ:      token(i)->identifier = "/=";   break;
        case TOKEN_MOD_EQ:      token(i)->identifier = "%=";   break;
        case TOKEN_SHL_EQ:      token(i)->identifier = "<<=";  break;
        case TOKEN_SHR_EQ:      token(i)->identifier = ">>=";  break;
        case TOKEN_SHL:         token(i)->identifier = "<<";   break;
        case TOKEN_SHR:         token(i)->identifier = ">>";   break;
        case TOKEN_XOR_EQ:      token(i)->identifier = "^=";   break;
        case TOKEN_AND_EQ:      token(i)->identifier = "&=";   break;
        case TOKEN_OR_EQ:       token(i)->identifier = "|=";   break;
        case '&':               token(i)->identifier = "&";    break;
        case '|':               token(i)->identifier = "|";    break;
        case '^':               token(i)->identifier = "^";    break;
        case '~':               token(i)->identifier = "~";    break;
        case '?':               token(i)->identifier = "?";    break;
        case '!':               token(i)->identifier = "!";    break;
        case '#':               token(i)->identifier = "#";    break;
        case '.':               token(i)->identifier = ".";    break;
        case TOKEN_USER_OP:                                    break;

        case '[':
                if (token(i + 1)->type == ']') {
                        token(i)->identifier = "[]";
                        token(i + 1)->ctx = LEX_HIDDEN;
                } else if (
                        (token(i + 1)->type == ';')
                     && (token(i + 2)->type == ';')
                     && (token(i + 3)->type == ';')
                ) {
                        token(i)->identifier = "[;;]";
                        token(i + 1)->ctx = LEX_HIDDEN;
                        token(i + 2)->ctx = LEX_HIDDEN;
                        token(i + 3)->ctx = LEX_HIDDEN;
                } else {
                        return false;
                }
                break;

        case TOKEN_KEYWORD:
                switch (token(i)->keyword) {
                case KEYWORD_IN:
                        token(i)->identifier = "in";
                        break;

                default:
                        return false;
                }
                break;
        }

        token(i)->module = NULL;
        token(i)->type = TOKEN_IDENTIFIER;

        return true;
}

inline static char *
clone_slice_a(Ty *ty, char const *p, char const *q)
{
        ptrdiff_t n = q - p;
        char *s = amA(n + 1);

        memcpy(s, p, n);
        s[n] = '\0';

        return s;
}

Expr *
parse_decorator_macro(Ty *ty)
{
        setctx(LEX_PREFIX);

        if (T1 == '}') {
                Token id = *tok();

                next();
                unconsume(')');
                unconsume('(');

                putback(id);
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
                die("expected function-like macro invocation inside @{...}");
        }

        return m;
}


static expression_vector
parse_decorators(Ty *ty)
{
        expression_vector decorators = {0};

        do {
                consume('@');
                consume('[');

                for (int i = 0 ; T0 != ']'; ++i) {
                        Expr *f = parse_expr(ty, 0);

                        if (
                                (f->type != EXPRESSION_FUNCTION_CALL)
                             && (f->type != EXPRESSION_METHOD_CALL)
                        ) {
                                Expr *call = mkexpr(ty);
                                call->start = f->start;
                                call->end = f->end;
                                if (f->type == EXPRESSION_MEMBER_ACCESS) {
                                        call->type = EXPRESSION_METHOD_CALL;
                                        call->object = f->object;
                                        call->method = f->member;
                                } else {
                                        call->type = EXPRESSION_FUNCTION_CALL;
                                        call->function = f;
                                }
                                f = call;
                        }

                        Expr *hole = mkxpr(PLACEHOLDER);

                        switch (f->type) {
                        case EXPRESSION_FUNCTION_CALL:
                                avI(f->args, hole, 0);
                                avI(f->fconds, NULL, 0);
                                break;

                        case EXPRESSION_METHOD_CALL:
                                avI(f->method_args, hole, 0);
                                avI(f->mconds, NULL, 0);
                                break;

                        default:
                                UNREACHABLE();
                        }

                        vvI(decorators, f, i);

                        if (T0 == ',') {
                                next();
                        }
                }

                consume(']');

        } while (T0 == '@' && T1 == '[');

        return decorators;
}

static Expr *
parse_type(Ty *ty, int prec)
{
        Expr *t;

        SAVE_TC(true);
        t = parse_expr(ty, prec);
        LOAD_TC();

        return t;
}


static void
parse_type_params(Ty *ty, expression_vector *params)
{
        SAVE_NE(true);
        consume('[');
        while (T0 != ']') {
                bool variadic = try_consume('*')
                             || try_consume(TOKEN_DOT_DOT_DOT);

                Expr *param = prefix_identifier(ty);

                if (variadic) {
                        param->type = EXPRESSION_MATCH_REST;
                }

                avP(*params, param);

                if (T0 != ']') {
                        consume(',');
                }
        }
        next();
        LOAD_NE();
}

/* * * * | prefix parsers | * * * */
static Expr *
prefix_integer(Ty *ty)
{
        expect(TOKEN_INTEGER);

        Expr *e = mkxpr(INTEGER);
        e->integer = tok()->integer;

        consume(TOKEN_INTEGER);

        return e;
}

static Expr *
prefix_real(Ty *ty)
{
        expect(TOKEN_REAL);

        Expr *e = mkxpr(REAL);
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
        avPv(s1->expressions, s2->expressions);
        avPv(s1->fmts, s2->fmts);
        avPv(s1->fmtfs, s2->fmtfs);
        avPv(s1->widths, s2->widths);
        avPn(s1->strings, s2->strings.items + 1, s2->strings.count - 1);
}

Expr *
extend_string(Ty *ty, Expr *s)
{
        while (
                (T0 == TOKEN_STRING)
             || (T0 == '"')
             || (
                        (T0 == TOKEN_IDENTIFIER)
                     && is_macro(ty, tok()->module, tok()->identifier)
                )
        ) {
                Expr *s2 = parse_expr(ty, 999);

                if (
                        (s2->type != EXPRESSION_STRING)
                     && (s2->type != EXPRESSION_SPECIAL_STRING)
                ) {
                        EStart = s2->start;
                        EEnd = s2->end;
                        die("string-adjacent macro expanded to non-string: %s", ExpressionTypeName(s2));
                }

                merge_strings(ty, s, s2);
        }

        return s;
}

static Expr *
prefix_string(Ty *ty)
{
        expect(TOKEN_STRING);

        Expr *e = mkxpr(STRING);
        e->string = tok()->string;

        consume(TOKEN_STRING);

        return extend_string(ty, e);
}

static char *
ss_next_str(Ty *ty, bool top)
{
        char *str;

        setctx(top ? LEX_FMT : LEX_XFMT);

        if (T0 != TOKEN_STRING) {
                // TODO: this shouldn't be necessary. we threw away a SS string
                // and were unable to rewind back through preprocessor-generated
                // tokens in order to produce it again
                return "";
        }

        str = tok()->string;

        next();

        return str;
}

static void
ss_skip_inner(Ty *ty, bool top)
{
        ss_next_str(ty, top);

        while (setctx(LEX_PREFIX), T0 == '{') {
                next();

                parse_expr(ty, 0);

                if (T0 == ':') {
                        next();
                        ss_skip_inner(ty, false);
                }

                if (T0 == '[') {
                        next();
                        parse_expr(ty, 0);
                        consume(']');
                }

                consume('}');

                ss_next_str(ty, top);
        }
}

static Expr *
ss_inner(Ty *ty, bool top)
{
        Expr *e = mkxpr(SPECIAL_STRING);

        avP(e->strings, ss_next_str(ty, top));

        while (setctx(LEX_PREFIX), T0 == '{') {
                Location start = tok()->start;

                next();

                SAVE_NE(false);
                SAVE_NC(true);
                avP(e->expressions, parse_expr(ty, 0));
                LOAD_NC();
                LOAD_NE();

                if (T0 == ':') {
                        next();

                        Expr *fmt = ss_inner(ty, false);
                        char *last = *vvL(fmt->strings);

                        /*
                         * Strip trailing spaces from the format specifier so
                         * {x:-.2f   } becomes just '-.2f' -- trailing spaces
                         * are used purely to control the width which gets passed
                         * to __fmt__
                         */
                        for (int i = (int)strlen(last) - 1; i >= 0 && isspace(last[i]); --i) {
                                last[i] = '\0';
                        }

                        bool empty = vN(fmt->strings) == 1
                               && **vvL(fmt->strings) == 0;

                        avP(e->fmts, !empty ? fmt : NULL);
                } else {
                        avP(e->fmts, NULL);
                }

                if (T0 == '[') {
                        next();
                        SAVE_NE(false);
                        avP(e->fmtfs, parse_expr(ty, 0));
                        LOAD_NE();
                        consume(']');
                } else {
                        avP(e->fmtfs, NULL);
                }

                Location end = tok()->end;
                avP(e->widths, end.s - start.s);

                consume('}');

                avP(e->strings, ss_next_str(ty, top));
        }

        e->end = TEnd;

        return e;
}

static void
skip_ss(Ty *ty)
{
        consume('"');
        ss_skip_inner(ty, true);
        consume('"');
}

static Expr *
prefix_ss(Ty *ty)
{
        Expr *e;
        Location start = tok()->start;

        consume('"');
        e = ss_inner(ty, true);
        consume('"');

        e->start = start;
        e->end = TEnd;

        return extend_string(ty, e);
}

static Expr *
prefix_hash(Ty *ty)
{
        Expr *e = mkexpr(ty);

        consume('#');

        e->type = EXPRESSION_PREFIX_HASH;
        e->operand = parse_expr(ty, 10);
        e->end = TEnd;

        return e;
}

static Expr *
prefix_slash(Ty *ty)
{
        Location start = tok()->start;

        next();

        Expr *body = parse_expr(ty, 1);

        Expr *nil = mkxpr(NIL);
        nil->start = start;

        Expr *f = mkcall(ty, nil);
        avP(f->args, body);
        avP(f->fconds, NULL);

        nil->end = f->end = TEnd;

        return mkpartial(ty, f);
}

static Expr *
prefix_dollar(Ty *ty)
{
        if (T1 == '{') {
                return prefix_implicit_lambda(ty);
        }

        Expr *e = mkexpr(ty);

        consume('$');
        setctx(LEX_INFIX);

        expect(TOKEN_IDENTIFIER);

        e->type = EXPRESSION_MATCH_NOT_NIL;
        e->identifier = tok()->identifier;
        e->module = tok()->module;

        if (e->module != NULL)
                die("unpexpected module in lvalue");

        consume(TOKEN_IDENTIFIER);

        e->end = TEnd;

        return e;
}

inline static bool
is_operator(char const *id)
{
        if (strcmp(id, "#") == 0) {
                return true;
        }

        for (int i = 0; id[i] != '\0'; ++i) {
                if (!contains(OperatorCharset, id[i])) {
                        return false;
                }
        }

        return true;
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

        if (is_macro(ty, e->module, e->identifier)) {
                return typarse(ty, e, NULL, &e->start, &token(-1)->end);
        }

        if (TypeContext && strcmp(e->identifier, "_") == 0) {
                e->type = EXPRESSION_MATCH_ANY;
                e->end = TEnd;
                return e;
        }

        if (!TypeContext && e->module == NULL && is_operator(e->identifier)) {
                e->type = EXPRESSION_OPERATOR;
                e->op.id = e->identifier;
                e->end = TEnd;
                return e;
        }

        // TODO: maybe get rid of this
        if (!NoConstraint && T0 == ':') {
                next();
                e->constraint = parse_type(ty, 0);
        } else {
                e->constraint = NULL;
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_eval(Ty *ty)
{
        Expr *e = mkxpr(EVAL);
        next();
        consume('(');
        e->operand = parse_expr(ty, 0);
        consume(')');
        e->end = TEnd;
        return e;
}

static Expr *
prefix_defined(Ty *ty)
{
        Expr *e;
        struct location start = tok()->start;

        next();
        consume('(');

        if (T0 != TOKEN_IDENTIFIER || T1 != ')') {
                // Force a parse error
                consume(TOKEN_IDENTIFIER);
                consume(')');
        }

        e = parse_expr(ty, 0);
        e->type = EXPRESSION_DEFINED;

        consume(')');

        e->start = start;
        e->end = TEnd;

        return e;
}

static Expr *
parse_expr_template(Ty *ty)
{
        Expr *template = mkxpr(TEMPLATE);
        Expr *save = CurrentTemplate;
        CurrentTemplate = template;
        avP(template->template.stmts, to_stmt(parse_expr(ty, 0)));
        template->end = TEnd;
        CurrentTemplate = save;
        return template;
}

static Expr *
prefix_function(Ty *ty)
{
        Expr *e = mkfunc(ty);

        bool sugared_generator = false;

        if (T0 == TOKEN_AT) {
                e->decorators = parse_decorators(ty);
        }

        int type = K0;

        if (type == KEYWORD_GENERATOR) {
                e->type = EXPRESSION_GENERATOR;
        } else {
                e->type = EXPRESSION_FUNCTION;
        }

        next();

        if (e->type == EXPRESSION_GENERATOR) {
                goto Body;
        }

        if (T0 == TOKEN_IDENTIFIER) {
                e->name = tok()->identifier;
                next();
        }

        if (T0 == TOKEN_STAR) {
                sugared_generator = true;
                next();
        }

        if (e->name != NULL && tok()->start.s[-1] == ' ') {
                Expr *f = parse_expr(ty, 0);
                f->name = e->name;
                return f;
        }

        char const *proto_start = tok()->start.s;

        SAVE_NE(true);

        if (T0 == '[') {
                parse_type_params(ty, &e->type_params);
        }

        if (CatchError()) {
                goto EndOfParams;
        }

        consume('(');

        while (T0 != ')') {
                setctx(LEX_PREFIX);

                bool special = false;

                if (T0 == TOKEN_STAR) {
                        next();
                        e->rest = e->params.count;
                        special = true;
                } else if (T0 == TOKEN_PERCENT) {
                        next();
                        e->ikwargs = e->params.count;
                        special = true;
                }

                expect(TOKEN_IDENTIFIER);
                avP(e->params, tok()->identifier);
                next();

                if (T0 == ':') {
                        next();
                        avP(e->constraints, parse_type(ty, 0));
                        (*vvL(e->constraints))->end = TEnd;
                } else {
                        avP(e->constraints, NULL);
                }

                if (!special && T0 == TOKEN_EQ) {
                        next();
                        avP(e->dflts, parse_expr(ty, 0));
                        (*vvL(e->dflts))->end = TEnd;
                } else {
                        avP(e->dflts, NULL);
                }

                if (T0 == ',') {
                        next();
                }
        }

        LOAD_NE();

        consume(')');

        vvX(SavePoints);

EndOfParams:
        e->end = TEnd;

        if (T0 == TOKEN_ARROW) {
                next();
                e->return_type = parse_type(ty, -1);
        }

        e->proto = clone_slice_a(ty, proto_start, TEnd.s);

        if (sugared_generator) {
                unconsume(TOKEN_KEYWORD);
                tok()->keyword = KEYWORD_GENERATOR;
        }

        if (try_consume(KEYWORD_WHERE)) {
                for (;;) {
                        Expr *sub;
                        Expr *super;

                        SAVE_NC(true);
                        if (T0 == '(') {
                                next();
                                sub = parse_type(ty, 0);
                                next();
                        } else {
                                sub = prefix_identifier(ty);
                        }
                        LOAD_NC();
                        consume(':');
                        super = parse_type(ty, 0);

                        TypeBound bound = { .var = sub, .bound = super };

                        avP(e->type_bounds,  bound);

                        if (K0 != KEYWORD_AND && T0 != ',') {
                                break;
                        }

                        next();

                }
        }

Body:
        if (T0 == ';') {
                next();
                e->body = NULL;
        } else if (T0 == TOKEN_EQ && type == KEYWORD_MACRO) {
                next();
                e->body = to_stmt(parse_expr_template(ty));
        } else {
                if (CatchError()) {
                        e->body = NULL;
                } else {
                        e->body = parse_statement(ty, -1);
                        vvX(SavePoints);
                }
        }

        if (sugared_generator) {
                e->body->expression->name = afmt("<%s:generator>", e->name);
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

        char *a = gensym();
        char *b = gensym();

        unconsume(')');

        unconsume(TOKEN_IDENTIFIER);
        tok()->module = NULL;
        tok()->identifier = b;

        putback(t);

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
        if (T1 == '[')
                return prefix_function(ty);

        Location start = tok()->start;
        Location end = tok()->end;

        next();

        if (T0 == '{') {
                next();

                Expr *m = parse_decorator_macro(ty);

                consume('}');

                Expr *stmt = mkxpr(STATEMENT);
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

        consume(TOKEN_STAR);

        if (
                TypeContext
             || (NoEquals && T0 != ')')
        ) {
                e->type = EXPRESSION_SPREAD;
                e->value = parse_expr(ty, 0);
        } else {
                e->type = EXPRESSION_MATCH_REST;
                e->module = NULL;


                if (T0 == TOKEN_IDENTIFIER) {
                        e->identifier = tok()->identifier;

                        if (tok()->module != NULL)
                                die("unexpected module qualifier in lvalue");

                        next();
                } else {
                        e->identifier = "_";
                }
        }

        e->end = TEnd;

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

        while (T0 != '}') {
                setctx(LEX_PREFIX);

                if (T0 == TOKEN_QUESTION) {
                        next();
                        avP(e->required, false);
                } else {
                        avP(e->required, true);
                }

                if (T0 == TOKEN_STAR) {
                        Expr *item = mkexpr(ty);
                        next();
                        if (T0 == '}') {
                                item->type = EXPRESSION_MATCH_REST;
                                item->identifier = "_";
                                item->module = NULL;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                                item->value = parse_expr(ty, 0);
                                item->end = TEnd;
                        }
                        avP(e->names, "*");
                        avP(e->es, item);
                        goto Next;
                }

                SAVE_NC(true);
                SAVE_NE(true);
                Expr *name = parse_expr(ty, 999);
                LOAD_NE();
                LOAD_NC();

                if (T0 == ',' || T0 == '}' || K0 == KEYWORD_IF) {
                        switch (name->type) {
                        case EXPRESSION_IDENTIFIER:
                        case EXPRESSION_MATCH_NOT_NIL:
                        case EXPRESSION_RESOURCE_BINDING:
                                avP(e->names, name->identifier);
                                avP(e->es, name);
                                break;
                        default:
                                 expect_one_of(',', '}', KEYWORD_IF);
                                 UNREACHABLE();
                        }
                } else if (name->type != EXPRESSION_IDENTIFIER) {
                        die_at(name, "unexpected expression used as field name in record literal");
                } else {
                        expect_one_of(':', '=');
                        next();
                        avP(e->names, name->identifier);
                        avP(e->es, parse_expr(ty, 0));
                }

Next:
                if (have_keyword(KEYWORD_IF)) {
                        next();
                        avP(e->tconds, parse_expr(ty, 0));
                } else {
                        avP(e->tconds, NULL);
                }

                if (T0 == ',') {
                        next();
                }
        }

        consume('}');

        e->end = TEnd;

        return e;
}

static Expr *
patternize(Ty *ty, Expr *e);

static Expr *
next_pattern(Ty *ty)
{
        SAVE_NE(true);
        SAVE_NC(false);

        Expr *p = parse_expr(ty, 0);
        p->end = TEnd;

        if (false && p->type == EXPRESSION_IDENTIFIER && T0 == ':') {
                next();
                p->constraint = parse_expr(ty, 0);
                p->constraint->end = TEnd;
        }

        LOAD_NC();
        LOAD_NE();

        return patternize(ty, p);
}

static Expr *
parse_pattern(Ty *ty)
{
        Expr *pattern = next_pattern(ty);

        if (T0 == ',') {
                Expr *p = mkexpr(ty);

                p->type = EXPRESSION_CHOICE_PATTERN;
                p->start = pattern->start;

                vec_init(p->es);
                avP(p->es, pattern);

                while (T0 == ',') {
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
prefix_super(Ty *ty)
{
        Expr *super = mkxpr(SUPER);

        next();

        return super;
}

static Expr *
prefix_do(Ty *ty)
{
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

            if (T0 == TOKEN_EQ) {
                    next();
                    def->target = definition_lvalue(ty, e);
                    def->value = parse_expr(ty, 0);
            } else {
                    Expr *t = mkxpr(IDENTIFIER);
                    t->identifier = gensym();
                    t->module = NULL;
                    def->target = t;
                    def->value = e;
            }

            avP(defs, def);

            if (T0 == ',') {
                    next();
            } else {
                break;
            }
        }

        make_with(ty, with, defs, parse_statement(ty, 0));

        with->end = TEnd;

        return with;
}

static Expr *
prefix_throw(Ty *ty)
{
        Expr *e = mkxpr(THROW);

        consume_keyword(KEYWORD_THROW);

        e->throw = parse_expr(ty, 0);

        if (T0 == ';')
                next();

        e->end = TEnd;

        return e;
}

static Expr *
prefix_typeof(Ty *ty)
{
        Expr *e = mkxpr(TYPE_OF);

        consume_keyword(KEYWORD_TYPEOF);

        SAVE_TC(false);
        e->operand = parse_expr(ty, 0);
        LOAD_TC();

        e->end = TEnd;

        return e;
}

static Expr *
prefix_yield(Ty *ty)
{
        Expr *e = mkxpr(YIELD);
        vec_init(e->es);

        consume_keyword(KEYWORD_YIELD);

        avP(e->es, parse_expr(ty, 1));
        while (T0 == ',') {
                next();
                avP(e->es, parse_expr(ty, 1));
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_match(Ty *ty)
{
        char *id = NULL;

        if (T1 == '{') {
                Token kw = *tok();
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = id = gensym();
                putback(kw);
        }

        Expr *e = mkxpr(MATCH);

        consume_keyword(KEYWORD_MATCH);

        e->subject = parse_expr(ty, -1);
        e->end = e->subject->end = TEnd;

        SAVE_NA(false);

        if (T0 == TOKEN_FAT_ARROW) {
                next();
                avP(e->patterns, patternize(ty, e->subject));
                e->subject = mkexpr(ty);
                e->subject->type = EXPRESSION_IDENTIFIER;
                e->subject->identifier = id = gensym();
                avP(e->thens, parse_expr(ty, 0));
                if (have_keyword(KEYWORD_ELSE)) {
                        next();
                        Expr *alt = parse_expr(ty, 0);
                        Expr *any = mkid("it");
                        avP(e->patterns, any);
                        avP(e->thens, alt);
                }
                goto End;
        }

        if (CatchError()) {
                goto End;
        }

        consume('{');

        avP(e->patterns, parse_pattern(ty));

        consume(TOKEN_FAT_ARROW);
        avP(e->thens, parse_expr(ty, 0));

        while (T0 != '}') {
                if (T0 == ',') {
                        next();
                }

                // Trailing comma is allowed
                if (T0 == '}') {
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

        Expr *iter;
        Expr *target = parse_target_list(ty);

        if (target->type != EXPRESSION_LIST) {
                iter_sugar(ty, &target, &iter);
        } else {
                consume_keyword(KEYWORD_IN);
                iter = parse_expr(ty, 0);
        }

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
        avP(g->body->each.body->expression->es, e);

        g->end = TEnd;

        return g;
}

static bool
try_parse_flag(Ty *ty, expression_vector *kwargs, StringVector *kws, expression_vector *kwconds)
{
        if (T0 != ':' && (T0 != TOKEN_BANG || !next_without_nl(ty, ':'))) {
                return false;
        }

        bool flag = (T0 == ':') || (next(), false);
        next();

        expect(TOKEN_IDENTIFIER);

        Expr *arg = mkxpr(BOOLEAN);
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

        if (T0 == TOKEN_STAR) {
                Expr *arg = mkexpr(ty);

                next();

                if (T0 == TOKEN_STAR) {
                        next();
                        arg->type = EXPRESSION_SPLAT;
                } else {
                        arg->type = EXPRESSION_SPREAD;
                }

                if (
                        T0 == ',' ||
                        T0 == ')' ||
                        have_keyword(KEYWORD_IF)
                ) {
                        arg->value = mkexpr(ty);
                        arg->value->type = EXPRESSION_IDENTIFIER;
                        arg->value->module = NULL;
                        arg->value->identifier = &"**"[arg->type == EXPRESSION_SPREAD];
                        arg->end = TEnd;
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
                 T0 == TOKEN_IDENTIFIER &&
                 (
                         T1 == ':' ||
                         T1 == TOKEN_EQ
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
        consume('(');

        setctx(LEX_PREFIX);

        Location start = tok()->start;

        if (CatchError()) {
                goto End;
        }

        if (T0 == ')') {
                goto Close;
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
                        die("malformed generator comprehension argument");
                }
        }

        while (T0 == ',') {
                next();
                setctx(LEX_PREFIX);
                next_arg(
                        ty,
                        &e->method_args,
                        &e->mconds,
                        &e->method_kwargs,
                        &e->method_kws,
                        NULL
                );
        }

Close:
        consume(')');
        vvX(SavePoints);

End:
        e->end = TEnd;
}

static Expr *
parse_method_call(Ty *ty, Expr *e)
{
        switch (T0) {
        case '(':
                parse_method_args(ty, e);
                e->end = TEnd;
                return e;
        case TOKEN_AT:
                next();
                parse_method_args(ty, e);
                e->end = TEnd;
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

        Expr *nil = mkxpr(NIL);

        Expr *f = mkcall(ty, nil);
        avP(f->args, body);
        avP(f->fconds, NULL);

        avP(e->method_args, mkpartial(ty, f));
        avP(e->mconds, NULL);

        e->end = TEnd;

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
        if (T0 == ')') {
                next();
                e = mkxpr(TUPLE);
                e->start = start;
                e->only_identifiers = true;
                return e;
        }

        /*
         * If we have an infix operator that cannot also be a prefix
         * operator, assume this is an operator section.
         */
        if (get_infix_parser(ty) != NULL && get_prefix_parser(ty) == NULL) {
                e = mkfunc(ty);
                avP(e->params, gensym());
                avP(e->dflts, NULL);
                avP(e->constraints, NULL);

                Expr *t = mkxpr(IDENTIFIER);
                t->identifier = e->params.items[0];
                t->module = NULL;

                e->body = mkstmt(ty);
                e->body->type = STATEMENT_EXPRESSION;
                e->body->expression = get_infix_parser(ty)(ty, t);

                consume(')');

                return e;
        }

        // (:a, ...)
        if (T0 == ':' && T1 == TOKEN_IDENTIFIER) {
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = token(2)->identifier;
                tok()->module = NULL;
        }

        SAVE_NE(true);
        SAVE_NA(false);
        SAVE_NC(false);
        if (CatchError()) {
                e = &NullExpr;
        } else {
                if (TypeContext && T0 == TOKEN_STAR) {
                        e = mkexpr(ty);
                        next();
                        e->type = EXPRESSION_SPREAD;
                        e->value = parse_expr(ty, 0);
                        e->end = TEnd;
                } else {
                        e = parse_expr(ty, 0);
                }
                vvX(SavePoints);
        }
        LOAD_NC();
        LOAD_NA();
        LOAD_NE();

        if (T0 == TOKEN_EQ || T0 == TOKEN_MAYBE_EQ) {
                SAVE_NA(true);
                e = infix_eq(ty, e);
                LOAD_NA();
        }

        if (
                (e->type == EXPRESSION_SPREAD)
             || (T0 == ',')
             || (T0 == ':')
             || (K0 == KEYWORD_IF)
        ) {
                Expr *list = mkxpr(TUPLE);
                list->start = start;
                list->only_identifiers = true;

                if (
                        (e->type != EXPRESSION_IDENTIFIER)
                     && (e->type != EXPRESSION_MATCH_REST)
                ) {
                        list->only_identifiers = false;
                }

                e->end = TEnd;
                avP(list->es, e);
                avP(list->names, NULL);
                avP(list->required, true);

                if (have_keyword(KEYWORD_IF)) {
                        next();
                        avP(list->tconds, parse_expr(ty, 0));
                } else {
                        avP(list->tconds, NULL);
                }

                if (T0 == ',') {
                        next();
                }

                while (T0 != ')') {
                        if (T0 == TOKEN_QUESTION) {
                                next();
                                avP(list->required, false);
                        } else {
                                avP(list->required, true);
                        }

                        SAVE_NE(true);
                        SAVE_NA(false);
                        SAVE_NC(false);
                        e = parse_expr(ty, 0);
                        LOAD_NC();
                        LOAD_NA();
                        LOAD_NE();

                        if (T0 == TOKEN_EQ || T0 == TOKEN_MAYBE_EQ) {
                                SAVE_NA(true);
                                e = infix_eq(ty, e);
                                LOAD_NA();
                        }


                        avP(list->es, e);
                        avP(
                                list->names,
                                (e->type == EXPRESSION_SPREAD) ? "*" : NULL
                        );

                        if (have_keyword(KEYWORD_IF)) {
                                next();
                                avP(list->tconds, parse_expr(ty, 0));
                        } else {
                                avP(list->tconds, NULL);
                        }

                        if (T0 != ')') {
                                consume(',');
                        }
                }

                consume(')');

                list->end = TEnd;

                if (T0 == TOKEN_ARROW) {
                        list->type = EXPRESSION_LIST;
                }

                return list;
        } else if (have_keyword(KEYWORD_FOR)) {
                e = gencompr(ty, e);

                consume(')');

                e->start = start;
                e->end = TEnd;

                return e;
        } else {
                consume(')');

                if (e->type == EXPRESSION_TUPLE && !has_names(e)) {
                        Expr *list = mkxpr(TUPLE);
                        list->start = start;
                        list->only_identifiers = false;
                        avP(list->names, NULL);
                        avP(list->required, true);
                        avP(list->es, e);
                        avP(list->tconds, NULL);
                        return list;
                } else {
                        e->start = start;
                        e->end = TEnd;
                        return e;
                }
        }
}

static Expr *
prefix_true(Ty *ty)
{
        Expr *e = mkxpr(BOOLEAN);
        e->boolean = true;

        consume_keyword(KEYWORD_TRUE);

        return e;
}

static Expr *
prefix_false(Ty *ty)
{
        Expr *e = mkxpr(BOOLEAN);
        e->boolean = false;

        consume_keyword(KEYWORD_FALSE);

        return e;
}

static Expr *
prefix_self(Ty *ty)
{

        Expr *e = mkxpr(SELF);

        consume_keyword(KEYWORD_SELF);

        return e;
}

static Expr *
prefix_nil(Ty *ty)
{

        Expr *e = mkxpr(NIL);

        consume_keyword(KEYWORD_NIL);

        return e;
}

static Expr *
prefix_regex(Ty *ty)
{
        Expr *e = mkxpr(REGEX);
        e->regex = tok()->regex;

        consume(TOKEN_REGEX);

        return e;
}


static Expr *
prefix_array(Ty *ty)
{
        setctx(LEX_INFIX);

        if (T2 == ']') switch (T1) {
        case TOKEN_USER_OP:
        case TOKEN_PERCENT:
        case TOKEN_PLUS:
        case TOKEN_MINUS:
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

        Location start = tok()->start;

        consume('[');

        /*
         * function sum [match] {
         *      [x, *xs] => x + sum(*xs),
         *      []       => 0,
         * }
         *
         * Why not?
         */
        if (K0 == KEYWORD_MATCH && T1 == ']') {
                char *args = gensym();

                f = mkfunc(ty);
                avP(f->params, args);
                avP(f->constraints, NULL);
                avP(f->dflts, NULL);
                f->rest = 0;

                Token match = *tok();
                next();
                next();

                if (T0 != '{') {
                        Expr *pat = parse_pattern(ty);

                        consume(TOKEN_FAT_ARROW);

                        Expr *good = parse_expr(ty, 0);
                        Expr *bad = (K0 == KEYWORD_ELSE)
                                  ? (next(), parse_expr(ty, 0))
                                  : NULL;

                        unconsume('}');

                        if (bad != NULL) {
                                unconsume(TOKEN_EXPRESSION);
                                tok()->e = bad;

                                unconsume(TOKEN_FAT_ARROW);

                                unconsume(TOKEN_IDENTIFIER);
                                tok()->identifier = "it";

                                unconsume(',');
                        }

                        unconsume(TOKEN_EXPRESSION);
                        tok()->e = good;

                        unconsume(TOKEN_FAT_ARROW);

                        unconsume(TOKEN_EXPRESSION);
                        tok()->e = pat;

                        unconsume('{');
                }

                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = args;

                putback(match);

                f->body = to_stmt(prefix_match(ty));

                return f;
        }

        int in_type = EXPRESSION_IN;

        if (T1 == TOKEN_KEYWORD) switch (K1) {
        case KEYWORD_IN:
        InSection:
                next();
                next();
                e = parse_expr(ty, 0);
                consume(']');
                f = mkfunc(ty);
                avP(f->params, gensym());
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
                f->end = TEnd;
                return f;
        case KEYWORD_NOT:
                next();
                if (K1 == KEYWORD_IN) {
                        in_type = EXPRESSION_NOT_IN;
                        goto InSection;
                }
                break;
        }

        e = mkxpr(ARRAY);
        e->start = start;

        if (CatchError()) {
                goto End;
        }

        while (T0 != ']') {
                setctx(LEX_PREFIX);
                if (T0 == TOKEN_STAR) {
                        Expr *item = mkexpr(ty);
                        next();

                        item->type = EXPRESSION_SPREAD;
                        if (T0 == ']' || T0 == ',') {
                                item->value = mkexpr(ty);
                                item->value->type = EXPRESSION_IDENTIFIER;
                                item->value->module = NULL;
                                item->value->identifier = "*";
                                item->value->start = item->start;
                                item->value->end = item->end = TEnd;
                        } else {
                                item->value = parse_expr(ty, 0);
                        }

                        item->end = TEnd;

                        avP(e->elements, item);
                        avP(e->optional, false);
                } else {
                        if (T0 == TOKEN_QUESTION) {
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

                        if (e->compr.pattern->type != EXPRESSION_LIST) {
                                iter_sugar(ty, &e->compr.pattern, &e->compr.iter);
                        } else {
                                consume_keyword(KEYWORD_IN);
                                e->compr.iter = parse_expr(ty, 0);
                        }

                        e->compr.cond = try_consume(KEYWORD_IF)
                                      ? parse_expr(ty, 0)
                                      : NULL;

                        e->compr.where = (K0 == KEYWORD_WHERE)
                                       ? parse_let_definition(ty)
                                       : NULL;

                        expect(']');
                } else if (T0 == ',') {
                        next();
                } else if (
                        e->elements.count == 1 &&
                        get_infix_parser(ty) != NULL &&
                        (T1 == ']' || (have_not_in(ty) && token(2)->type == ']'))
                ) {
                        f = mkfunc(ty);
                        avP(f->params, gensym());
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
                                putback(t2);
                        }
                        putback(t);
                        f->body = mkstmt(ty);
                        f->body->type = STATEMENT_EXPRESSION;
                        f->body->expression = get_infix_parser(ty)(ty, e->elements.items[0]);
                        f->start = start;
                        e = f;
                } else {
                        expect(']');
                }
        }

        next();
        vvX(SavePoints);

End:
        e->end = TEnd;
        return e;
}

static Expr *
prefix_template(Ty *ty)
{
        Expr *template = mkxpr(TEMPLATE);
        Expr *save = CurrentTemplate;

        next();

        CurrentTemplate = template;
        while (T0 != TOKEN_TEMPLATE_END) {
                avP(template->template.stmts, parse_statement(ty, 0));
        }
        next();
        template->end = TEnd;
        CurrentTemplate = save;

        return template;
}

static Expr *
prefix_template_expr(Ty *ty)
{
        expression_vector *exprs = &CurrentTemplate->template.exprs;
        expression_vector *holes = &CurrentTemplate->template.holes;

        Expr *e = mkxpr(TEMPLATE_HOLE);
        e->hole.i = vN(CurrentTemplate->template.holes);

        next();

        if (T0 == '(') {
                next();
                avP(*holes, parse_expr(ty, 0));
                consume(')');
        } else if (T0 == '{') {
                e->type = EXPRESSION_TEMPLATE_VHOLE;
                next();
                avP(*holes, parse_expr(ty, 0));
                consume('}');
        } else if (T0 == ':') {
                e->type = EXPRESSION_TEMPLATE_THOLE;
                next();
                avP(*holes, parse_expr(ty, 99));
        } else if (T0 == '\\' || T0 == TOKEN_CHECK_MATCH || T0 == '!') {
                next();
                e->type = EXPRESSION_TEMPLATE_XHOLE;
                e->hole.expr = parse_expr(ty, 99);
                avP(*exprs, e);
        } else {
                avP(*holes, parse_expr(ty, 99));
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_greater(Ty *ty)
{
        Expr *e = mkxpr(REF_PATTERN);

        consume('>');

        e->target = assignment_lvalue(ty, parse_expr(ty, 0));

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
prefix_incrange(Ty *ty)
{
        Expr *e = mkxpr(DOT_DOT_DOT);

        Expr *zero = mkxpr(INTEGER);
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
        Expr *e = mkxpr(DOT_DOT);

        Expr *zero = mkxpr(INTEGER);
        zero->integer = 0;

        consume(TOKEN_DOT_DOT);

        e->left = zero;
        e->right = no_rhs(ty, 0) ? NULL : parse_expr(ty, 7);
        e->end = TEnd;

        return e;
}

static Expr *
infix_subscript(Ty *, Expr *);

static Expr *
implicit_subscript(Ty *ty, Expr *o)
{
        Expr *f = mkfunc(ty);
        f->body = mkret(ty, infix_subscript(ty, o));

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

        if (T0 == '{') {
                return prefix_implicit_lambda(ty);
        }

        if (T0 == TOKEN_KEYWORD && K0 == KEYWORD_NOT) {
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = "__not__";
                tok()->module = NULL;
        }

        Expr *o = mkxpr(IDENTIFIER);
        o->identifier = gensym();
        o->module = NULL;

        if (T0 == TOKEN_INTEGER) {
                intmax_t k = tok()->integer;
                next();
                unconsume(']');
                unconsume(TOKEN_INTEGER);
                tok()->integer = k;
                unconsume('[');
        }

        if (T0 == '[') {
                return implicit_subscript(ty, o);
        }

        Expr *e = mkexpr(ty);
        e->maybe = try_consume('?');
        e->start = start;
        e->type = try_consume('.') ? EXPRESSION_MEMBER_ACCESS
                                   : EXPRESSION_METHOD_CALL;
        e->member = prefix_identifier(ty);
        e->object = o;

        if (e->type == EXPRESSION_METHOD_CALL) {
                e = parse_method_call(ty, e);
        }

        Expr *f = mkfunc(ty);
        f->body = mkret(ty, e);
        f->start = start;
        f->end = TEnd;

        avP(f->params, o->identifier);
        avP(f->dflts, NULL);
        avP(f->constraints, NULL);

        return f;
}

static Expr *
prefix_colon(Ty *ty)
{
        T0 = '&';
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
        Expr *e = mkxpr(LIST);
        e->only_identifiers = true;
        vec_init(e->es);

        next();

        SAVE_NE(true);
        SAVE_NP(true);
        while (T0 != '|') {
                Expr *item = parse_expr(ty, 1);
                e->only_identifiers &= (item->type == EXPRESSION_IDENTIFIER);
                avP(e->es, item);
                if (T0 != '|')
                        consume(',');
        }
        LOAD_NE();
        LOAD_NP();

        consume('|');

        e->end = TEnd;

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
        f->end = TEnd;

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

        if (T0 == TOKEN_IDENTIFIER) {
                if (tok()->module != NULL && *tok()->module != '\0') {
                        next();
                        EStart = e->start;
                        EEnd= TEnd;
                        die("unexpected module qualifier in tag binding pattern");
                }
                if (T1 != '(') {
                        next();
                        consume('(');
                }
                Expr *call = parse_expr(ty, 10);
                call->type = EXPRESSION_TAG_PATTERN_CALL;
                call->start = e->start;
                call->end = TEnd;
                return call;
        }

        e->type = EXPRESSION_DICT;
        e->dflt = NULL;

        consume('{');

        vec_init(e->keys);
        vec_init(e->values);

        while (T0 != '}') {
                setctx(LEX_PREFIX);

                if (T0 == TOKEN_STAR && T1 == ':') {
                        struct location start = tok()->start;
                        next();
                        next();
                        unconsume(TOKEN_ARROW);
                        e->dflt = parse_expr(ty, 0);
                        e->dflt->start = start;
                        e->dflt->end = TEnd;
                } else if (T0 == TOKEN_STAR) {
                        Expr *item = mkexpr(ty);
                        next();
                        if (T0 == TOKEN_STAR) {
                                next();
                                item->type = EXPRESSION_SPLAT;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                        }

                        /*
                         * If we have just ** as an item on its own (e.g. %{'abc': 123, **, 'def': 321})
                         * we treat it as an identifier. This is a special case that is patched up
                         * later by __desugar_partial__.
                         */
                        if (T0 == ',' || T0 == '}') {
                                item->value = mkexpr(ty);
                                item->value->type = EXPRESSION_IDENTIFIER;
                                item->value->module = NULL;
                                item->value->identifier = "**" + (item->type == EXPRESSION_SPREAD);
                                item->value->start = item->start;
                                item->value->end = item->end = TEnd;
                        } else {
                                item->value = parse_expr(ty, 0);
                                item->end = TEnd;
                        }

                        avP(e->keys, item);
                        avP(e->values, NULL);
                } else {
                        SAVE_NC(true);
                        Expr *key = parse_expr(ty, 0);
                        avP(e->keys, key);
                        LOAD_NC();
                        if (key->type == EXPRESSION_IDENTIFIER) {
                                avP(e->values, key->constraint);
                                key->constraint = NULL;
                        } else {
                                avP(e->values, NULL);
                        }
                        if (T0 == ':') {
                                next();
                                *vvL(e->values) = parse_expr(ty, 0);
                        }
                }

                if (K0 == KEYWORD_FOR) {
                        next();
                        e->type = EXPRESSION_DICT_COMPR;
                        e->dcompr.pattern = parse_target_list(ty);
                        consume_keyword(KEYWORD_IN);
                        e->dcompr.iter = parse_expr(ty, 0);
                        e->dcompr.cond = try_consume(KEYWORD_IF)
                                       ? parse_expr(ty, 0)
                                       : NULL;
                        e->dcompr.where = (K0 == KEYWORD_WHERE)
                                        ? parse_let_definition(ty)
                                        : NULL;
                        expect('}');
                } else if (T0 == ',') {
                        next();
                } else {
                        expect('}');
                }
        }

        next();

        e->end = TEnd;

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
        Expr *fun = mkxpr(IDENTIFIER);
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

        setctx(LEX_PREFIX);

        Location start = tok()->start;

        if (T0 == ')') {
                next();
                e->end = TEnd;
                return e;
        }

        if (CatchError()) {
                goto End;
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
                        die("malformed generator comprehension argument");
                }
        }

        while (T0 == ',') {
                next();
                setctx(LEX_PREFIX);
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

        vvX(SavePoints);

End:
        e->end = TEnd;
        return e;
}

static Expr *
infix_eq(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = T0 == TOKEN_EQ ? EXPRESSION_EQ : EXPRESSION_MAYBE_EQ;
        next();

        e->start = left->start;
        e->target = assignment_lvalue(ty, left);

        if (get_prefix_parser(ty) == NULL) {
                e->type = (e->type == EXPRESSION_EQ)
                        ? EXPRESSION_REF_PATTERN
                        : EXPRESSION_REF_MAYBE_PATTERN;
                e->end = TEnd;
                return e;
        }

        SAVE_NA(true);

        if (left->type == EXPRESSION_LIST) {
                e->value = parse_expr(ty, -1);
        } else {
                e->value = parse_expr(ty, 1);
        }

        LOAD_NA();

        e->end = e->value->end;

        return e;
}

static Expr *
prefix_complement(Ty *ty)
{
        Expr *e = mkxpr(UNARY_OP);
        e->uop = "~";

        next();

        e->operand = parse_expr(ty, 8);
        e->end = TEnd;

        return e;
}

static Expr *
prefix_user_op(Ty *ty)
{
        Expr *e = mkxpr(UNARY_OP);
        e->uop = tok()->operator;

        next();

        e->operand = parse_expr(ty, 9);
        e->end = TEnd;

        return e;
}

static Expr *
infix_complement(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_USER_OP;
        e->start = left->start;
        e->left = left;
        e->op_name = "~";

        next();

        e->right = parse_expr(ty, 7);
        e->end = TEnd;

        return e;
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
        e->end = TEnd;

        return e;
}

static Expr *
infix_type_union(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->start = left->start;
        e->type = EXPRESSION_TYPE_UNION;
        avP(e->es, left);

        while (T0 == '|') {
                next();
                avP(e->es, parse_type(ty, 5));
        }

        e->end = TEnd;

        return e;
}

static Expr *
infix_list(Ty *ty, Expr *left)
{

        Expr *e = mkexpr(ty);
        e->start = left->start;
        e->type = EXPRESSION_LIST;
        avP(e->es, left);

        SAVE_NE(true);

        while (T0 == ',') {
                next();
                avP(e->es, parse_expr(ty, 1));
        }

        LOAD_NE();

        e->end = TEnd;

        return e;
}

static Expr *
infix_count_from(Ty *ty, Expr *left)
{
        next();

        Expr *e = mkxpr(DOT_DOT);
        e->start = left->start;
        e->left = left;
        e->right = NULL;
        e->end = TEnd;

        return e;
}

static Expr *
infix_subscript(Ty *ty, Expr *left)
{

        Expr *e = mkexpr(ty);

        consume('[');

        if (T0 == ']') {
                char *xs = gensym();
                char *i = gensym();

                next();

                e->type = EXPRESSION_SUBSCRIPT;
                e->container = mkid(xs);
                e->subscript = mkid(i);
                e->subscript->start = e->start;
                e->end = TEnd;

                Expr *f = mkfunc(ty);
                avP(f->params, i);
                avP(f->dflts, NULL);
                avP(f->constraints, NULL);
                f->body = mkret(ty, e);
                f->start = left->start;
                f->end = TEnd;

                Stmt *def = mkstmt(ty);
                def->type = STATEMENT_DEFINITION;
                def->pub = false;
                def->target = mkid(xs);
                def->value = left;

                Stmt *multi = mkstmt(ty);
                multi->type = STATEMENT_MULTI;
                avP(multi->statements, def);
                avP(multi->statements, to_stmt(f));

                return to_expr(multi);
        }

        Expr *i;
        if (T0 == ';') {
                i = NULL;
        } else {
                i = parse_expr(ty, -1);
        }

        if (T0 == ']' && i != NULL) {
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

        if (T0 != ']' && T0 != ';') {
                e->slice.j = parse_expr(ty, 0);
        }

        if (T0 == ']') {
                goto End;
        }

        consume(';');

        if (T0 != ']') {
                e->slice.k = parse_expr(ty, 0);
        }

End:
        consume(']');

        e->end = TEnd;

        return e;
}

static Expr *
infix_as(Ty *ty, Expr *left)
{
        consume_keyword(KEYWORD_AS);

        if (NoEquals) {
                Expr *alias = parse_expr(ty, 99);

                if (alias->type != EXPRESSION_IDENTIFIER) {
                        EStart = alias->start;
                        EEnd = alias->end;
                        die("pattern alias must be an identifier");
                }

                alias->type = EXPRESSION_ALIAS_PATTERN;
                alias->aliased = left;

                return alias;
        } else {
                Expr *cast = mkxpr(CAST);
                cast->left = left;
                cast->right = parse_expr(ty, 1);
                cast->start = left->start;
                cast->end = TEnd;
                return cast;
        }
}

static Expr *
infix_member_access(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(MEMBER_ACCESS);

        e->start = left->start;
        e->maybe = (T0 == TOKEN_DOT_MAYBE);

        next();

        /*
         * xs.N is syntactic sugar for xs[N]
         */
        if (T0 == TOKEN_INTEGER) {
                e->type = EXPRESSION_SUBSCRIPT;
                e->container = left;
                e->subscript = mkexpr(ty);
                e->subscript->type = EXPRESSION_INTEGER;
                e->subscript->integer = tok()->integer;
                next();
                e->start = left->start;
                e->end = TEnd;
                return e;
        }

        e->object = left;

        if (tok()->type == '{') {
                next();
                e->member = parse_expr(ty, 1);
                consume('}');
                e->type = EXPRESSION_DYN_MEMBER_ACCESS;
        } else if (AllowErrors && T0 != TOKEN_IDENTIFIER) {
                e->member = &BlankID;
        } else {
                e->member = prefix_identifier(ty);

                if (is_fun_macro(ty, NULL, e->member->identifier)) {
                        Expr *call = infix_function_call(ty, e->member);
                        avI(call->args, left, 0);
                        avI(call->fconds, NULL, 0);
                        return call;
                }

                if (is_macro(ty, NULL, e->member->identifier)) {
                        return typarse(
                                ty,
                                e->member,
                                left,
                                &e->member->start,
                                &e->member->end
                        );
                }
        }


        if (
                !have_without_nl(ty, '(')
             && !have_without_nl(ty, '$')
             && !have_without_nl(ty, TOKEN_AT)
        ) {
                e->end = TEnd;
                return e;
        } else {
                e->type = (e->type == EXPRESSION_MEMBER_ACCESS)
                        ? EXPRESSION_METHOD_CALL
                        : EXPRESSION_DYN_METHOD_CALL;
                return parse_method_call(ty, e);
        }
}

static Expr *
infix_squiggly_not_nil_arrow(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(NOT_NIL_VIEW_PATTERN);

        consume('$~>');

        e->left = left;
        e->right = parse_expr(ty, 0);
        e->start = left->start;
        e->end = TEnd;

        return e;
}

static Expr *
infix_squiggly_arrow(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(VIEW_PATTERN);

        consume(TOKEN_SQUIGGLY_ARROW);

        e->left = left;
        e->right = parse_expr(ty, 0);
        e->start = left->start;
        e->end = TEnd;

        return e;
}

static Expr *
infix_arrow_function(Ty *ty, Expr *left)
{
        Expr *e;

        consume(TOKEN_ARROW);

        if (TypeContext) {
                e = mkxpr(FUNCTION_TYPE);
                e->left = left;
                e->right = parse_expr(ty, 0);
                e->start = left->start;
                e->end = TEnd;
                return e;
        }

        e = mkfunc(ty);
        e->start = left->start;

        e->proto = clone_slice_a(ty, left->start.s, left->end.s);

        if (
                left->type != EXPRESSION_LIST
             && (
                        left->type != EXPRESSION_TUPLE
                     || !left->only_identifiers
                )
            ) {
                Expr *l = mkxpr(LIST);
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
                Expr *dflt = NULL;
                if (p->type == EXPRESSION_EQ) {
                        dflt = p->value;
                        p = p->target;
                }
                if (p->type == EXPRESSION_IDENTIFIER) {
                        avP(e->params, p->identifier);
                        avP(e->constraints, p->constraint);
                } else if (p->type == EXPRESSION_MATCH_REST) {
                        avP(e->params, p->identifier);
                        avP(e->constraints, p->constraint);
                        e->rest = i;
                } else {
                        char *name = gensym();
                        avP(e->params, name);
                        avP(e->constraints, NULL);
                        avP(body->statements, mkdef(ty, definition_lvalue(ty, p), name));
                }
                avP(e->dflts, dflt);
        }

        Stmt *ret = mkret(ty, parse_expr(ty, 0));

        if (body->statements.count == 0) {
                e->body = ret;
        } else {
                avP(body->statements, ret);
                e->body = body;
        }

        e->end = TEnd;

        return e;
}

static Expr *
infix_identifier(Ty *ty, Expr *left)
{
        Expr *op = mkid(tok()->identifier);

        next();

        Expr *right = parse_expr(ty, 9);

        Expr *call = mkcall(ty, op);

        avP(call->args, left);
        avP(call->fconds, NULL);

        avP(call->args, right);
        avP(call->fconds, NULL);

        call->start = left->start;
        call->end = right->end;

        return call;
}

static Expr *
infix_kw_or(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_CHOICE_PATTERN;
        vec_init(e->es);

        avP(e->es, left);

        do {
                next();
                avP(e->es, parse_expr(ty, 1));
        } while (have_keyword(KEYWORD_OR));

        e->start = left->start;
        e->end = TEnd;

        return e;
}

static Expr *
infix_kw_and(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);

        e->type = EXPRESSION_KW_AND;
        e->left = left;
        e->start = left->start;

        consume_keyword(KEYWORD_AND);

        e->p_cond = parse_condparts(ty, false);

        e->end = TEnd;

        return e;
}

static Expr *
infix_kw_in(Ty *ty, Expr *left)
{
        Expr *e = mkexpr(ty);
        e->left = left;
        e->start = left->start;

        if (K0 == KEYWORD_NOT) {
                next();
                e->type = EXPRESSION_NOT_IN;
        } else {
                e->type = EXPRESSION_IN;
        }

        consume_keyword(KEYWORD_IN);

        e->right = parse_expr(ty, 6);
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

        Expr *nil = mkxpr(NIL);

        Expr *f = mkcall(ty, nil);
        avP(f->args, body);
        avP(f->fconds, NULL);

        Expr *call = mkcall(ty, left);
        avP(call->args, mkpartial(ty, f));
        avP(call->fconds, NULL);

        next();

        return call;
}

static Expr *
infix_conditional(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(CONDITIONAL);

        e->cond = left;

        consume(TOKEN_QUESTION);

        SAVE_NC(true);
        if (T0 != ':') {
                e->then = parse_expr(ty, 2);
                consume(':');
                e->otherwise = parse_expr(ty, 2);
        } else {
                consume(':');
                e->then = parse_expr(ty, 2);
                e->otherwise = mkxpr(NIL);
        }
        LOAD_NC();

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
        e->end = TEnd;

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
        e->end = TEnd;

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

BINARY_OPERATOR(not_eq,   NOT_EQ,    6, false)
BINARY_OPERATOR(dbl_eq,   DBL_EQ,    6, false)

BINARY_OPERATOR(and,      AND,         5, false)
BINARY_OPERATOR(xor,      XOR,         5, false)
BINARY_OPERATOR(shl,      SHL,         7, false)
BINARY_OPERATOR(shr,      SHR,         7, false)
BINARY_OPERATOR(bit_and,  BIT_AND,     5, false)
BINARY_OPERATOR(bit_or,   BIT_OR,      5, false)

BINARY_OPERATOR(or,       OR,          4, false)
BINARY_OPERATOR(wtf,      WTF,         4, false)

BINARY_OPERATOR(check_match, CHECK_MATCH,  3, false)

BINARY_LVALUE_OPERATOR(plus_eq,  PLUS_EQ,  2, true)
BINARY_LVALUE_OPERATOR(star_eq,  STAR_EQ,  2, true)
BINARY_LVALUE_OPERATOR(div_eq,   DIV_EQ,   2, true)
BINARY_LVALUE_OPERATOR(mod_eq,   MOD_EQ,   2, true)
BINARY_LVALUE_OPERATOR(minus_eq, MINUS_EQ, 2, true)

BINARY_LVALUE_OPERATOR(and_eq, AND_EQ, 2, true)
BINARY_LVALUE_OPERATOR(or_eq,  OR_EQ,  2, true)
BINARY_LVALUE_OPERATOR(xor_eq, XOR_EQ, 2, true)
BINARY_LVALUE_OPERATOR(shl_eq, SHL_EQ, 2, true)
BINARY_LVALUE_OPERATOR(shr_eq, SHR_EQ, 2, true)
/* * * * | end of infix parsers | * * * */

static prefix_parse_fn *
get_prefix_parser(Ty *ty)
{
        setctx(LEX_PREFIX);

        switch (T0) {
        case TOKEN_INTEGER:            return prefix_integer;
        case TOKEN_REAL:               return prefix_real;
        case TOKEN_STRING:             return prefix_string;
        case TOKEN_REGEX:              return prefix_regex;

        case '"':                      return prefix_ss;

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
        case '^':                      return prefix_carat;
        case '>':                      return prefix_greater;

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
        case '~':                      return prefix_complement;

        case TOKEN_ARROW:              return prefix_arrow;

        case '|':                      return prefix_bit_or;

        case TOKEN_STAR:               return prefix_star;

        case TOKEN_EXPRESSION:         return prefix_expr;

        default:                       return NULL;
        }

Keyword:

        switch (K0) {
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
        case KEYWORD_TYPEOF:    return prefix_typeof;
        case KEYWORD_THROW:     return prefix_throw;
        case KEYWORD_WITH:      return prefix_with;
        case KEYWORD_DO:        return prefix_do;
        case KEYWORD_SUPER:     return prefix_super;

        case KEYWORD_IF:
        case KEYWORD_FOR:
        case KEYWORD_WHILE:
        case KEYWORD_TRY:
        case KEYWORD_RETURN:
        case KEYWORD_CONTINUE:
        case KEYWORD_BREAK:
                return prefix_statement;

        default:                return NULL;
        }
}

static infix_parse_fn *
get_infix_parser(Ty *ty)
{
        setctx(LEX_INFIX);

        switch (T0) {
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
        case '$~>':                return infix_squiggly_not_nil_arrow;

        case TOKEN_DOT_DOT:        return no_rhs(ty, 1) ? infix_count_from : infix_range;
        case TOKEN_DOT_DOT_DOT:    return no_rhs(ty, 1) ? infix_count_from : infix_incrange;

        case TOKEN_IDENTIFIER:     return infix_identifier;

        case TOKEN_PLUS_EQ:        return infix_plus_eq;
        case TOKEN_STAR_EQ:        return infix_star_eq;
        case TOKEN_DIV_EQ:         return infix_div_eq;
        case TOKEN_MOD_EQ:         return infix_mod_eq;
        case TOKEN_MINUS_EQ:       return infix_minus_eq;

        case TOKEN_AND_EQ:         return infix_and_eq;
        case TOKEN_OR_EQ:          return infix_or_eq;
        case TOKEN_XOR_EQ:         return infix_xor_eq;
        case TOKEN_SHL_EQ:         return infix_shl_eq;
        case TOKEN_SHR_EQ:         return infix_shr_eq;

        case TOKEN_MAYBE_EQ:
        case TOKEN_EQ:             return infix_eq;

        case TOKEN_SHL:            return infix_shl;
        case TOKEN_SHR:            return infix_shr;
        case '^':                  return infix_xor;
        case '&':                  return infix_bit_and;
        case '|':                  return TypeContext ? infix_type_union : infix_bit_or;

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
        case '~':                  return infix_complement;
        case TOKEN_NOT_EQ:         return infix_not_eq;
        case TOKEN_DBL_EQ:         return infix_dbl_eq;
        case TOKEN_CHECK_MATCH:    return infix_check_match;
        case TOKEN_OR:             return infix_or;
        case TOKEN_WTF:            return infix_wtf;
        case TOKEN_AND:            return infix_and;
        case TOKEN_USER_OP:        return infix_user_op;

        case TOKEN_ELVIS:
        case TOKEN_QUESTION:       return infix_conditional;

        case '\\':     return next_without_nl(ty, '(') ? infix_slash  : NULL;
        case TOKEN_AT: return next_without_nl(ty, '(') ? infix_at     : NULL;

        default:                   return NULL;
        }

Keyword:

        switch (K0) {
        case KEYWORD_AND: return infix_kw_and;
        case KEYWORD_OR:  return infix_kw_or;
        case KEYWORD_NOT:
        case KEYWORD_IN:  return infix_kw_in;
        case KEYWORD_AS:  return infix_as;
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
        setctx(LEX_INFIX);

        switch (T0) {
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

        case TOKEN_IDENTIFIER:
                return tok()->raw && tok()->start.line == token(-1)->end.line
                     ? 9
                     : -3;

        case TOKEN_MINUS:          return 8;
        case TOKEN_PLUS:           return 8;

        case TOKEN_DOT_DOT:        return 7;
        case TOKEN_DOT_DOT_DOT:    return 7;

        case TOKEN_CMP:            return 7;
        case TOKEN_GEQ:            return 7;
        case TOKEN_LEQ:            return 7;
        case TOKEN_GT:             return 7;
        case TOKEN_LT:             return 7;

        case TOKEN_SHL:            return 7;
        case TOKEN_SHR:            return 7;

        case '~':                  return 7;

        case TOKEN_NOT_EQ:         return 6;
        case TOKEN_DBL_EQ:         return 6;

        case TOKEN_AND:            return 5;
        case '^':                  return 5;
        case '&':                  return 5;
        case '|':                  return NoPipe ? -3 : 5;

        case TOKEN_OR:             return 4;
        case TOKEN_WTF:            return 4;

        /* this may need to have lower precedence. I'm not sure yet. */
        case '$~>':                return 3;
        case TOKEN_SQUIGGLY_ARROW: return 3;
        case TOKEN_CHECK_MATCH:    return 3;

        case TOKEN_QUESTION:       return 3;
        case TOKEN_ELVIS:          return 3;


        case TOKEN_MAYBE_EQ:
        case TOKEN_EQ:             return NoEquals ? -3 : 2;
        case TOKEN_PLUS_EQ:        return 2;
        case TOKEN_STAR_EQ:        return 2;
        case TOKEN_DIV_EQ:         return 2;
        case TOKEN_MOD_EQ:         return 2;

        case TOKEN_AND_EQ:         return 2;
        case TOKEN_OR_EQ:          return 2;
        case TOKEN_XOR_EQ:         return 2;
        case TOKEN_SHR_EQ:         return 2;
        case TOKEN_SHL_EQ:         return 2;

        case TOKEN_MINUS_EQ:       return 2;
        case TOKEN_ARROW:          return 2;

        case ',':                  return 0;

        case TOKEN_KEYWORD:        goto Keyword;
        case TOKEN_USER_OP:        goto UserOp;

        default:                   return -3;
        }

Keyword:
        switch (K0) {
        case KEYWORD_OR: return NoAndOr ? -3 : 2;

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
        case EXPRESSION_TEMPLATE_XHOLE:
        case EXPRESSION_KW_AND:
                return e;
        case EXPRESSION_REF_PATTERN:
                e->target = assignment_lvalue(ty, e->target);
                return e;
        case EXPRESSION_LIST:
        case EXPRESSION_CHOICE_PATTERN:
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
                for (int i = 0; i < vN(e->elements); ++i) {
                        *v_(e->elements, i) = definition_lvalue(ty, *v_(e->elements, i));
                }
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
                                        die("shorthand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = definition_lvalue(ty, e->values.items[i]);
                }
                return e;
        }

        die_at(e, "expression is not a valid definition lvalue: %s", ExpressionTypeName(e));
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
                e->type = EXPRESSION_CHOICE_PATTERN;
        case EXPRESSION_TUPLE:
        case EXPRESSION_CHOICE_PATTERN:
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
                                        die("short-hand target in dict lvalue must be an identifier");
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
        try_symbolize_application(ty, NULL, e);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                if (strcmp(e->identifier, "_") == 0 && e->module == NULL) {
                        // TODO: ??
                        // e->type = EXPRESSION_MATCH_ANY;
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
        case EXPRESSION_TEMPLATE_HOLE:
        case EXPRESSION_TEMPLATE_XHOLE:
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
                                        die("short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                key->string = e->keys.items[i]->identifier;
                                e->values.items[i] = e->keys.items[i];
                                e->keys.items[i] = key;
                        }
                        e->values.items[i] = assignment_lvalue(ty, e->values.items[i]);
                }
                return e;
        case EXPRESSION_REF_PATTERN:
                e->target = assignment_lvalue(ty, e->target);
                return e;
        default:
                EStart = e->start;
                EEnd = e->end;
                die("expression is not a valid assignment lvalue: %s", ExpressionTypeName(e));
        }
}

/*
 * This is kind of a hack.
 */
static Expr *
parse_definition_lvalue(Ty *ty, int context, Expr *e)
{
        int save = TokenIndex;

        if (e == NULL) {
                SAVE_NI(true);
                SAVE_NE(true);
                SAVE_NA(false);
                SAVE_NC(false);
                SAVE_LC(true);
                e = parse_expr(ty, 1);
                EStart = e->start;
                EEnd = e->end;
                LOAD_LC();
                LOAD_NC();
                LOAD_NA();
                LOAD_NE();
                LOAD_NI();
        }

        e = definition_lvalue(ty, e);

        if (context == LV_LET && T0 == ',') {
                Expr *l = mkxpr(LIST);
                l->start = e->start;
                vec_init(l->es);
                avP(l->es, e);
                while (T0 == ',') {
                        next();
                        Expr *e = parse_definition_lvalue(ty, LV_SUB, NULL);
                        if (e == NULL) {
                                die("expected lvalue but found %s", token_show(ty, tok()));
                        }
                        avP(l->es, e);
                }
                e = l;
        }

        switch (context) {
        case LV_LET:
                if (T0 != TOKEN_EQ)
                        goto Error;
                break;
        case LV_EACH:
                if (K0 == KEYWORD_IN)
                        break;
                if (T0 != ',')
                        goto Error;
                if (false && T1 != TOKEN_IDENTIFIER)
                        goto Error;
                break;
        default:
                break;
        }

        e->end = TEnd;
        return e;

Error:
        seek(ty, save);
        return NULL;
}

static Expr *
parse_target_list(Ty *ty)
{
        SAVE_NI(true);
        SAVE_NE(true);
        SAVE_NC(false);

        Expr *target = parse_expr(ty, 0);

        LOAD_NC();
        LOAD_NE();
        LOAD_NI();

        if (T0 != ',' && !have_keyword(KEYWORD_IN)) {
                return target;
        }

        Expr *e = mkxpr(LIST);

        avP(e->es, parse_definition_lvalue(ty, LV_EACH, target));

        if (e->es.items[0] == NULL) {
        Error:
                die("expected lvalue in for-each loop");
        }

        while (
                T0 == ',' && (
                        T1 == TOKEN_IDENTIFIER ||
                        T1 == '[' ||
                        T1 == '{' ||
                        (T1 == '%' && token(2)->type == '{') ||
                        true /* FIXME: why were we doing these lookaheads? */
                )
        ) {
                next();

                target = parse_definition_lvalue(ty, LV_EACH, NULL);
                if (target == NULL) {
                        goto Error;
                }

                avP(e->es, target);
        }

        return e;
}

static Stmt *
parse_for_loop(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_FOR_LOOP;

        consume_keyword(KEYWORD_FOR);

        bool match = false;
        bool cloop = false;

        if (have_keyword(KEYWORD_MATCH)) {
                match = true;
                next();
        } else {
                int save = TokenIndex;
                SAVE_JB;
                SAVE_NI(true);
                SAVE_NE(NoEquals);
                if (setjmp(JB) != 0) {
                        LOAD_NE();
                        cloop = true;
                } else {
                        parse_expr(ty, 0);
                        cloop = T0 == ';';
                }
                LOAD_NI();
                RESTORE_JB;
                seek(ty, save);
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

                s->each.target = parse_target_list(ty);

                if (s->each.target->type != EXPRESSION_LIST) {
                        iter_sugar(ty, &s->each.target, &s->each.array);
                } else {
                        consume_keyword(KEYWORD_IN);
                        s->each.array = parse_expr(ty, 0);
                }

                if (T0 == TOKEN_KEYWORD && K0 == KEYWORD_IF) {
                        next();
                        s->each.cond = parse_expr(ty, 0);
                } else {
                        s->each.cond = NULL;
                }

                if (T0 == TOKEN_KEYWORD && K0 == KEYWORD_WHILE) {
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

                s->end = TEnd;

                return s;
        }

        if (T0 == '(') {
                next();
        }

        if (T0 == ';') {
                next();
                s->for_loop.init = NULL;
        } else {
                s->for_loop.init = parse_statement(ty, -1);
        }

        if (T0 == ';') {
                s->for_loop.cond = NULL;
        } else {
                s->for_loop.cond = parse_expr(ty, 0);
        }

        consume(';');

        if (T0 == ')') {
                next();
                s->for_loop.next = NULL;
        } else {
                s->for_loop.next = parse_expr(ty, 0);
        }

        s->end = TEnd;

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
                p->target = parse_definition_lvalue(ty, LV_LET, NULL);
                consume(TOKEN_EQ);
                SAVE_NA(true);
                p->e = parse_expr(ty, -1);
                LOAD_NA();
                return p;
        }

        SAVE_NE(true);
        Expr *e = parse_expr(ty, 0);
        LOAD_NE();

        if (T0 == TOKEN_EQ) {
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
                        die("illegal condition used as controlling expression of if statement");
                }

                if (not && part->target == NULL) {
                        Expr *not = mkxpr(PREFIX_BANG);
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
        if (have_keywords(KEYWORD_WHILE, KEYWORD_MATCH)) {
                next();
                Stmt *m = parse_match_statement(ty);
                m->type = STATEMENT_WHILE_MATCH;
                m->start = start;
                return m;
        }

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_WHILE;

        consume_keyword(KEYWORD_WHILE);

        vec_init(s->While.parts);

        SAVE_NA(true);

        avP(s->While.parts, parse_condpart(ty));

        while (have_keyword(KEYWORD_AND)) {
                next();
                avP(s->While.parts, parse_condpart(ty));
        }

        LOAD_NA();

        s->While.block = parse_block(ty);

        s->end = TEnd;

        return s;
}

static Stmt *
parse_if(Ty *ty)
{

        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_IF;

        consume_keyword(KEYWORD_IF);

        s->iff.neg = try_consume(KEYWORD_NOT);
        s->iff.parts = parse_condparts(ty, s->iff.neg);
        s->iff.then = parse_statement(ty, -1);

        if (have_keyword(KEYWORD_ELSE)) {
                next();
                s->iff.otherwise = parse_statement(ty, -1);
        } else {
                s->iff.otherwise = NULL;
        }

        s->end = TEnd;

        return s;
}

static Stmt *
parse_match_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_MATCH;

        consume_keyword(KEYWORD_MATCH);

        s->match.e = parse_expr(ty, -1);

        if (CatchError()) {
                goto End;
        }

        consume('{');

        SAVE_NA(false);

        while (T0 != '}') {
                avP(s->match.patterns, parse_pattern(ty));
                consume(TOKEN_FAT_ARROW);
                avP(s->match.statements, parse_statement(ty, 0));

                if (T0 == ',') {
                        next();
                }
        }

        LOAD_NA();

        consume('}');

        vvX(SavePoints);

End:
        return s;
}

static Stmt *
parse_function_definition(Ty *ty)
{
        Stmt *s = mkstmt(ty);

        if (K0 == KEYWORD_MACRO) {
                Token kw = *token(0);
                consume(TOKEN_KEYWORD);

                op_fixup(ty, 0);

                Token name = *token(0);
                consume(TOKEN_IDENTIFIER);

                if (T0 == '(') {
                        s->type = STATEMENT_FUN_MACRO_DEFINITION;
                } else {
                        s->type = STATEMENT_MACRO_DEFINITION;
                        unconsume(')');
                        unconsume('(');
                }

                putback(name);
                putback(kw);
        } else {
                s->type = STATEMENT_FUNCTION_DEFINITION;
        }

        Location target_start = tok()->start;
        Location target_end = tok()->end;
        char *module = NULL;

        // FIXME: Hack to skip decorators and find the function name
        for (int i = 0; i < 128 && s->type == STATEMENT_FUNCTION_DEFINITION; ++i) {
                if (KW(i) == KEYWORD_FUNCTION) {
                        if (op_fixup(ty, i + 1)) {
                                s->type = STATEMENT_OPERATOR_DEFINITION;
                        }

                        if (token(i + 1)->type == TOKEN_IDENTIFIER) {
                                target_start = token(i + 1)->start;
                                target_end = token(i + 1)->end;
                                module = token(i + 1)->module;
                        }

                        break;
                }
        }

        Expr *f = prefix_function(ty);
        if (f->name == NULL) {
                die("anonymous function definition used in statement context");
        }

        if (s->type == STATEMENT_MACRO_DEFINITION) {
                avI(f->params, "self", 0);
                avI(f->constraints, NULL, 0);
                avI(f->dflts, NULL, 0);
        }

        if (
                0 && contains(OperatorCharset, f->name[0]) &&
                (
                     f->name[1] == '\0' ||
                     f->name[0] != '$'  ||
                     contains(OperatorCharset, f->name[1])
                )
        ) {
                s->type = STATEMENT_OPERATOR_DEFINITION;
        }

        Expr *target = mkxpr(IDENTIFIER);
        target->identifier = f->name;
        target->module = module;
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
        next();

        setctx(LEX_INFIX);

        expect(TOKEN_USER_OP);
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
                die("expected 'left' or 'right' in operator directive");
        }

        if (T0 != TOKEN_NEWLINE) {
                Expr *e = parse_expr(ty, 0);
                table_put(ty, &uopcs, uop, PTR(e));
        }

        consume(TOKEN_NEWLINE);

        return &NullStatement;
}

static Stmt *
parse_return_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_RETURN;
        vec_init(s->returns);

        consume_keyword(KEYWORD_RETURN);

        if (tok()->start.line != s->start.line || get_prefix_parser(ty) == NULL) {
                return s;
        }

        avP(s->returns, parse_expr(ty, 0));

        while (T0 == ',') {
                next();
                avP(s->returns, parse_expr(ty, 0));
        }

        if (T0 == ';')
                next();

        return s;
}

static Stmt *
parse_let_definition(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_DEFINITION;

        if (K0 == KEYWORD_CONST) {
                next();
                s->cnst = true;
        } else {
                expect_one_of(KEYWORD_LET, KEYWORD_WHERE);
                next();
        }

        SAVE_LC(true);
        s->target = parse_definition_lvalue(ty, LV_LET, NULL);
        if (s->target == NULL) {
                die("failed to parse lvalue in 'let' definition");
        }
        LOAD_LC();

        consume(TOKEN_EQ);

        SAVE_NA(true);
        s->value = parse_expr(ty, -1);
        LOAD_NA();

        s->end = TEnd;

        if (T0 == ';')
                next();

        return s;
}

static Stmt *
parse_defer_statement(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_DEFER;

        consume_keyword(KEYWORD_DEFER);

        s->expression = mkfunc(ty);
        s->expression->body = parse_statement(ty, -1);

        if (T0 == ';') {
                next();
        }

        return s;
}

inline static Stmt *
try_conditional_from(Ty *ty, Stmt *s)
{
        if (tok()->start.line == TEnd.line && have_keyword(KEYWORD_IF)) {
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

        if (
                tok()->start.line == s->start.line
             && get_prefix_parser(ty) != NULL
             && (
                        !have_keyword(KEYWORD_IF)
                     || T0 == '('
                )
        ) {
                s->expression = parse_expr(ty, 0);
        } else {
                s->expression = NULL;
        }

        s = try_conditional_from(ty, s);

        if (T0 == ';')
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

        if (T0 == ';')
                next();

        return s;
}

static Stmt *
parse_null_statement(Ty *ty)
{
        consume(';');
        return &NullStatement;
}

inline static bool
should_split(Ty *ty)
{
        if (tok()->start.line == TEnd.line) {
                return false;
        }

        switch (T0) {
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

        setctx(LEX_PREFIX);

        PLOG("%s", "");
        PLOG(
                "%sparse_expr%s(%d): [%s] | tok()=[%s]: %s%.*s%s~%s\n",
                TERM(93),
                TERM(0),
                prec,
                token_show(ty, token(-1)),
                token_showx(ty, tokenx(0), TERM(92;1)),
                TERM(97;1;3),
                (TEnd.s == NULL) ? 0 : (int)strcspn(TEnd.s, "\n"),
                TEnd.s,
                TERM(91;1),
                TERM(0)
        );

        if (++ParseDepth > 256)
                die("exceeded maximum recursion depth of 256");

        //if (AllowErrors && CatchError()) {
        //        next();
        //        -ParseDepth;
        //        return &NullExpr;
        //}

        prefix_parse_fn *f = get_prefix_parser(ty);
        if (f == NULL) {
                die(
                        "expected expression but found %s%s%s",
                        TERM(34),
                        token_show(ty, tok()),
                        TERM(0)
                );
        }

        e = LastParsedExpr = f(ty);

        while (!should_split(ty) && prec < get_infix_prec(ty)) {
                infix_parse_fn *f = get_infix_parser(ty);
                if (f == NULL) {
                        die("unexpected token after expression: %s", token_show(ty, tok()));
                }
                if (
                        (
                                (T1 == ']' && T0 != '[')
                             || (have_not_in(ty) && token(2)->type == ']')
                        )
                     && !is_postfix(tok())
                ) {
                        // Special case for operator slices. Very based!
                        goto End;
                }
                e = LastParsedExpr = f(ty, e);
        }

        if (have_without_nl(ty, '"')) {
                Expr *ss = prefix_ss(ty);
                ss->lang = e;
                e = ss;
        }

End:
        PLOG(
                "parse_expr(): => %s%s%s : %s%.*s%s",
                TERM(95),
                ExpressionTypeName(e),
                TERM(0),
                TERM(97;1;3),
                (TEnd.s == NULL) ? 0 : (int)strcspn(TEnd.s, "\n"),
                TEnd.s,
                TERM(0)
        );

        //if (AllowErrors) {
        //        vvX(SavePoints);
        //}

        --ParseDepth;

        return LastParsedExpr = e;
}

static Stmt *
parse_block(Ty *ty)
{
        Stmt *block = mkstmt(ty);

        consume('{');

        block->type = STATEMENT_BLOCK;
        vec_init(block->statements);

        CompilerScopePush(ty);

        if (CatchError()) {
                goto End;
        }

        while (T0 != '}') {
                Stmt *s = parse_statement(ty, -1);
                s->end = TEnd;
                avP(block->statements, s);
        }

        vvX(SavePoints);

End:
        CompilerScopePop(ty);

        consume('}');

        block->end = TEnd;

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
        return s;
}

static Expr *
parse_method(
        Ty *ty,
        Location start,
        Expr *decorator_macro,
        char const *doc,
        expression_vector decorators
)
{
        unconsume(TOKEN_KEYWORD);
        tok()->keyword = KEYWORD_FUNCTION;

        Expr *func = prefix_function(ty);
        func->start = start;
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

typedef struct {
        char *name;
        Expr *constraint;
        Expr *dflt;
} FuncParam;

static Stmt *
parse_class_definition(Ty *ty)
{
        Location start = tok()->start;

        bool tag = K0 == KEYWORD_TAG;
        bool trait = K0 == KEYWORD_TRAIT;
        next();

        expect(TOKEN_IDENTIFIER);

        Stmt *s = mkstmt(ty);
        s->class.name = tok()->identifier;

        s->start = start;
        s->class.loc = tok()->start;

        next();

        if (T0 == '[') {
                parse_type_params(ty, &s->class.type_params);
        }

        if (T0 == '=') {
                next();
                s->type = STATEMENT_TYPE_DEFINITION;
                s->class.type = parse_expr(ty, 0);
                s->end = TEnd;
                return s;
        } else {
                s->type = tag ? STATEMENT_TAG_DEFINITION
                              : STATEMENT_CLASS_DEFINITION;
                s->class.is_trait = trait;
        }

        /*
         * Allow some optional parameters here that will implicitly become
         * parameters of the init() method which are immediately assigned
         * to instance variables of the same name.
         *
         * e.g.
         *      class Foo(name: String, xs) {
         *              init() {
         *                      assert @name == name
         *                      assert @xs == xs
         *              }
         *      }
         *
         * is equivalent to
         *
         *      class Foo {
         *              init(name: String, xs) {
         *                      @name = name
         *                      @xs = xs
         *                      assert @name == name
         *                      assert @xs == xs
         *              }
         *      }
         */
        Expr *init = NULL;
        vec(FuncParam) init_params = {0};
        if (!tag && try_consume('(')) while (!try_consume(')')) {
                FuncParam param;
                Location start;
                Location end;

                expect(TOKEN_IDENTIFIER);
                param.name = tok()->identifier;
                start = tok()->start;
                end = tok()->end;
                next();

                param.constraint = try_consume(':')
                                 ? parse_expr(ty, 0)
                                 : NULL;

                param.dflt = try_consume('=')
                           ? parse_expr(ty, 0)
                           : NULL;

                if (T0 != ')') {
                        consume(',');
                }

                Expr *field = mkid(param.name);
                field->start = start;
                field->end = end;
                field->constraint = param.constraint;

                if (param.dflt != NULL) {
                        Expr *eql = mkxpr(EQ);
                        eql->target = field;
                        eql->value = param.dflt;
                        field = eql;
                }

                avP(init_params, param);
                avP(s->tag.fields, field);
        }

        if (T0 == '<') {
                next();
                s->tag.super = parse_type(ty, 0);
        } else {
                s->tag.super = NULL;
        }

        if (T0 == ':') {
                next();
                do {
                        expect(TOKEN_IDENTIFIER);
                        avP(s->tag.traits, parse_type(ty, 0));
                } while (T0 == ',' && (next(), true));
        }

        /* Hack to allow comma-separated tag declarations */
        if (tag && T0 == ',') {
                Stmt *tags = mkstmt(ty);
                tags->type = STATEMENT_MULTI;
                vec_init(tags->statements);
                avP(tags->statements, s);
                while (T0 == ',') {
                        next();
                        expect(TOKEN_IDENTIFIER);
                        avP(tags->statements, mktagdef(ty, tok()->identifier));
                        next();
                }
                s = tags;
        }

        if (tag && T0 == ';') {
                next();
        } else {
                consume('{');
                while (T0 != '}') {
                        parse_sync_lex(ty);

                        char const *doc = NULL;
                        lex_keep_comments(ty, true);
                        if (T0 == TOKEN_COMMENT) {
                                doc = tok()->comment;
                                next();
                        }
                        lex_keep_comments(ty, false);

                        /*
                         * Lol.
                         */
                        op_fixup(ty, K0 == KEYWORD_STATIC);

                        Expr *decorator_macro = NULL;
                        if (T0 == '@' && T1 == '{') {
                                next();
                                next();
                                decorator_macro = parse_decorator_macro(ty);
                                consume('}');
                        }

                        expression_vector decorators = {0};
                        if (T0 == TOKEN_AT) {
                                decorators = parse_decorators(ty);
                        }

                        bool _static = try_consume(KEYWORD_STATIC);

                        // ================/ :) /===
                        setctx(LEX_NAME);
                        char *name = tok()->identifier;
                        Location start = tok()->start;
                        next();
                        setctx(LEX_PREFIX);
                        // =========================

                        if (name == NULL) {
                                die(
                                        "%s\n%s\n%s\n",
                                        token_show(ty, token(-1)),
                                        token_show(ty, token(0)),
                                        token_show(ty, token(1))
                                );
                        }

                        Expr *meth;
                        if (
                                (T0 == ':')
                             || (T0 == '=' && tok()->start.s[-1] == ' ')
                        ) {
                                Expr *field = mkid(name);
                                if (T0 == ':') {
                                        next();
                                        SAVE_NE(true);
                                        field->constraint = parse_type(ty, 1);
                                        LOAD_NE();
                                }
                                if (T0 == TOKEN_EQ) {
                                        field = infix_eq(ty, field);
                                }
                                if (
                                        (field->type != EXPRESSION_IDENTIFIER)
                                     && (field->type != EXPRESSION_EQ)
                                ) {
                                        EStart = field->start;
                                        EEnd = field->end;
                                        die("expected a field declarator");
                                }
                                avP(s->tag.fields, field);
                                try_consume(';');
                        } else {
                                bool setter = try_consume('=');
                                bool star   = try_consume('*');
                                bool getter = (T0 == TOKEN_ARROW) || (T0 == '{');

                                if (getter) {
                                        unconsume(')');
                                        unconsume('(');
                                }

                                if (star) {
                                        unconsume('*');
                                }

                                meth = parse_method(
                                        ty,
                                        start,
                                        decorator_macro,
                                        doc,
                                        decorators
                                );

                                meth->name = name;

                                if      (_static) { avP(s->tag.statics, meth); }
                                else if (getter)  { avP(s->tag.getters, meth); }
                                else if (setter)  { avP(s->tag.setters, meth); }
                                else              { avP(s->tag.methods, meth); }

                                if (
                                        !(getter | setter | _static)
                                     && (strcmp(name, "init") == 0)
                                ) {
                                        init = *vvL(s->tag.methods);
                                }
                        }
                }
                setctx(LEX_PREFIX);
                consume('}');
        }

        if (vN(init_params) > 0) {
                if (init == NULL) {
                        init = mkfunc(ty);
                        init->name = "init";
                        init->body = mkstmt(ty);
                        init->body->type = STATEMENT_BLOCK;
                        avP(s->tag.methods, init);
                }

                if (init->body->type != STATEMENT_BLOCK) {
                        EStart = init->start;
                        EEnd = init->end;
                        die("non-block init() body with implicit classs parameters");
                }

                for (int i = 0; i < vN(init_params); ++i) {
                        FuncParam *param = v_(init_params, i);

                        avI(init->params,      param->name,       i);
                        avI(init->constraints, param->constraint, i);
                        avI(init->dflts,       param->dflt,       i);

                        Expr *member = mkid(param->name);

                        Expr *assignment = mkxpr(EQ);
                        assignment->target = mkxpr(MEMBER_ACCESS);
                        assignment->target->object = mkid("self");
                        assignment->target->member = member;
                        assignment->value = member;

                        Stmt *stmt = mkstmt(ty);
                        stmt->type = STATEMENT_EXPRESSION;
                        stmt->expression = assignment;

                        avI(init->body->statements, stmt, i);
                }
        }

        s->end = TEnd;

        return s;
}

inline static void
next_name(Ty *ty, StringVector *names)
{
        expect(TOKEN_IDENTIFIER);

        if (tok()->module != NULL) {
                avP(*names, tok()->module);
        }

        avP(*names, tok()->identifier);

        next();
}

inline static bool
have_typedef(Ty *ty)
{
        return T0 == TOKEN_IDENTIFIER
            && (
                        T1 == '='
                     || T1 == '['
               );
}

static Stmt *
parse_use(Ty *ty)
{
        Stmt *stmt = mkstmt(ty);
        stmt->type = STATEMENT_USE;

        next();

        if (have_typedef(ty)) {
                stmt->type = STATEMENT_TYPE_DEFINITION;
                stmt->class.name = tok()->identifier;
                next();
                if (T0 == '[') {
                        parse_type_params(ty, &stmt->class.type_params);
                }
                consume('=');
                stmt->class.type = parse_type(ty, -1);
                stmt->end = TEnd;
                return stmt;
        }

        do next_name(ty, &stmt->use.name);
        while (T0 == '.' && (next(), 1));

        if (T0 == '(') {
                next();

                do next_name(ty, &stmt->use.names);
                while (T0 == ',' && (next(), 1));

                consume(')');
        }

        stmt->end = TEnd;

        return stmt;
}

static Stmt *
parse_set_type(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_SET_TYPE;

        consume_keyword(KEYWORD_SET_TYPE);

        s->target = prefix_identifier(ty);
        s->value = parse_type(ty, 0);

        return s;
}

static Stmt *
parse_catch(Ty *ty)
{
        Stmt *try = mkstmt(ty);
        try->type = STATEMENT_TRY;

        while (have_keyword(KEYWORD_CATCH)) {
                next();
                if (T0 == '{') {
                        next();
                        while (T0 != '}') {
                                SAVE_NE(true);
                                avP(try->try.patterns, parse_expr(ty, 0));
                                LOAD_NE();
                                consume(TOKEN_FAT_ARROW);
                                avP(try->try.handlers, parse_statement(ty, -1));
                                try_consume(',');
                        }
                        next();
                } else {
                        SAVE_NE(true);
                        avP(try->try.patterns, parse_expr(ty, 0));
                        LOAD_NE();
                        avP(try->try.handlers, parse_statement(ty, -1));
                }
        }

        Stmt *body = parse_statement(ty, 0);
        Stmt *multi = NULL;

        while (get_prefix_parser(ty) != NULL) {
                if (multi == NULL) {
                        multi = mkstmt(ty);
                        multi->type = STATEMENT_MULTI;
                        avP(multi->statements, body);
                }
                avP(multi->statements, parse_statement(ty, 0));
        }

        try->try.s = (multi != NULL) ? multi : body;
        try->end = TEnd;

        return try;
}

static Stmt *
parse_try(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_TRY;

        consume_keyword(KEYWORD_TRY);

        if (T0 != '{') {
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

                if (have_keywords(KEYWORD_OR, KEYWORD_ELSE)) {
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

        s->end = TEnd;

        return s;
}

static Stmt *
parse_import(Ty *ty)
{
        Stmt *s = mkstmt(ty);
        s->type = STATEMENT_IMPORT;

        s->import.pub = have_keyword(KEYWORD_PUB) && (next(), true);

        consume_keyword(KEYWORD_IMPORT);

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

        while (T0 == '.') {
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

        if (T0 == TOKEN_IDENTIFIER && strcmp(tok()->identifier, "hiding") == 0) {
                next();
                s->import.hiding = true;
        } else {
                s->import.hiding = false;
        }

        vec_init(s->import.identifiers);
        vec_init(s->import.aliases);

        if (T0 == '(') {
                next();
                if (T0 == TOKEN_DOT_DOT) {
                        next();
                        avP(s->import.identifiers, "..");
                        avP(s->import.aliases, "..");
                } else while (T0 == TOKEN_IDENTIFIER) {
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
                        if (T0 == ',')
                                next();
                        else
                                expect(')');
                }
                consume(')');
        }

        s->end = TEnd;

        consume(TOKEN_NEWLINE);

        return s;
}

static Stmt *
_parse_statement(Ty *ty, int prec)
{
        Stmt *s;

        setctx(LEX_PREFIX);

        switch (T0) {
        case TOKEN_AT:
                if (T1 == '[')
                        return parse_function_definition(ty);
                else
                        goto Expression;

        case '{':            return parse_block(ty);
        case ';':            return parse_null_statement(ty);
        case TOKEN_KEYWORD:  goto Keyword;
        default:             goto Expression;
        }

Keyword:

        switch (K0) {
        case KEYWORD_CLASS:    return parse_class_definition(ty);
        case KEYWORD_TAG:      return parse_class_definition(ty);
        case KEYWORD_TRAIT:    return parse_class_definition(ty);
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
        case KEYWORD_CONST:    return parse_let_definition(ty);
        case KEYWORD_BREAK:    return parse_break_statement(ty);
        case KEYWORD_CONTINUE: return parse_continue_statement(ty);
        case KEYWORD_TRY:      return parse_try(ty);
        case KEYWORD_CATCH:    return parse_catch(ty);
        case KEYWORD_SET_TYPE: return parse_set_type(ty);

        case KEYWORD_USE:
                s = parse_use(ty);
                if (s->type == STATEMENT_USE) {
                        CompilerDoUse(ty, s, NULL);
                }
                return s;

        default:
                goto Expression;
        }

Expression:

        s = mkstmt(ty);
        s->type = STATEMENT_EXPRESSION;
        s->expression = parse_expr(ty, prec);
        s->end = s->expression->end;

        if (s->expression->type == EXPRESSION_STATEMENT) {
                s = s->expression->statement;
        }

        if (T0 == ';') {
                consume(';');
        }

        return s;
}

static Stmt *
parse_statement(Ty *ty, int prec)
{
        //if (AllowErrors && CatchError()) {
        //        next();
        //        return &NullStatement;
        //}

        Stmt *stmt = _parse_statement(ty, prec);

        //if (AllowErrors) {
        //        vvX(SavePoints);
        //}

        return stmt;
}

static void
SetNamespace(Stmt *s, Namespace *ns)
{
        s->ns = ns;

        if (
                s->type == STATEMENT_EXPRESSION
             && s->expression->type == EXPRESSION_STATEMENT
        ) {
                SetNamespace(s->expression->statement, ns);
        } else if (s->type == STATEMENT_MULTI) {
                for (int i = 0; i < vN(s->statements); ++i) {
                        SetNamespace(v__(s->statements, i), ns);
                }
        }
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
                IntroduceDefinitions(ty, s);
                break;

        case STATEMENT_OPERATOR_DEFINITION:
                s->doc = doc;
                s->value->doc = doc;
                define_operator(ty, NULL, s);
                break;

        case STATEMENT_CLASS_DEFINITION:
                s->class.doc = doc;
                define_class(ty, s);
                break;

        case STATEMENT_TAG_DEFINITION:
                s->tag.doc = doc;
                define_tag(ty, s);
                break;

        case STATEMENT_TYPE_DEFINITION:
                s->class.doc = doc;
                define_type(ty, s, NULL);
                break;

        case STATEMENT_SET_TYPE:
                compiler_set_type_of(ty, s);
                break;

        case STATEMENT_MULTI:
                for (int i = 0; i < s->statements.count; ++i) {
                        define_top(ty, s->statements.items[i], doc);
                }
                break;

        case STATEMENT_DEFINITION:
                s->doc = doc;
        case STATEMENT_IF:
                IntroduceDefinitions(ty, s);
                break;

        case STATEMENT_EXPRESSION:
                if (s->expression->type == EXPRESSION_STATEMENT) {
                        define_top(ty, s->expression->statement, doc);
                }
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
tokenize(Ty *ty, char const *source, TokenVector *tokens_out)
{
        lex_save(ty, &CtxCheckpoint);
        ParserState save = state;

        lex_init(ty, "(tokenize)", source);
        lex_keep_comments(ty, true);

        vec_init(tokens);

        while (T0 != TOKEN_END && T0 != TOKEN_ERROR) {
                while (get_prefix_parser(ty) != NULL) {
                        next();
                }

                setctx(LEX_INFIX);

                next();
        }

        while (vN(tokens) > 0 && vvL(tokens)->type == TOKEN_END) {
                vvX(tokens);
        }

        *tokens_out = tokens;

        state = save;
        lex_restore(ty, &CtxCheckpoint);

        return true;
}

static bool
ImportModule(Ty *ty, Stmt *import)
{
        lex_save(ty, &CtxCheckpoint);
        ParserState save = state;

        bool ok = compiler_import_module(ty, import);

        state = save;
        lex_restore(ty, &CtxCheckpoint);

        setctx(LEX_INFIX);
        setctx(LEX_PREFIX);

        return ok;
}

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
        lex_save(ty, &CtxCheckpoint);

        ParserState save = state;
        m0(state);

        volatile statement_vector program = {0};

        lex_init(ty, file, source);
        lex_keep_comments(ty, true);

        setctx(LEX_PREFIX);

        if (setjmp(JB) != 0) {
        Error:
                avP(program, NULL);

                *err_loc = tok()->start;
                *prog_out = program.items;

                if (tok_out != NULL) {
                        *tok_out = tokens;
                }

                state = save;

                return false;
        }

        while (T0 == TOKEN_NEWLINE) {
                next();
        }

        while (
                have_keywords(KEYWORD_PUB, KEYWORD_IMPORT)
             || have_keyword(KEYWORD_IMPORT)
             || T0 == TOKEN_COMMENT
        ) {
                if (T0 == TOKEN_COMMENT) {
                        next();
                } else {
                        Stmt *import = parse_import(ty);
                        if (!ImportModule(ty, import)) {
                                goto Error;
                        }
                }
        }

        while (TokenIndex > 0 && token(-1)->type == TOKEN_COMMENT) {
                TokenIndex -= 1;
        }

        while (T0 != TOKEN_END) {
                char const *doc = NULL;

                while (
                        have_keyword(KEYWORD_NAMESPACE)
                     || have_keywords(KEYWORD_PUB, KEYWORD_NAMESPACE)
                ) {
                        lex_need_nl(ty, true);

                        bool pub = have_keyword(KEYWORD_PUB) && (next(), true);

                        next();

                        expect(TOKEN_IDENTIFIER);
                        Namespace *ns = PushNS(ty, tok()->identifier, pub);
                        next();

                        while (T0 == '.') {
                                next();
                                expect(TOKEN_IDENTIFIER);
                                PushNS(ty, tok()->identifier, true);
                                CurrentNamespace->braced = false;
                                next();
                        }

                        if (T0 == TOKEN_NEWLINE) {
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
                lex_need_nl(ty, false);

                while (T0 == TOKEN_COMMENT) {
                        doc = tok()->comment;
                        next();
                }

                if (AllowErrors) {
                        for (bool stop = false; !stop;) switch (T0) {
                        case ']':
                        case '}':
                        case ')':
                                next();
                                break;
                        default:
                                stop = true;

                        }
                }

                if (T0 == TOKEN_END) {
                        break;
                }

                bool pub = have_keyword(KEYWORD_PUB);

                if (pub) {
                        next();
                        if (!have_keyword(KEYWORD_FUNCTION) &&
                            !have_keyword(KEYWORD_MACRO) &&
                            !have_keyword(KEYWORD_CLASS) &&
                            !have_keyword(KEYWORD_USE) &&
                            !have_keyword(KEYWORD_CONST) &&
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
                while (
                        s->type == STATEMENT_EXPRESSION
                     && s->expression->type == EXPRESSION_STATEMENT
                ) {
                        s = s->expression->statement;
                }

                s->end = TEnd;

                if (s->type != STATEMENT_MACRO_DEFINITION) {
                        avP(program, s);
                }

                if (pub) switch (s->type) {
                case STATEMENT_DEFINITION:
                case STATEMENT_FUNCTION_DEFINITION:
                case STATEMENT_MACRO_DEFINITION:
                case STATEMENT_FUN_MACRO_DEFINITION:
                case STATEMENT_OPERATOR_DEFINITION:
                        s->pub = true;
                        break;
                case STATEMENT_TAG_DEFINITION:
                case STATEMENT_CLASS_DEFINITION:
                case STATEMENT_TYPE_DEFINITION:
                        s->class.pub = true;
                        break;
                default:
                        die("`pub` applied to unexpected statement: %s", ExpressionTypeName((Expr *)s));
                }

                SetNamespace(s, CurrentNamespace);

                define_top(ty, s, doc);

#ifdef TY_DEBUG_NAMES
                pns(s->ns, true);
#endif

                while (T0 == '}' && CurrentNamespace != NULL) {
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
        *prog_out = vv(program);

        if (tok_out != NULL) {
                *tok_out = tokens;
        }

        state = save;

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
                vN(tokens) = TokenIndex;
                avP(tokens, ((struct token) {
                        .ctx = LCTX,
                        .type = TOKEN_EXPRESSION,
                        .start = lex_pos(ty),
                        .end = lex_pos(ty)
                }));
                next();
        } else {
                Token *prev = token(-1);
                if (!prev->pp) {
                        vN(tokens) = TokenIndex;
                        lex_rewind(ty, &prev->end);
                }
        }

        Token *t = token(i);

        lex_keep_comments(ty, keep_comments);

        return *t;
}

void
parse_next(Ty *ty)
{
        next();
}

struct value
parse_get_type(Ty *ty, int prec, bool resolve, bool want_raw)
{
        int save = TokenIndex;

        SAVE_JB;

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(ty, false);

        Value v;
        Expr *e;

        if (setjmp(JB) != 0) {
                v = NIL;
                seek(ty, save);
        } else {
                e = parse_type(ty, prec);
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

        RESTORE_JB;

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
parse_get_expr(Ty *ty, int prec, bool resolve, bool want_raw)
{
        int save = TokenIndex;

        SAVE_JB;

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(ty, false);

        Value v;
        Expr *e;

        if (setjmp(JB) != 0) {
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

        RESTORE_JB;

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

        SAVE_JB;

        SAVE_NI(false);
        SAVE_NE(false);

        bool keep_comments = lex_keep_comments(ty, false);

        struct value v;

        if (setjmp(JB) != 0) {
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

        RESTORE_JB;

        lex_keep_comments(ty, keep_comments);

        return v;
}

static Value
pp_eval(Ty *ty, Expr *expr)
{
        lex_save(ty, &CtxCheckpoint);
        ParserState save = state;

        Value v = compiler_eval(ty, expr);

        state = save;
        lex_restore(ty, &CtxCheckpoint);

        return v;
}

static void
pp_while(Ty *ty)
{
}

static void
pp_if(Ty *ty)
{
        vec(int) starts   = {0};
        vec(int) ends     = {0};
        vec(Expr *) conds = {0};

        int very_start = TokenIndex;

        Token it = *tokenx(1);

        PLOG("%sPP_IF()%s: BEGIN", TERM(96;1), TERM(0));

        lex_in_pp(ty, true);

        for (;;) {
                if (tokenx(0)->type == TOKEN_END) {
                        EStart = it.start;
                        EEnd = it.end;
                        die("unterminated conditional directive");
                }

                if (tokenx(0)->type == TOKEN_ERROR) {
                        EStart = it.start;
                        EEnd = it.end;
                        die(NULL);
                }

                if (tokenx(0)->type == '"') {
                        skip_ss(ty);
                        continue;
                }

                if (tokenx(0)->type != TOKEN_DIRECTIVE) {
                        nextx();
                        continue;
                }

                if (conds.count > 0) {
                        xvP(ends, TokenIndex);
                }

                nextx();

                if (tokenx(0)->type == ']') {
                        nextx();
                        consume('\n');
                        break;
                }

                switch (K0) {
                case KEYWORD_ELSE:
                        next();

                        if (K0 == KEYWORD_IF) {
                                next();
                        }

                        if (T0 != '\n') {
                                xvP(conds, parse_expr(ty, 0));
                        } else {
                                xvP(conds, NULL);
                        }

                        consume('\n');

                        xvP(starts, TokenIndex);

                        break;
                case KEYWORD_IF:
                        next();

                        xvP(conds, parse_expr(ty, 0));

                        consume('\n');

                        xvP(starts, TokenIndex);

                        break;
                default:
                        die("encountered invalid directive while parsing conditional");
                }
        }

        int very_end = TokenIndex;

        int start = -1;
        int end = -1;

        Value val;
        for (int i = 0; i < conds.count; ++i) {
                if (
                        (*v_(conds, i) == NULL)
                     || ((val = pp_eval(ty, *v_(conds, i))), 0)
                     || value_truthy(ty, &val)
                ) {
                        start = *v_(starts, i);
                        end = *v_(ends, i);
                        break;
                }
        }

        PLOG("%sPP_IF()%s: END", TERM(96;1), TERM(0));
        for (int i = very_start; i < very_end; ++i) {
                if (i < start || i >= end) {
                        v_(tokens, i)->ctx = LEX_HIDDEN;
                }
                v_(tokens, i)->pp = true;
                PLOG(
                        "    %s[%5d]%s  (%s)",
                        TERM(95;1),
                        i,
                        TERM(0),
                        token_show(ty, v_(tokens, i))
                );
        }

        lex_in_pp(ty, false);

        xvF(conds);
        xvF(starts);
        xvF(ends);
}

/* vim: set sts=8 sw=8 expandtab: */
