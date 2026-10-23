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
#include "xd.h"
#include "value.h"
#include "vec.h"
#include "vm.h"
#include "diag.h"
#include "syntax.h"

#define BINARY_OPERATOR(name, t, prec, right_assoc)                          \
        static Expr *                                                        \
        infix_ ## name(Ty *ty, Expr *left)                                   \
        {                                                                    \
                Expr *e = mkxpr(t);                                          \
                next();                                                      \
                xF(e, left) = left;                                          \
                xF(e, right) = parse_expr(ty, prec - (right_assoc ? 1 : 0)); \
                e->start = left->start;                                      \
                e->end = token(-1)->end;                                     \
                return e;                                                    \
        }                                                                    \

#define BINARY_LVALUE_OPERATOR(name, t, prec, right_assoc)                   \
        static Expr *                                                        \
        infix_ ## name(Ty *ty, Expr *left)                                   \
        {                                                                    \
                Expr *e = mkxpr(t);                                          \
                consume(TOKEN_ ## t);                                        \
                xF(e, target) = assignment_lvalue(ty, left);                 \
                xF(e, value) = parse_expr(ty, prec - (right_assoc ? 1 : 0)); \
                e->start = xF(e, target)->start;                             \
                e->end = xF(e, value)->end;                                  \
                return e;                                                    \
        }                                                                    \

#define PREFIX_OPERATOR(name, token, prec)                                 \
        static Expr *                                                      \
        prefix_ ## name(Ty *ty)                                            \
        {                                                                  \
                Expr *e = mkxpr(PREFIX_ ## token);                         \
                consume(TOKEN_ ## token);                                  \
                xF(e, operand) = parse_expr(ty, prec);                     \
                e->end = xF(e, operand)->end;                              \
                return e;                                                  \
        }                                                                  \

#define PREFIX_LVALUE_OPERATOR(name, token, prec)                             \
        static Expr *                                                         \
        prefix_ ## name(Ty *ty)                                               \
        {                                                                     \
                Expr *e = mkxpr(PREFIX_ ## token);                            \
                consume(TOKEN_ ## token);                                     \
                xF(e, operand) = assignment_lvalue(ty, parse_expr(ty, prec)); \
                e->end = TEnd;                                                \
                return e;                                                     \
        }                                                                     \

#define T0 (token(0)->type)
#define T1 (token(1)->type)
#define T2 (token(2)->type)
#define T3 (token(3)->type)

#define K0 ((T0 == TOKEN_KEYWORD) ? token(0)->keyword : -1)
#define K1 ((T1 == TOKEN_KEYWORD) ? token(1)->keyword : -1)
#define K2 ((T2 == TOKEN_KEYWORD) ? token(2)->keyword : -1)
#define K3 ((T3 == TOKEN_KEYWORD) ? token(3)->keyword : -1)
#define KW(i) ((token(i)->type == TOKEN_KEYWORD) ? token(i)->keyword : -1)

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

#define consume_n_1(t) do {                              \
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
        (consume)(ty, t);                                \
} while (0)

#define consume_n_2(t, tt) do {                          \
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
        (consume_tagged)(ty, t, tt);                     \
} while (0)

#define consume_kw(t) (                                     \
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
        ((consume_keyword)(ty, (KEYWORD_##t))),             \
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
#define consume_n_1(t)     ((consume)(ty, (t)))
#define consume_n_2(t, tt) ((consume_tagged)(ty, (t), (tt)))

#define               next()                           ((next)(ty))
#define        consume_kw(t) ((consume_keyword)(ty, (KEYWORD_##t)))
#define            expect(t)                    ((expect)(ty, (t)))
#define          setctx(ctx)                  ((setctx)(ty, (ctx)))
#define PLOGX(...) ((void)0)
#define  PLOG(...) ((void)0)
#define PLOGC(...) ((void)0)
#endif

#define try_consume_n_1(t)     ((try_consume)(ty, (t)))
#define try_consume_n_2(t, tt) ((try_consume_tagged)(ty, (t), (tt)))
#define try_consume(...)       VA_SELECT(try_consume_n, __VA_ARGS__)

#define                 tok()                                  ((tok)(ty))
#define              token(i)                           ((token)(ty, (i)))
#define               skip(n)                            ((skip)(ty, (n)))
#define            have_kw(k)                 ((have_kw)(ty, KEYWORD_##k))
#define      have_kws(k0, k1) ((have_kws)(ty, KEYWORD_##k0, KEYWORD_##k1))
#define          unconsume(t)                       ((unconsume)(ty, (t)))
#define    expect_one_of(...)       ((expect_one_of)(ty, __VA_ARGS__, -1))
#define          consume(...)            VA_SELECT(consume_n, __VA_ARGS__)

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

typedef struct {
        Expr const *call;
        Expr *module;
        Expr *text;
        StringVector names;
} SynLiteral;

typedef struct ParserState {
        TokenVector tokens;
        usize TokenBase;
        int TokenIndex;

        int depth;

        vec(LexState) stack;

        LexState CtxCheckpoint;
        LexContext lctx;
        bool comments;

        Namespace *CurrentNamespace;

        Expr *CurrentTemplate;
        Expr *last;

        Location EEnd;
        Location EStart;
        Location TEnd;

        Module *module;

        char const *filename;

        bool NoEquals;
        bool NoConstraint;
        bool NoIn;
        bool NoAndOr;
        bool InList;
        bool NoPipe;
        bool NoLG;
        bool TypeContext;
        bool InField;

        int ForParen;
        bool ForInit;
        Expr *ForInitExpr;

        vec(SynLiteral) SynLiterals;
} ParserState;

static ParserState state;

enum {
        TOKEN_BUFFER_SIZE = 50000
};

static TokenVector TokenBuffer;

struct table uops;
struct table uopcs;

static Expr BlankID = {
        .type = EXPRESSION_IDENTIFIER
};

static Expr WildCard = {
        .type = EXPRESSION_IDENTIFIER
};

static Stmt NullStatement = {
        .type = STATEMENT_NULL
};

static Expr NullExpr = {
        .type = EXPRESSION_STATEMENT
};

#define CtxCheckpoint     (state.CtxCheckpoint)
#define CurrentNamespace  (state.CurrentNamespace)
#define CurrentTemplate   (state.CurrentTemplate)
#define TEnd              (state.TEnd)
#define EEnd              (state.EEnd)
#define EStart            (state.EStart)
#define FileName          (state.filename)
#define LCTX              (state.lctx)
#define NoAndOr           (state.NoAndOr)
#define InList            (state.InList)
#define NoConstraint      (state.NoConstraint)
#define NoEquals          (state.NoEquals)
#define NoIn              (state.NoIn)
#define NoPipe            (state.NoPipe)
#define NoLG              (state.NoLG)
#define ParseDepth        (state.depth)
#define TokenIndex        (state.TokenIndex)
#define TypeContext       (state.TypeContext)
#define InField           (state.InField)
#define ForParen          (state.ForParen)
#define ForInit           (state.ForInit)
#define ForInitExpr       (state.ForInitExpr)
#define LValueContext     (state.LValueContext)
#define TOKENS            (state.tokens)
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
#define SAVE_FD(b) bool FDSave = InField; InField = (b);
#define SAVE_LC(b) 0 // bool LCSave = LValueContext; LValueContext = (b);

#define LOAD_NE() NoEquals = NESave;
#define LOAD_NC() NoConstraint = NCSave;
#define LOAD_NI() NoIn = NISave;
#define LOAD_NP() NoPipe = NPSave;
#define LOAD_NA() NoAndOr = NASave;
#define LOAD_TC() TypeContext = TCSave;
#define LOAD_FD() InField = FDSave;
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
parse_match_cond(Ty *ty, bool expr);

#define have_match_cond(ty) (have_kws(MATCH, IF) || have_kws(MATCH, WHILE))

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
parse_condparts(Ty *ty, bool *neg);

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

inline static Token *
(tok)(Ty *ty);

inline static Token *
(token)(Ty *ty, int i);

Expr *
mkcall(Ty *ty, Expr *func);

static Expr *
mkpartial(Ty *ty, Expr *sugared);

static void
record_extra(Ty *ty, char const *kind, char const *form, Location start, Location end);

static void
record_sugar(Ty *ty, char const *form, Location start, Location end);

#define gensym() ((gensym)(ty))
char *
(gensym)(Ty *ty)
{
        static u64 sym = 0;
        return (char *)ifmt("#%u", sym++);
}

inline static Expr *
mkexpr(Ty *ty)
{
        Expr *e = AstNewFull(0);
        e->arena = GetArenaAlloc(ty);
        e->mod = CompilerCurrentModule(ty);
        e->start = tok()->start;
        e->end = tok()->end;
        return e;
}

#define SYNTH(x, at) ((x)->start = (x)->end = (at), (x)->synth = true)
#define SYNTHETIC(x) ((x)->synth = true)

#define mkxpr(t) (mkxpr)(ty, EXPRESSION_##t)
inline static Expr *
(mkxpr)(Ty *ty, int type)
{
        Expr *e = AstNew(type);
        e->arena = GetArenaAlloc(ty);
        e->mod = CompilerCurrentModule(ty);
        e->start = tok()->start;
        e->end = tok()->end;
        return e;
}

#define mkid(id) ((mkid)(ty, (id)))
inline static Expr *
(mkid)(Ty *ty, char *name)
{
        Expr *ident = mkxpr(IDENTIFIER);
        xF(ident, identifier) = name;
        return ident;
}

inline static Expr *
mkfunc(Ty *ty)
{
        Expr *f = mkxpr(FUNCTION);

        static volatile int t = -1;

        xF(f, rest)    = -1;
        xF(f, ikwargs) = -1;
        xF(f, class)   = NULL;
        xF(f, ftype)   = FT_NONE;
        xF(f, t)       = ++t;

        return f;
}

inline static Stmt *
mkstmt(Ty *ty)
{
        Stmt *s = AstNewFull(STATEMENT_NULL);
        s->ns = CurrentNamespace;
        s->arena = GetArenaAlloc(ty);
        s->mod = CompilerCurrentModule(ty);
        s->start = tok()->start;
        s->end = tok()->end;
        return s;
}

#define mkstmtx(t) ((mkstmtx)(ty, STATEMENT_##t))
inline static Stmt *
(mkstmtx)(Ty *ty, int type)
{
        Stmt *s = AstNew(type);
        s->ns = CurrentNamespace;
        s->arena = GetArenaAlloc(ty);
        s->mod = CompilerCurrentModule(ty);
        s->start = tok()->start;
        s->end = tok()->end;
        return s;
}

inline static Stmt *
mkret(Ty *ty, Expr *value)
{
        Stmt *s = mkstmtx(RETURN);
        sF(s, ret) = value;
        s->start = value->start;
        s->end = value->end;
        SYNTHETIC(s);
        return s;
}

inline static Stmt *
mkdef(Ty *ty, Expr *lvalue, char *name)
{
        Expr *value = mkxpr(IDENTIFIER);
        xF(value, identifier) = name;
        xF(value, module) = NULL;
        SYNTH(value, lvalue->end);

        Stmt *s = mkstmtx(DEFINITION);
        sF(s, pub) = false;
        sF(s, target) = lvalue;
        sF(s, value) = value;
        s->start = lvalue->start;
        s->end = lvalue->end;
        SYNTHETIC(s);

        return s;
}

#define to_expr(e) ((to_expr)(ty, (Stmt *)(e)))
inline static Expr *
(to_expr)(Ty *ty, Stmt *s)
{
        if (s->type < EXPRESSION_MAX_TYPE) {
                return (Expr *)s;
        }

        Expr *e = mkxpr(STATEMENT);
        e->start = s->start;
        e->end = s->end;
        xF(e, statement) = s;

        return e;
}

#define to_stmt(e) ((to_stmt)(ty, (Expr *)(e)))
inline static Stmt *
(to_stmt)(Ty *ty, Expr *e)
{
        if (e->type >= EXPRESSION_MAX_TYPE) {
                return (Stmt *)e;
        }

        Stmt *s = mkstmtx(EXPRESSION);
        s->start = e->start;
        s->end = e->end;
        sF(s, expression) = e;

        return s;
}

__attribute__((always_inline))
inline static Token *
update(Ty *ty, Token *tok)
{
        return tok;
}

Token *
TokenAt(TokenVector const *ts, Location loc)
{
        usize lo = 0;
        usize hi = vN(*ts);

        if (loc.src == 0) {
                return NULL;
        }

        while (lo < hi) {
                usize mid = lo + (hi - lo) / 2;
                if (v__(*ts, mid).start.byte < loc.byte) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        for (; lo < vN(*ts) && v__(*ts, lo).start.byte == loc.byte; ++lo) {
                if (v__(*ts, lo).start.src == loc.src) {
                        return v_(*ts, lo);
                }
        }

        return NULL;
}

static Token *
tokenxx_slow(Ty *ty, int i)
{
        Token t;

        while (vN(TOKENS) <= i + TokenIndex) {
                t = lex_token(ty, LCTX);

                if (UNLIKELY(t.type == TOKEN_END) && vN(state.stack) > 0) {
                        lex_restore(ty, &vXx(state.stack));
                        continue;
                }

                if (vN(TOKENS) == TokenIndex) {
                        lex_save(ty, &CtxCheckpoint);
                }

                if (vN(TOKENS) > 0 && LocS(vvL(TOKENS)->start) == LocS(t.start)) {
                        *vvL(TOKENS) = t;
                        return vvL(TOKENS);
                }

                PLOG(
                        "%sAdd tokens%s[%d]: %s",
                        TERM(92;),
                        TERM(0),
                        (int)vN(TOKENS),
                        token_showx(ty, &t, "")
                );

                avP(TOKENS, t);
        }

#if 0
        static int64_t last_index = -1;
        static int64_t last_count = -1;

        if (TokenIndex + i != last_index || vN(TOKENS) != last_count) {
                PLOG(
                        "%s[%d]%stokenxx%s(% -2d)%s = %s",
                        TERM(95),
                        TokenIndex + i,
                        TERM(92),
                        TERM(93),
                        i,
                        TERM(0),
                        token_showx(ty, v_(TOKENS, TokenIndex + i), "")
                );
                last_index = TokenIndex + i;
                last_count = vN(TOKENS);
        }
#endif

        return update(ty, v_(TOKENS, TokenIndex + i));
}

__attribute__((always_inline))
inline static Token *
(tokenxx)(Ty *ty, int i)
{
        isize j = (isize)TokenIndex + i;

        if (LIKELY(j >= 0 && j < (isize)vN(TOKENS))) {
                return update(ty, v_(TOKENS, j));
        }

        return tokenxx_slow(ty, i);
}

__attribute__((always_inline))
inline static bool
invisible(Ty *ty, Token *tok)
{
        return (tok->ctx == LEX_HIDDEN);
}

#define tokenx(i) ((tokenx)(ty, (i)))
static Token *
tokenx_slow(Ty *ty, int i)
{
        int n    = abs(i);
        int step = (n == 0) ? 1 : (i / n);

        if (i >= 0) while (invisible(ty, tokenxx(ty, 0))) {
                TokenIndex += 1;
        }

        for (;;) {
                while (
                        (i + TokenIndex >= 0)
                     && invisible(ty, tokenxx(ty, i))
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

__attribute__((always_inline))
inline static Token *
(tokenx)(Ty *ty, int i)
{
        isize j = (isize)TokenIndex + i;

        if (
                LIKELY(j >= 0 && j < (isize)vN(TOKENS))
             && !invisible(ty, v_(TOKENS, j))
             && ((i < 0) || !invisible(ty, v_(TOKENS, TokenIndex)))
        ) {
                return update(ty, v_(TOKENS, j));
        }

        return tokenx_slow(ty, i);
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
        TokenIndex = t - vv(TOKENS);
        TEnd = tokenx(-1)->end;
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

static Token *
token_slow(Ty *ty, int i)
{
        Token *t;

        for (;;) {
                t = tokenx(i);

                if (
                        LIKELY(t->type != TOKEN_DIRECTIVE)
                     || (tokenx(i + 1)->type != TOKEN_KEYWORD)
                     || t->pp
                     || lex_state(ty)->in_pp
                ) {
                        goto End;
                }

                int save = TokenIndex;
                Location end = TEnd;

                switch (tokenx(i + 1)->keyword) {
                case KEYWORD_IF:    skipx(i); pp_if(ty);    break;
                case KEYWORD_WHILE: skipx(i); pp_while(ty); break;
                default:            goto End;
                }

                TokenIndex = save;
                TEnd = end;
        }
End:
        PLOG(
                "%stoken(%s%d=%td%s)%s => (%s)",
                TERM(34;4),
                TERM(93;1),
                i,
                t - v_(TOKENS, 0),
                TERM(34;4),
                TERM(0),
                token_showx(ty, t, "")
        );

        if (i == 0) {
                EStart = t->start;
                EEnd = t->end;
        }

        return t;
}

__attribute__((always_inline))
inline static Token *
(token)(Ty *ty, int i)
{
        Token *t = tokenx(i);

        if (UNLIKELY(t->type == TOKEN_DIRECTIVE)) {
                return token_slow(ty, i);
        }

        if (i == 0) {
                EStart = t->start;
                EEnd   = t->end;
        }

        return t;
}

inline static Token *
(tok)(Ty *ty)
{
        return token(0);
}

inline static void
TagTokenOf(Ty *ty, Expr *e, int tag)
{
        Token *t = TokenAt(&TOKENS, e->start);

        if (t != NULL) {
                t->tag = tag;
        }
}

void
parse_sync_lex(Ty *ty)
{
        Token t;

        if (
                (TokenIndex == 0)
             || (TokenIndex >= vN(TOKENS))
             || (t = *token(-1)).pp
             || v_(TOKENS, TokenIndex - 1)->pp
        ) {
                return;
        }

        PLOG(
                "%sparse_sync_lex()%s:  %spre%s: [%s] | [%s]",
                TERM(34),
                TERM(0),
                TERM(92;1),
                TERM(0),
                token_showx(ty, v_(TOKENS, TokenIndex - 1), ""),
                token_showx(ty, v_(TOKENS, TokenIndex), TERM(93;1))
        );

        vN(TOKENS) = TokenIndex;
        lex_need_nl(ty, t.nl);
        lex_rewind(ty, &t.end);

        PLOG(
                "%sparse_sync_lex()%s: %spost%s: [%s] | [%s]",
                TERM(34),
                TERM(0),
                TERM(91;1),
                TERM(0),
                token_showx(ty, v_(TOKENS, TokenIndex - 1), ""),
                token_showx(ty, v_(TOKENS, TokenIndex), TERM(93;1))
        );
}

inline static bool
ctx_insensitive(Token const *t, int ctx)
{
        if (
                ((ctx != LEX_PREFIX) && (ctx != LEX_INFIX))
             || ((t->ctx != LEX_PREFIX) && (t->ctx != LEX_INFIX))
             || (t->type == TOKEN_END)
             || (t->type == TOKEN_ERROR)
             || (t->type == TOKEN_NEWLINE)
             || (LocS(t->start) == NULL)
        ) {
                return false;
        }

        unsigned char c = *LocS(t->start);

        return !xisdigit(c)
            && !contains("/-#&*!?$'%", c)
            && !(c == '.' && xisdigit(LocS(t->start)[1]));
}

inline static bool
need_nl_before_tok(Ty *ty)
{
        if (TokenIndex == 0) {
                return false;
        }

        Token const *t = v_(TOKENS, TokenIndex - 1);

        return t->nl && (t->type != TOKEN_NEWLINE);
}

inline static void
(setctx)(Ty *ty, int ctx)
{
        if (
                   (LCTX == ctx)
                || (tok()->ctx == LEX_FAKE)
                || tok()->pp
        ) {
                return;
        }

        LCTX = ctx;

        if (vN(TOKENS) == TokenIndex + 1 && ctx_insensitive(tok(), ctx)) {
                Token *t = tok();
                LexState *ls = lex_state(ty);
                t->ctx = ctx;
                lex_rewind(ty, &t->end);
                lex_need_nl(ty, t->nl);
                ls->ctx        = ctx;
                ls->blank_line = false;
                lex_save(ty, &CtxCheckpoint);
                return;
        }

        Location seek = (ctx == LEX_FMT || ctx == LEX_DOC || ctx == LEX_TYX)
                      ? token(-1)->end
                      : tok()->start;

        bool nl = need_nl_before_tok(ty);

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

        while (
                (vN(TOKENS) > TokenIndex)
             && (v_(TOKENS, TokenIndex)->ctx != LEX_FMT)
             && (v_(TOKENS, TokenIndex)->ctx != LEX_DOC)
             // && (v_(tokens, TokenIndex)->ctx != LEX_REGEX)
        ) {
                PLOG("  Pop tokens[%zu]: %s", vN(TOKENS) - 1, token_showx(ty, vvL(TOKENS), ""));
                vN(TOKENS) -= 1;
        }

        while (vN(TOKENS) > 0 && LocS(vvL(TOKENS)->start) == LocS(seek)) {
                PLOG("  Pop tokens[%zu]: %s", vN(TOKENS) - 1, token_showx(ty, vvL(TOKENS), ""));
                vN(TOKENS) -= 1;
        }

        PLOGC('\n');

        // TODO: ???
        if (TokenIndex > vN(TOKENS)) {
                TokenIndex = vN(TOKENS);
        }

        logctx(ty);
}

static void
logctx(Ty *ty)
{
#if 1
        tok();

        int lo = max(0, TokenIndex - 3);
        int hi = vN(TOKENS) - 1;

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
                        token_showx(ty, &TOKENS.items[i], c),
                        c,
                        TERM(0)
                );
        }

        char const *ahead = LocS(lex_pos(ty));

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

static bool
RecoverError(Ty *ty)
{
        Value exc = vm_catch(ty);

        if (vN(ty->sinks) == 0) {
                TySuppress(ty, exc, "parser recovery");
        } else {
                TyDiagRecord(ty, exc, NULL);
        }

        return true;
}

static bool
ProbeFailed(Ty *ty)
{
        if (ClassOf(vm_get(ty, 0)) != CLASS_PARSE_ERROR) {
                vm_rethrow(ty);
        }

        (void)vm_catch(ty);

        return true;
}

#define TryParse()    (!VM_TRY() && ProbeFailed(ty))
#define EndTryParse() (vm_finally(ty))

#define CatchError()   (AllowErrors && !VM_TRY() && RecoverError(ty))
#define EndCatch()     (AllowErrors ? vm_finally(ty) : (void)0)

/*
 * Push a token into the token stream, so that it will be returned by the next call
 * to tok().
 */
inline static void
(unconsume)(Ty *ty, int type)
{
        Token t = {
                .type  = type,
                .start = TEnd,
                .end   = TEnd,
                .ctx   = LEX_FAKE
        };

        PLOG("Inserting tokens[%d] = %s", TokenIndex, token_showx(ty, &t, ""));

        logctx(ty);

        avI(TOKENS, t, TokenIndex);
}

#define putback(t) ((putback)(ty, (t)))
inline static void
(putback)(Ty *ty, Token t)
{
        unconsume(TOKEN_ERROR);
        *tok() = t;
        tok()->ctx = LEX_FAKE;
}

inline static Module *
ParsedModule(Ty *ty)
{
        return (state.module != NULL) ? state.module : CompilerCurrentModule(ty);
}

static Value
ErrorLocation(Ty *ty, Location start, Location end)
{
        Module const *mod = ParsedModule(ty);
        char const *name = (mod->name != NULL) ? mod->name : mod->path;

        GC_STOP();

        Value locs = ARRAY(vA());
        vAp(
                locs.array,
                vTn(
                        "file",   (mod->path == NULL) ? NIL : xSz(mod->path),
                        "module", (name == NULL) ? NIL : vSsz(name),
                        "start",  vTn(
                                "line", INTEGER(LocLine(start) + 1),
                                "col",  INTEGER(LocCol(start) + 1)
                        ),
                        "end",    vTn(
                                "line", INTEGER(LocLine(end) + 1),
                                "col",  INTEGER(LocCol(end) + 1)
                        )
                )
        );

        GC_RESUME();

        return locs;
}

static Location
ClampToLine(Location start, Location end)
{
        if (LocS(end) == NULL || LocS(end) < LocS(start)) {
                return start;
        }

        if (LocSameLine(end, start)) {
                return end;
        }

        Location stop = start;

        while (LocS(stop)[0] != '\0' && LocS(stop)[0] != '\n') {
                stop.byte += 1;
        }

        return stop;
}

static Location
BackOverSpace(Location loc)
{
        while ((LocS(loc)[0] == '\0' || xisspace((u8)LocS(loc)[0])) && LocS(loc)[-1] != '\0') {
                loc.byte -= 1;
        }

        return loc;
}

noreturn static void
SyntaxFailure(Ty *ty, int class, char const *msg, Location start, Location end)
{
        byte_vector text = {0};
        Expr where = {
                .type  = EXPRESSION_NIL,
                .start = start,
                .end   = ClampToLine(start, end),
                .mod   = ParsedModule(ty)
        };

        WriteDiagnostic(
                ty,
                &text,
                class_name(ty, class),
                msg,
                (LocS(start) != NULL) ? &where : NULL,
                NULL,
                NULL,
                3,
                2
        );

        GC_STOP();
        Value locs = ErrorLocation(ty, start, (LocS(end) == NULL) ? start : end);
        Value err = TyNewCompileError(ty, class, msg, locs, vv(text), NIL, NIL);
        GC_RESUME();

        xvF(text);

        vm_throw(ty, &err);
}

noreturn static void
LexError(Ty *ty, Token const *t)
{
        char const *msg = (t->error != NULL) ? t->error : "invalid token";

        SyntaxFailure(ty, CLASS_SYNTAX_ERROR, msg, t->start, t->end);
}

static Token const *
PendingLexError(Ty *ty)
{
        for (int i = TokenIndex; i < vN(TOKENS) && i <= TokenIndex + 1; ++i) {
                Token const *t = v_(TOKENS, i);
                if (t->type == TOKEN_ERROR && t->error != NULL) {
                        return t;
                }
        }

        return NULL;
}

noreturn void
ParseError(Ty *ty, char const *fmt, ...)
{
        Token const *bad = PendingLexError(ty);

        if (bad != NULL || fmt == NULL) {
                LexError(ty, (bad != NULL) ? bad : tokenx(0));
        }

        va_list ap;
        byte_vector msg = {0};

        va_start(ap, fmt);
        vdump(&msg, fmt, ap);
        va_end(ap);

        Location start = EStart;
        Location end   = EEnd;

        if (LocS(start) != NULL && tokenx(0)->type == TOKEN_END) {
                start = BackOverSpace(start);
                end   = start;
        }

        char *text = sclonea(ty, vv(msg));
        xvF(msg);

        SyntaxFailure(ty, CLASS_PARSE_ERROR, text, start, end);
}

#define die(...) ParseError(ty, __VA_ARGS__)
#define die_at(e, ...)                     \
        do {                               \
                EStart = (e)->start;       \
                EEnd   = (e)->end;         \
                die(__VA_ARGS__);          \
        } while (0)

inline static Namespace *
PushNS(Ty *ty, char *id, Token const *src, bool pub)
{
        Namespace *ns = amA(sizeof *ns);
        ns->id     = id;
        ns->src_id = id;
        ns->pub    = pub;
        ns->braced = true;
        ns->next   = CurrentNamespace;
        ns->start  = src->start;

        if (
                (LocS(src->start) != NULL)
             && (LocS(src->end) != NULL)
             && (LocS(src->end) > LocS(src->start))
             && (strcspn(LocS(src->start), " \t\n(){}[]") >= (usize)(LocS(src->end) - LocS(src->start)))
        ) {
                usize n = LocS(src->end) - LocS(src->start);
                char *sid = amA(n + 1);
                memcpy(sid, LocS(src->start), n);
                sid[n] = '\0';
                ns->src_id = sid;
        }

        CompilerEnterNS(ty, ns);

        return (CurrentNamespace = ns);
}

inline static void
PopNS(Ty *ty)
{
        CompilerLeaveNS(ty);

        CurrentNamespace = CurrentNamespace->next;
}

static void
CloseNS(Ty *ty, Location end)
{
        CurrentNamespace->end = end;
        record_extra(ty, "Namespace", NULL, CurrentNamespace->start, end);
        PopNS(ty);
}

static void
SetNamespace(Stmt *s, Namespace *ns)
{
        if (!IsExpr(s)) {
                s->ns = ns;
        }

        switch (s->type) {
        case STATEMENT_EXPRESSION:
                if (sF(s, expression)->type == EXPRESSION_STATEMENT) {
                        SetNamespace(xF(sF(s, expression), statement), ns);
                }
                break;

        case STATEMENT_MULTI:
                for (int i = 0; i < vN(sF(s, statements)); ++i) {
                        SetNamespace(v__(sF(s, statements), i), ns);
                }
                break;

        case EXPRESSION_STATEMENT:
                SetNamespace(xF(((Expr *)s), statement), ns);
                break;
        }
}

inline static bool
(have_kw)(Ty *ty, int kw)
{
        return (K0 == kw);
}

inline static bool
(have_kws)(Ty *ty, int kw1, int kw2)
{
        return (T0 == TOKEN_KEYWORD) && (K0 == kw1)
            && (T1 == TOKEN_KEYWORD) && (K1 == kw2);
}

inline static bool
have_without_nl(Ty *ty, int t)
{
        return (T0 == t || K0 == t)
            && (LocSameLine(tok()->start, TEnd));
}

inline static bool
next_without_nl(Ty *ty, int t)
{
        return (T1 == t || K1 == t)
            && (LocSameLine(token(1)->start, tok()->end));
}

static bool
have_not_in(Ty *ty)
{
        return (K0 == KEYWORD_NOT) && (K1 == KEYWORD_IN);
}

inline static bool
no_rhs(Ty *ty, int i)
{
        return (token(i)->type == ']')
            || (token(i)->type == ')')
            || (token(i)->type == '}');
}

static char const *
found_hint(Ty *ty)
{
        if (
                (T0 == TOKEN_KEYWORD)
             && (TokenIndex > 0)
             && (KW(-1) == KEYWORD_LET || KW(-1) == KEYWORD_FOR || KW(-1) == KEYWORD_CONST)
        ) {
                return afmt("\n\n  hint: `%s` is a keyword, so it can't be used as a name", keyword_show(K0));
        }

        for (int i = 1; i <= 3 && i <= TokenIndex; ++i) {
                Token const *prev = token(-i);

                if (prev->type != TOKEN_IDENTIFIER || prev->identifier == NULL) {
                        continue;
                }

                char const *name = DashedName(ty, prev->identifier);
                usize n = strlen(name);

                if (n < 2) {
                        continue;
                }

                switch (name[n - 1]) {
                case '?':  return afmt("\n\n  hint: `%s` is one name, since `?` can end an identifier; put a space before `?` for a conditional", name);
                case '!':  return afmt("\n\n  hint: `%s` is one name, since `!` can end an identifier; put a space before `!=`", name);
                }
        }

        return "";
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
                "expected %s but found %s%s%s%s",
                token_show_type(ty, type),
                TERM(34),
                token_show(ty, tok()),
                TERM(0),
                found_hint(ty)
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

        adump(&msg, " but found %s%s%s%s", TERM(34), token_show(ty, tok()), TERM(0), found_hint(ty));

        die("%s", v_(msg, 0));
}


static void
expect_keyword(Ty *ty, int type)
{
        if (K0 != type) {
                die(
                        "expected %s but found %s%s%s",
                        token_show(ty, &(Token){ .type = TOKEN_KEYWORD, .keyword = type }),
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

inline static bool
(try_consume_tagged)(Ty *ty, int t, int tt)
{
        return (T0 == t || K0 == t)
             ? ((tok()->tag = tt), next(), true)
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
(consume_tagged)(Ty *ty, int type, int tt)
{
        if (expect(type)) {
                tok()->tag = tt;
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
        if (have_kw(IF)) {
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
        xF(it, identifier) = "it";

        (*iterable) = mkxpr(LIST);
        (*iterable)->type = EXPRESSION_LIST;
        rvP(xF((*iterable), es), it);

        SWAP(Expr *, *target, *iterable);

        SYNTH(it, (*iterable)->start);
        SYNTH((*target), (*iterable)->start);
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
        case TOKEN_DOT_MAYBE:   token(i)->identifier = ".?";   break;
        case TOKEN_WTF:         token(i)->identifier = "??";   break;
        case TOKEN_USER_OP:                                    break;

        case '@':
                if (token(i + 1)->type != '(') {
                        return false;
                }
                token(i)->identifier = "@";
                break;

        case '[':
                if (token(i + 1)->type == ']') {
                        token(i)->identifier = "[]";
                        token(i + 1)->ctx = LEX_HIDDEN;
                } else if (
                        (token(i + 1)->type == ';')
                     && (token(i + 2)->type == ';')
                     && (token(i + 3)->type == ']')
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

inline static char *
clone_span_a(Ty *ty, char const *p, char const *q)
{
        if (p == NULL || q == NULL || q < p) {
                return NULL;
        }

        return clone_slice_a(ty, p, q);
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
                        (m->type != EXPRESSION_FUNCTION_CALL)
                     || (xF(m, function)->type != EXPRESSION_IDENTIFIER)
                )
                // TODO: allow . for module access here
        ) {
                EStart = m->start;
                EEnd = m->end;
                die("expected function-like macro invocation inside @{...}");
        }

        return m;
}


static void
parse_decorators(Ty *ty, ExprVec *decs, ExprVec *macro_decs)
{
        Location start = tok()->start;

        while (try_consume('@')) {
                Expr *f = parse_expr(ty, 0);
                f->start = start;

                if (
                        (f->type != EXPRESSION_FUNCTION_CALL)
                     && (f->type != EXPRESSION_METHOD_CALL)
                ) {
                        Expr *call = mkexpr(ty);
                        call->start = start;
                        call->end = f->end;
                        if (f->type == EXPRESSION_MEMBER_ACCESS) {
                                call->type = EXPRESSION_METHOD_CALL;
                                xF(call, object) = xF(f, object);
                                xF(call, method) = xF(f, member);
                        } else {
                                call->type = EXPRESSION_FUNCTION_CALL;
                                xF(call, function) = f;
                        }
                        f = call;
                }

                Expr *hole = mkxpr(PLACEHOLDER);
                SYNTH(hole, f->end);

                switch (f->type) {
                case EXPRESSION_FUNCTION_CALL:
                        rvI(xF(f, args), hole, 0);
                        rvI(xF(f, fconds), NULL, 0);
                        break;

                case EXPRESSION_METHOD_CALL:
                        rvI(xF(f, method_args), hole, 0);
                        rvI(xF(f, mconds), NULL, 0);
                        break;

                default:
                        UNREACHABLE();
                }

                if (IsMacroInvocation(ty, f)) {
                        svP(*macro_decs, f);
                } else {
                        rvP(*decs, f);
                }

                try_consume(',');
                try_consume(';');

                start = tok()->start;
        }
}

static Expr *
parse_type(Ty *ty, int prec)
{
        Expr *t;

        SAVE_TC(true);
        SAVE_NE(true);
        t = parse_expr(ty, prec);
        LOAD_NE();
        LOAD_TC();

        return t;
}

static void
parse_type_params(Ty *ty, ExprVec *params)
{
        SAVE_NE(true);
        consume('[');
        while (T0 != ']') {
                bool variadic = try_consume('*');
                bool pack     = try_consume(TOKEN_DOT_DOT_DOT);

                Expr *param = prefix_identifier(ty);

                if (variadic) {
                        param->type = EXPRESSION_MATCH_REST;
                } else if (pack) {
                        param->type = EXPRESSION_PACK;
                }

                rvP(*params, param);

                if (T0 != ']') {
                        consume(',');
                }
        }
        next();
        LOAD_NE();
}

static Expr *
parse_member(Ty *ty)
{
        int ctx = LCTX;
        Expr *member;

        setctx(LEX_MEMBER);

        if (AllowErrors && T0 != TOKEN_IDENTIFIER) {
                member = mkid("");
        } else {
                expect(TOKEN_IDENTIFIER);
                member = mkid(tok()->identifier);
                next();
        }

        setctx(ctx);

        return member;
}

static void
parse_comprehension(Ty *ty, Comprehension *comp)
{
        while (try_consume(KEYWORD_FOR)) {
                ComprPart part;

                part.pattern = parse_target_list(ty);

                if (part.pattern->type != EXPRESSION_LIST) {
                        iter_sugar(ty, &part.pattern, &part.iter);
                } else {
                        consume_kw(IN);
                        part.iter = parse_expr(ty, 0);
                }

                part._while = try_consume(KEYWORD_WHILE)
                            ? parse_expr(ty, 0)
                            : NULL;

                part._if = try_consume(KEYWORD_IF)
                         ? parse_condparts(ty, &(bool){false})
                         : (condpart_vector){0};

                part.where = (K0 == KEYWORD_WHERE)
                           ? parse_let_definition(ty)
                           : NULL;

                rvP(*comp, part);
        }
}

/* * * * | prefix parsers | * * * */
static Expr *
prefix_integer(Ty *ty)
{
        expect(TOKEN_INTEGER);

        Expr *e = mkxpr(INTEGER);
        xF(e, integer) = tok()->integer;

        consume(TOKEN_INTEGER);

        return e;
}

static Expr *
prefix_real(Ty *ty)
{
        expect(TOKEN_REAL);

        Expr *e = mkxpr(REAL);
        xF(e, real) = tok()->real;

        consume(TOKEN_REAL);

        return e;
}

static Bytes
astrcat(Ty *ty, Bytes s1, Bytes s2)
{
        usize n1 = s1.length;
        usize n2 = s2.length;
        char *s = amA(n1 + n2 + 1);

        memcpy(s, s1.data, n1);
        memcpy(s + n1, s2.data, n2);
        s[n1 + n2] = '\0';

        return BYTES(s, n1 + n2);
}

static Expr *
merge_strings(Ty *ty, Expr *s1, Expr *s2)
{
        if (s1->type == EXPRESSION_STRING && s2->type == EXPRESSION_STRING) {
                xF(s1, string) = astrcat(ty, xF(s1, string), xF(s2, string));
                return s1;
        }

        if (s2->type == EXPRESSION_STRING) {
                Bytes *last = vvL(xF(s1, strings));
                *last = astrcat(ty, *last, xF(s2, string));
                return s1;
        }

        if (s1->type == EXPRESSION_STRING) {
                Bytes *first = v_(xF(s2, strings), 0);
                *first = astrcat(ty, xF(s1, string), *first);
                return s2;
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
        Bytes *last = vvL(xF(s1, strings));
        *last = astrcat(ty, *last, xF(s2, strings).items[0]);
        rvPv(xF(s1, expressions), xF(s2, expressions));
        rvPv(xF(s1, fmts), xF(s2, fmts));
        rvPv(xF(s1, fmtfs), xF(s2, fmtfs));
        rvPv(xF(s1, widths), xF(s2, widths));
        rvPn(xF(s1, strings), xF(s2, strings).items + 1, xF(s2, strings).count - 1);

        return s1;
}

inline static u32
quote_column(Token const *t)
{
        return (t->type == TOKEN_IDENTIFIER)
             ? LocCol(t->start) + strlen(t->identifier)
             : LocCol(t->start);
}

inline static bool
continues_string(Ty *ty, Location const *first)
{
        Token const *t = tok();

        return (LocSameLine(t->start, TEnd))
            || (quote_column(t) == LocCol(*first));
}

Expr *
extend_string(Ty *ty, Expr *s)
{
        Location first = s->start;
        bool merged = false;

        while (
                (
                        (T0 == TOKEN_STRING)
                     || (T0 == '"')
                     || (
                                (T0 == TOKEN_IDENTIFIER)
                             && IsMacroName(ty, tok()->module, tok()->identifier)
                        )
                )
             && continues_string(ty, &first)
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

                s = merge_strings(ty, s, s2);

                s->start = first;
                s->end = s2->end;
                merged = true;
        }

        if (merged) {
                record_sugar(ty, "string-concat", s->start, s->end);
        }

        return s;
}

static Expr *
prefix_string(Ty *ty)
{
        expect(TOKEN_STRING);

        Expr *e = mkxpr(STRING);
        xF(e, string) = tok()->string;

        consume(TOKEN_STRING);

        return extend_string(ty, e);
}

static Token
ss_next_str(Ty *ty, int quotes)
{
        Token str;
        int ctx = (quotes == 0) ? LEX_XFMT : LEX_FMT;

        if (quotes >= 3) {
                ctx = LEX_DOC;
                lex_state(ty)->quotes = quotes;
        }

        setctx(ctx);

        if (T0 == TOKEN_ERROR) {
                die(NULL);
        }

        if (quotes >= 3) {
                expect(TOKEN_STRING);
        }

        if (T0 != TOKEN_STRING) {
                // TODO: this shouldn't be necessary. we threw away a SS string
                // and were unable to rewind back through preprocessor-generated
                // tokens in order to produce it again
                return (Token) { .type = TOKEN_STRING, .string = z_bytes("") };
        }

        str = *tok();

        next();

        return str;
}

static void
ss_skip_inner(Ty *ty, int quotes)
{
        ss_next_str(ty, quotes);

        while (setctx(LEX_PREFIX), T0 == '{') {
                next();

                parse_expr(ty, 0);

                if (T0 == ':') {
                        next();
                        ss_skip_inner(ty, 0);
                }

                if (T0 == '[') {
                        next();
                        parse_expr(ty, 0);
                        consume(']');
                }

                consume('}');

                ss_next_str(ty, quotes);
        }
}

static void
dedent_string(Ty *ty, Expr *e, TokenVector const *parts)
{
        Location close = tok()->start;
        char const *begin = LocS(v__(*parts, 0).start);
        char const *line = LocS(close);

        if (T0 != '"') {
                die("unterminated docstring starting on line %d", LocLine(v__(*parts, 0).start) + 1);
        }

        while (line > begin && line[-1] != '\n') {
                line -= 1;
        }

        for (char const *p = line; p < LocS(close); ++p) {
                if (!xisspace((u8)*p)) {
                        die("illegal docstring terminator on line %d", LocLine(close) + 1);
                }
        }

        usize indent = LocS(close) - line;
        char const *end = line;
        if (end > begin && end[-1] == '\n') {
                end -= 1;
                if (end > begin && end[-1] == '\r') {
                        end -= 1;
                }
        }

        for (usize i = 0; i < vN(*parts); ++i) {
                Token const *part = v_(*parts, i);
                char const *stop = (i + 1 == vN(*parts)) ? end : LocS(part->end);
                Token str = lex_docstring_part(ty, part->start, stop, indent, i == 0);
                if (str.type == TOKEN_ERROR) {
                        LexError(ty, &str);
                }
                v__(xF(e, strings), i) = str.string;
        }
}

static Expr *
ss_inner(Ty *ty, int quotes)
{
        Expr *e = mkxpr(SPECIAL_STRING);
        TokenVector parts = {0};
        Token str = ss_next_str(ty, quotes);

        rvP(xF(e, strings), str.string);
        if (quotes >= 3) {
                rvP(parts, str);
        }

        while (setctx(LEX_PREFIX), (T0 == '{')) {
                Location start = tok()->start;
                next();

                lex_need_nl(ty, false);

                SAVE_NE(false);
                SAVE_NC(true);
                rvP(xF(e, expressions), parse_expr(ty, 0));
                LOAD_NC();
                LOAD_NE();

                if (try_consume(':')) {
                        Expr *fmt = ss_inner(ty, 0);
                        Bytes *last = vvL(xF(fmt, strings));

                        /*
                         * Strip trailing spaces from the format specifier so
                         * {x:-.2f   } becomes just '-.2f' -- trailing spaces
                         * are used purely to control the width which gets passed
                         * to __fmt__
                         */
                        while (
                                (last->length > 0)
                             && xisspace((u8)last->data[last->length - 1])
                        ) {
                                last->length -= 1;
                        }

                        bool empty = (vN(xF(fmt, strings)) == 1)
                                  && (last->length == 0);

                        rvP(xF(e, fmts), !empty ? fmt : NULL);
                } else {
                        rvP(xF(e, fmts), NULL);
                }

                if (try_consume('[')) {
                        SAVE_NE(false);
                        rvP(xF(e, fmtfs), parse_expr(ty, 0));
                        LOAD_NE();
                        consume(']');
                } else {
                        rvP(xF(e, fmtfs), NULL);
                }

                Location end = tok()->end;
                rvP(xF(e, widths), LocS(end) - LocS(start));

                consume('}');

                str = ss_next_str(ty, quotes);
                rvP(xF(e, strings), str.string);
                if (quotes >= 3) {
                        rvP(parts, str);
                }
        }

        if (quotes >= 3) {
                dedent_string(ty, e, &parts);
        }

        e->end = TEnd;

        return e;
}

static void
skip_ss(Ty *ty)
{
        int quotes = max(tok()->integer, 1);

        for (int i = 0; i < quotes; ++i) {
                consume('"');
        }
        ss_skip_inner(ty, quotes);
        for (int i = 0; i < quotes; ++i) {
                consume('"');
        }
}

static Expr *
prefix_ss(Ty *ty)
{
        Expr *e;
        Location start = tok()->start;
        int quotes = max(tok()->integer, 1);

        for (int i = 0; i < quotes; ++i) {
                consume('"');
        }
        e = ss_inner(ty, quotes);
        for (int i = 0; i < quotes; ++i) {
                consume('"');
        }

        e->start = start;
        e->end = TEnd;

        return extend_string(ty, e);
}

static Bytes
re_next_part(Ty *ty)
{
        Bytes str;

        setctx(LEX_REGEX);

        if (T0 != TOKEN_STRING) {
                return z_bytes("");
        }

        str = tok()->string;

        next();

        return str;
}

static Expr *
re_inner(Ty *ty)
{
        Expr *e = mkxpr(DYNAMIC_REGEX);

        rvP(xF(e, strings), re_next_part(ty));

        while (setctx(LEX_PREFIX), (T0 == '$' && T1 == '{')) {
                next();
                next();

                lex_need_nl(ty, false);

                SAVE_NE(false);
                SAVE_NC(true);
                rvP(xF(e, expressions), parse_expr(ty, 0));
                LOAD_NC();
                LOAD_NE();

                consume('}');

                rvP(xF(e, strings), re_next_part(ty));
        }

        e->end = TEnd;

        setctx(LEX_REGEX);

        return e;
}

static Expr *
prefix_dyn_regex(Ty *ty)
{
        Expr *e;
        Location start = tok()->start;

        consume(TOKEN_DYN_REGEX);
        e = re_inner(ty);

        expect(TOKEN_DYN_REGEX);
        xF(e, re_flags) = tok()->string.data;
        next();

        e->start = start;
        e->end = TEnd;

        return e;
}

static Expr *
prefix_hash(Ty *ty)
{
        Expr *e = mkxpr(PREFIX_HASH);

        consume('#');

        xF(e, operand) = parse_expr(ty, 10);
        e->end = TEnd;

        return e;
}

static Expr *
prefix_slash(Ty *ty)
{
        Location start = tok()->start;

        next();

        Location slash = TEnd;
        Expr *body = parse_expr(ty, 1);

        Expr *nil = mkxpr(NIL);
        nil->start = start;
        nil->end = slash;

        Expr *f = mkcall(ty, nil);
        rvP(xF(f, args), body);
        rvP(xF(f, fconds), NULL);

        f->end = TEnd;
        SYNTHETIC(f);
        SYNTHETIC(nil);

        return mkpartial(ty, f);
}

static Expr *
prefix_dollar(Ty *ty)
{
        if (T1 == '{') {
                return prefix_implicit_lambda(ty);
        }

        Expr *e = mkxpr(MATCH_NOT_NIL);

        consume('$');
        setctx(LEX_INFIX);

        expect(TOKEN_IDENTIFIER);

        xF(e, identifier) = tok()->identifier;
        xF(e, module) = tok()->module;

        if (xF(e, module) != NULL) {
                die_at(e, "not-nil ($<id>) pattern contains unexpected module qualifier");
        }

        consume(TOKEN_IDENTIFIER);

        e->end = TEnd;

        return e;
}

static Expr *
patternize(Ty *ty, Expr *e);

static Expr *
template_pattern(Ty *ty, Expr *template)
{
        usize count = vN(xF(template, template).holes);

        Expr *bindings = mkxpr(ARRAY);
        bindings->start = template->start;
        bindings->end = template->end;

        for (usize i = 0; i < count; ++i) {
                Expr *hole = v__(xF(template, template).holes, i);
                if (hole->type != EXPRESSION_IDENTIFIER || xF(hole, module) != NULL) {
                        EStart = hole->start;
                        EEnd = hole->end;
                        die("holes in a quasiquote pattern must be plain names");
                }
                Expr *binding = mkxpr(IDENTIFIER);
                xF(binding, identifier) = xF(hole, identifier);
                xF(binding, module) = NULL;
                binding->start = hole->start;
                binding->end = hole->end;
                rvP(xF(bindings, elements), binding);
                rvP(xF(bindings, aconds), NULL);
                rvP(xF(bindings, optional), false);
        }

        Expr *fun = mkxpr(IDENTIFIER);
        xF(fun, identifier) = "__ast_match__";
        xF(fun, module) = NULL;
        SYNTH(fun, template->start);

        Value *pointer = amA(sizeof *pointer);
        *pointer = PTR(template);

        Expr *source = mkxpr(VALUE);
        xF(source, v) = pointer;
        SYNTH(source, template->start);

        Expr *n = mkxpr(INTEGER);
        xF(n, integer) = (intmax_t)count;
        SYNTH(n, template->start);

        char *param = gensym();

        Expr *subject = mkxpr(IDENTIFIER);
        xF(subject, identifier) = param;
        xF(subject, module) = NULL;
        SYNTH(subject, template->start);

        Expr *call = mkcall(ty, fun);
        rvP(xF(call, args), source);
        rvP(xF(call, fconds), NULL);
        rvP(xF(call, args), n);
        rvP(xF(call, fconds), NULL);
        rvP(xF(call, args), subject);
        rvP(xF(call, fconds), NULL);
        SYNTH(call, template->start);

        Expr *matcher = mkfunc(ty);
        SYNTH(matcher, template->start);
        rvP(xF(matcher, params), param);
        rvP(xF(matcher, constraints), NULL);
        rvP(xF(matcher, dflts), NULL);
        xF(matcher, body) = to_stmt(call);

        Expr *view = mkxpr(VIEW_PATTERN);
        xF(view, left) = matcher;
        xF(view, right) = patternize(ty, bindings);
        view->start = template->start;
        view->end = template->end;
        SYNTHETIC(view);
        SYNTHETIC(bindings);

        return view;
}



inline static bool
syn_idchar(int c)
{
        return (c & 0x80) || isalnum(c) || (c == '_');
}

static isize
syn_skip_string(Ty *ty, isize i)
{
        int q = lex_look_byte(ty, i);

        if (lex_look_byte(ty, i + 1) == q && lex_look_byte(ty, i + 2) == q) {
                for (i += 3; lex_look_byte(ty, i) != '\0'; ++i) {
                        if (
                                (lex_look_byte(ty, i) == q)
                             && (lex_look_byte(ty, i + 1) == q)
                             && (lex_look_byte(ty, i + 2) == q)
                        ) {
                                return i + 3;
                        }
                }
                return i;
        }

        int braces = 0;

        for (i += 1; lex_look_byte(ty, i) != '\0'; ++i) {
                int c = lex_look_byte(ty, i);
                if (c == '\\') {
                        i += 1;
                } else if (q == '"' && c == '{') {
                        braces += 1;
                } else if (q == '"' && c == '}' && braces > 0) {
                        braces -= 1;
                } else if (braces > 0 && (c == '"' || c == '\'')) {
                        i = syn_skip_string(ty, i) - 1;
                } else if (c == q) {
                        return i + 1;
                }
        }

        return i;
}

static isize
syn_body_length(Ty *ty)
{
        int depth = 0;

        for (isize i = 0;;) {
                int c = lex_look_byte(ty, i);
                int c1 = lex_look_byte(ty, i + 1);
                int c2 = lex_look_byte(ty, i + 2);

                if (c == '\0') {
                        return -1;
                }

                if (c == '$' && c1 == '$' && c2 == '[') {
                        depth += 1;
                        i += 3;
                } else if (c == '$' && c1 == '$' && c2 == ']') {
                        if (depth == 0) {
                                return i;
                        }
                        depth -= 1;
                        i += 3;
                } else if (c == '$' && c1 == '$' && c2 == '<') {
                        for (i += 3; lex_look_byte(ty, i) != '>'; ++i) {
                                if (lex_look_byte(ty, i) == '\0') {
                                        return -1;
                                }
                        }
                        i += 1;
                } else if (c == '"' || c == '\'') {
                        i = syn_skip_string(ty, i);
                } else if (c == '/' && c1 == '/') {
                        while (lex_look_byte(ty, i) != '\n' && lex_look_byte(ty, i) != '\0') {
                                i += 1;
                        }
                } else if (c == '/' && c1 == '*') {
                        for (i += 2; lex_look_byte(ty, i) != '\0'; ++i) {
                                if (
                                        (lex_look_byte(ty, i) == '*')
                                     && (lex_look_byte(ty, i + 1) == '/')
                                ) {
                                        i += 2;
                                        break;
                                }
                        }
                } else {
                        i += 1;
                }
        }
}

static char *
syn_name(Ty *ty, char const *s, usize *n)
{
        byte_vector name = {0};
        usize i = 0;

        while (syn_idchar(s[i]) || (s[i] == '-' && syn_idchar(s[i + 1]) && i > 0)) {
                if (s[i] == '-') {
                        rvP(name, toupper((unsigned char)s[i + 1]));
                        i += 2;
                } else {
                        rvP(name, s[i]);
                        i += 1;
                }
        }

        if (s[i] == '?' || s[i] == '!') {
                rvP(name, s[i]);
                i += 1;
        }

        rvP(name, '\0');
        *n = i;

        return vv(name);
}

static void
syn_add_name(Ty *ty, StringVector *names, char *name)
{
        if (name[0] == '\0' || strcmp(name, "_") == 0) {
                return;
        }

        for (usize i = 0; i < vN(*names); ++i) {
                if (strcmp(v__(*names, i), name) == 0) {
                        return;
                }
        }

        rvP(*names, name);
}

static bool
syn_gap_keyword(char const *name)
{
        static char const *keywords[] = { "_", "nl", "blank", "sp", "any" };

        for (usize i = 0; i < countof(keywords); ++i) {
                if (strcmp(keywords[i], name) == 0) {
                        return true;
                }
        }

        return false;
}

static void
syn_scan_names(Ty *ty, char const *s, StringVector *names)
{
        usize n;

        for (usize i = 0; s[i] != '\0'; ++i) {
                if (s[i] != '$' || s[i + 1] != '$') {
                        continue;
                }

                usize j = i + 2;

                if (s[j] == '(' || s[j] == '<') {
                        bool paren = (s[j] == '(');
                        j += 1;
                        while (s[j] == ' ' || s[j] == '\t') {
                                j += 1;
                        }
                        if (!syn_idchar(s[j])) {
                                continue;
                        }
                        char *name = syn_name(ty, s + j, &n);
                        j += n;
                        while (s[j] == ' ' || s[j] == '\t') {
                                j += 1;
                        }
                        if (paren && s[j] == ':') {
                                syn_add_name(ty, names, name);
                        } else if (
                                !paren
                             && (s[j] == '>' || s[j] == '~')
                             && !syn_gap_keyword(name)
                        ) {
                                syn_add_name(ty, names, name);
                        }
                } else if (syn_idchar(s[j])) {
                        syn_add_name(ty, names, syn_name(ty, s + j, &n));
                }
        }
}

static Expr *
syn_call(Ty *ty, Expr *module, char *method, Expr *text, Location start, Location end)
{
        Expr *call = mkxpr(METHOD_CALL);
        xF(call, object) = module;
        xF(call, method) = mkid(method);
        SYNTH(xF(call, method), start);
        rvP(xF(call, method_args), text);
        rvP(xF(call, mconds), NULL);

        char const *home = (state.module == NULL) ? NULL
                         : (state.module->path != NULL) ? state.module->path
                         : state.module->name;

        if (home != NULL) {
                Expr *where = mkxpr(STRING);
                xF(where, string) = (Bytes) { .data = home, .length = strlen(home) };
                SYNTH(where, start);
                rvP(xF(call, method_args), where);
                rvP(xF(call, mconds), NULL);
        }

        call->start = start;
        call->end = end;
        return call;
}

static Expr *
prefix_syn_literal(Ty *ty)
{
        Location start = tok()->start;

        Expr *module = mkid(tok()->identifier);
        xF(module, module) = tok()->module;
        module->start = start;
        module->end = tok()->end;

        next();
        next();

        parse_sync_lex(ty);

        isize n = syn_body_length(ty);
        if (n < 0) {
                die("unterminated syn$$[ literal");
        }

        Location body = lex_pos(ty);
        byte_vector text = {0};
        char b[128];

        while (vN(text) < (usize)n) {
                if (!lex_next_char(ty, b)) {
                        break;
                }
                rvPn(text, b, strlen(b));
        }

        for (int i = 0; i < 3; ++i) {
                lex_next_char(ty, b);
        }

        Location end = lex_pos(ty);

        rvP(text, '\0');

        Expr *str = mkxpr(STRING);
        xF(str, string) = (Bytes) { .data = vv(text), .length = vN(text) - 1 };
        str->start = body;
        str->end = body;

        SynLiteral lit = {
                .module = module,
                .text   = str
        };

        syn_scan_names(ty, vv(text), &lit.names);

        Expr *call = syn_call(ty, module, "__pattern__", str, start, end);
        lit.call = call;

        if (state.module != NULL) {
                rvP(
                        state.module->macros,
                        ((MacroSpan) {
                                .name  = "$$[",
                                .start = start,
                                .end   = end
                        })
                );
        }

        avP(state.SynLiterals, lit);

        TEnd = end;

        return call;
}

static Expr *
syn_view_pattern(Ty *ty, Expr *e)
{
        for (usize i = 0; i < vN(state.SynLiterals); ++i) {
                SynLiteral const *lit = v_(state.SynLiterals, i);
                if (lit->call != e) {
                        continue;
                }

                Expr *bindings = mkxpr(ARRAY);
                SYNTH(bindings, e->end);

                for (usize j = 0; j < vN(lit->names); ++j) {
                        Expr *id = mkid(v__(lit->names, j));
                        xF(id, module) = NULL;
                        SYNTH(id, e->end);
                        rvP(xF(bindings, elements), id);
                        rvP(xF(bindings, aconds), NULL);
                        rvP(xF(bindings, optional), false);
                }

                Expr *view = mkxpr(VIEW_PATTERN);
                xF(view, left) = syn_call(ty, lit->module, "__matcher__", lit->text, e->start, e->end);
                xF(view, right) = patternize(ty, bindings);
                view->start = e->start;
                view->end = e->end;

                return view;
        }

        return NULL;
}

static void
record_extra(Ty *ty, char const *kind, char const *form, Location start, Location end)
{
        if (
                (state.module == NULL)
             || (start.byte >= end.byte)
             || !HAVE_COMPILER_FLAG(FIDELITY)
        ) {
                return;
        }

        rvP(
                state.module->extras,
                ((SyntaxExtra) {
                        .kind  = kind,
                        .form  = form,
                        .start = start,
                        .end   = end
                })
        );
}

static void
record_embedded(Ty *ty, char const *form, Location start, Location end, void const *node)
{
        usize n = (state.module == NULL) ? 0 : vN(state.module->extras);

        record_extra(ty, "Embedded", form, start, end);

        if (state.module != NULL && vN(state.module->extras) > n) {
                vvL(state.module->extras)->node = node;
        }
}

static void
record_sugar(Ty *ty, char const *form, Location start, Location end)
{
        record_extra(ty, "Sugar", form, start, end);
}

static void
record_macro(Ty *ty, Expr const *e, void const *expansion)
{
        Location end = token(-1)->end;

        if (vN(TOKENS) <= TokenIndex) {
                Location pos = lex_pos(ty);
                if (pos.byte > end.byte) {
                        end = pos;
                }
        }

        if (end.byte > TEnd.byte) {
                TEnd = end;
        }

        if (state.module != NULL) {
                rvP(
                        state.module->macros,
                        ((MacroSpan) {
                                .name      = xF(e, identifier),
                                .start     = e->start,
                                .end       = end,
                                .expansion = expansion
                        })
                );
        }
}

static Expr *
prefix_identifier(Ty *ty)
{
        expect(TOKEN_IDENTIFIER);

        if (
                (T1 == TOKEN_TEMPLATE_BEGIN)
             && (token(1)->start.byte == tok()->end.byte)
             && (CurrentTemplate == NULL)
        ) {
                return prefix_syn_literal(ty);
        }

        int i_id = TokenIndex;
        Expr *e = mkxpr(IDENTIFIER);

        xF(e, identifier) = tok()->identifier;
        xF(e, module) = tok()->module;

        consume(TOKEN_IDENTIFIER);

        if (IsMacro(ty, e)) {
                Expr *expanded;
                v_(TOKENS, i_id)->tag = TT_MACRO;
                if (TY_CATCH_ERROR()) {
                        expanded = mkxpr(ERROR);
                        expanded->start = e->start;
                        expanded->end = TEnd;
                        xF(expanded, message) = afmt(
                                "error during expansion of macro %s",
                                QualifiedName(e)
                        );
                        Value err = TY_CATCH();
                        TyDiagRecord(ty, err, expanded);
                } else {
                        expanded = typarse(
                                ty,
                                e,
                                NULL,
                                &e->start,
                                &token(-1)->end
                        );
                        SetNamespace((Stmt *)expanded, CurrentNamespace);
                        TY_CATCH_END();
                }
                record_macro(ty, e, expanded);
                return expanded;
        }

        if (TypeContext && s_eq(xF(e, identifier), "_")) {
                e->type = EXPRESSION_MATCH_ANY;
                e->end = TEnd;
                return e;
        }

        if (!TypeContext && (xF(e, module) == NULL) && lex_is_operator(xF(e, identifier))) {
                e->type = EXPRESSION_OPERATOR;
                xF(e, op).id = xF(e, identifier);
                e->end = TEnd;
                return e;
        }

        // TODO: maybe get rid of this
        if (!NoConstraint && try_consume(':', TT_PUNCT)) {
                SAVE_NA(true);
                xF(e, constraint) = parse_type(ty, 0);
                LOAD_NA();
        } else {
                xF(e, constraint) = NULL;
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
        xF(e, operand) = parse_expr(ty, 0);
        consume(')');
        e->end = TEnd;
        return e;
}

static Expr *
prefix_defined(Ty *ty)
{
        Expr *e;
        Location start = tok()->start;

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
        rvP(xF(template, template).stmts, to_stmt(parse_expr(ty, 0)));
        template->end = TEnd;
        CurrentTemplate = save;
        return template;
}

static void
parse_function_header(Ty *ty, Expr *e)
{
        char const *volatile proto_start = LocS(tok()->start);
        bool volatile recovered = false;

        SAVE_NE(true);

        if (T0 == '[') {
                parse_type_params(ty, &xF(e, type_params));
        }

        if (CatchError()) {
                recovered = true;
                goto EndOfParams;
        }

        consume('(');

        while (T0 != ')') {
                setctx(LEX_PREFIX);

                bool special = false;
                Location param = tok()->start;

                if (T0 == TOKEN_STAR) {
                        next();
                        xF(e, rest) = xF(e, params).count;
                        special = true;
                } else if (T0 == TOKEN_PERCENT) {
                        next();
                        xF(e, ikwargs) = xF(e, params).count;
                        special = true;
                }

                expect(TOKEN_IDENTIFIER);
                rvP(xF(e, params), tok()->identifier);
                tok()->tag = TT_PARAM;
                next();

                if (try_consume(':', TT_PUNCT)) {
                        rvP(xF(e, constraints), parse_type(ty, 0));
                        (*vvL(xF(e, constraints)))->end = TEnd;
                } else {
                        rvP(xF(e, constraints), NULL);
                }

                if (!special && T0 == TOKEN_EQ) {
                        next();
                        rvP(xF(e, dflts), parse_expr(ty, 0));
                        (*vvL(xF(e, dflts)))->end = TEnd;
                } else {
                        rvP(xF(e, dflts), NULL);
                }

                record_extra(ty, "Param", NULL, param, TEnd);

                if (T0 == ',') {
                        next();
                }
        }

        LOAD_NE();

        consume(')');

        EndCatch();

EndOfParams:
        while (vN(xF(e, constraints)) < vN(xF(e, params))) {
                rvP(xF(e, constraints), NULL);
        }

        while (vN(xF(e, dflts)) < vN(xF(e, params))) {
                rvP(xF(e, dflts), NULL);
        }

        e->end = TEnd;

        if (T0 == TOKEN_ARROW) {
                next();
                xF(e, return_type) = parse_type(ty, -1);
        }

        if (!recovered) {
                xF(e, proto) = clone_span_a(ty, proto_start, LocS(TEnd));
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

                        rvP(xF(e, type_bounds),  bound);

                        if (K0 != KEYWORD_AND && T0 != ',') {
                                break;
                        }

                        next();

                }
        }
}

static Expr *
parse_function(Ty *ty, Expr **name, bool *is_operator)
{
        Expr *e = mkfunc(ty);

        bool sugared_generator = false;

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

        if (is_operator != NULL) {
                *is_operator = op_fixup(ty, 0);
        } else {
                (void)op_fixup(ty, 0);
        }

        if (T0 == TOKEN_IDENTIFIER) {
                xF(e, name) = tok()->identifier;
                if (is_operator != NULL && s_eq(xF(e, name), "in")) {
                        *is_operator = true;
                }
                if (name != NULL) {
                        *name = mkid(tok()->identifier);
                        xF((*name), module) = tok()->module;
                }
                tok()->tag = TT_FUNC;
                next();
        }

        xF(e, star) = try_consume('*');

        if (xF(e, name) != NULL && LocS(tok()->start)[-1] == ' ') {
                Expr *f = parse_expr(ty, 0);
                if (
                        (f->type != EXPRESSION_FUNCTION)
                     && (f->type != EXPRESSION_IMPLICIT_FUNCTION)
                ) {
                        die_at(f, "expected function expression");
                }
                xF(f, name) = xF(e, name);
                return f;
        }

        parse_function_header(ty, e);

        if (sugared_generator) {
                unconsume(TOKEN_KEYWORD);
                tok()->keyword = KEYWORD_GENERATOR;
        }

Body:
        if (T0 == ';') {
                next();
                xF(e, body) = NULL;
        } else if (type == KEYWORD_MACRO && try_consume('=')) {
                xF(e, body) = to_stmt(parse_expr_template(ty));
        } else {
                if (CatchError()) {
                        xF(e, body) = NULL;
                } else {
                        xF(e, body) = parse_statement(ty, -1);
                        EndCatch();
                }
        }

        if (sugared_generator && xF(e, name) != NULL) {
                xF(sF(xF(e, body), expression), name) = afmt("<%s:gen>", xF(e, name));
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_function(Ty *ty)
{
        ExprVec decorators       = {0};
        ExprVec macro_decorators = {0};

        SCRATCH_SAVE();

        parse_decorators(ty, &decorators, &macro_decorators);

        Expr *fun = parse_function(ty, NULL, NULL);
        xF(fun, decorators) = decorators;

        while (vN(macro_decorators) > 0) {
                Expr *dec = *vvX(macro_decorators);
                v__(xF(dec, args), 0) = fun;
                fun = dec;
                expedite_fun(ty, fun, NULL);
        }

        SCRATCH_RESTORE();

        return fun;
}

static Expr *
prefix_assert_jit(Ty *ty)
{
        next();

        Expr *f = parse_expr(ty, 0);

        if (f->type == EXPRESSION_FUNCTION) {
                xF(f, must_jit) = true;
        }

        return f;
}

/* rewrite [ op ] as ((a, b) -> a op b) */
static Expr *
opfunc(Ty *ty)
{
        Location start = tok()->start;

        consume('[');

        Token t = *tok();
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

        Location end = TEnd;

        Expr *e = parse_expr(ty, 0);
        e->start = start;
        SYNTHETIC(e);

        record_sugar(ty, "operator-function", start, end);

        return e;
}

static Expr *
prefix_at(Ty *ty)
{
        switch (T1) {
        case '{':
                next();
                next();

                Expr *m = parse_decorator_macro(ty);

                consume('}');

                Expr *stmt = mkxpr(STATEMENT);
                xF(stmt, statement) = parse_statement(ty, -1);

                rvI(xF(m, args), stmt, 0);
                rvI(xF(m, fconds), NULL, 0);

                return m;

        default:
                return prefix_function(ty);
        }
}



static Expr *
prefix_star(Ty *ty)
{
        Expr *e = mkxpr(SPREAD);

        consume(TOKEN_STAR);

        if (
                TypeContext
             || (NoEquals && T0 != ')')
        ) {
                e->type = EXPRESSION_SPREAD;
                xF(e, value) = parse_expr(ty, 0);
        } else {
                e->type = EXPRESSION_MATCH_REST;
                xF(e, module) = NULL;


                if (T0 == TOKEN_IDENTIFIER) {
                        xF(e, identifier) = tok()->identifier;

                        if (tok()->module != NULL)
                                die("unexpected module qualifier in lvalue");

                        next();
                } else {
                        xF(e, identifier) = "_";
                }
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_statement(Ty *ty)
{
        Expr *e = mkxpr(STATEMENT);

        SAVE_NE(false);

        xF(e, statement) = parse_statement(ty, -1);
        e->end = xF(e, statement)->end;

        LOAD_NE();

        return e;
}

static Expr *
prefix_record(Ty *ty)
{
        Expr *e = mkxpr(TUPLE);

        consume('{');

        while (T0 != '}') {
                setctx(LEX_PREFIX);

                bool optional = try_consume('?');
                rvP(xF(e, required), !optional);

                if (T0 == TOKEN_STAR) {
                        Expr *item = mkxpr(SPREAD);
                        next();
                        if (T0 == '}') {
                                item->type = EXPRESSION_MATCH_REST;
                                xF(item, identifier) = "_";
                                xF(item, module) = NULL;
                        } else if (TypeContext && T0 == ',') {
                                item->type = EXPRESSION_SPREAD;
                                xF(item, value) = NULL;
                                item->end = TEnd;
                        } else {
                                item->type = EXPRESSION_SPREAD;
                                xF(item, value) = parse_expr(ty, 0);
                                item->end = TEnd;
                        }
                        rvP(xF(e, names), "*");
                        rvP(xF(e, es), item);
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
                                rvP(xF(e, names), xF(name, identifier));
                                rvP(xF(e, es), name);
                                break;

                        default:
                                expect_one_of(':', '=');
                                UNREACHABLE();
                        }
                } else if (name->type != EXPRESSION_IDENTIFIER) {
                        die_at(
                                name,
                                "unexpected expression used as "
                                "field name in record literal"
                        );
                } else {
                        expect_one_of(':', '=');
                        tok()->tag = TT_PUNCT;
                        next();
                        rvP(xF(e, names), xF(name, identifier));
                        rvP(xF(e, es), parse_expr(ty, 0));
                        TagTokenOf(ty, name, TT_FIELD);
                }

Next:
                if (try_consume(KEYWORD_IF)) {
                        rvP(xF(e, tconds), parse_expr(ty, 0));
                } else {
                        rvP(xF(e, tconds), NULL);
                }

                try_consume(',');
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
        Expr *pat;

        if (try_consume(KEYWORD_ELSE)) {
                pat = mkid("_");
        } else {
                SAVE_NE(true);
                SAVE_NC(false);
                pat = parse_expr(ty, 0);
                pat->end = TEnd;
                LOAD_NC();
                LOAD_NE();
        }

        return patternize(ty, pat);
}

static Expr *
parse_pattern(Ty *ty)
{
        Expr *pattern = next_pattern(ty);

        if (T0 == ',') {
                Expr *choices = mkxpr(CHOICE_PATTERN);
                choices->start = pattern->start;
                rvP(xF(choices, es), pattern);
                while (try_consume(',')) {
                        rvP(xF(choices, es), next_pattern(ty));
                }
                choices->end = v_L(xF(choices, es))->end;
                pattern = choices;
        }

        return pattern;
}

void
make_with(Ty *ty, Expr *e, StmtVec defs, Stmt *body)
{
        e->type = EXPRESSION_WITH;
        xF(e, with).defs = defs;

        Stmt *try = mkstmtx(TRY);
        sF(try, try).s = body;

        sF(try, try).finally = mkstmtx(DROP);

        Stmt *s = mkstmtx(MULTI);
        rvPv(sF(s, statements), defs);
        rvP(sF(s, statements), try);
        xF(e, with).block = s;

        try->start = body->start;
        try->end = body->end;
        SYNTHETIC(try);

        SYNTH(sF(try, try).finally, body->end);

        s->start = e->start;
        s->end = body->end;
        SYNTHETIC(s);

        for (usize i = 0; i < vN(defs); ++i) {
                SYNTHETIC(v__(defs, i));
                SYNTHETIC(sF(v__(defs, i), value));
        }
}

static Expr *
prefix_dbg(Ty *ty)
{
        consume_kw(DBG);

        Expr *e = parse_expr(ty, 0);
        e->dbg = true;

        return e;
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
        Expr *with = mkxpr(WITH);
        StmtVec defs = {0};

        // with / use
        next();

        for (;;) {
                SAVE_NE(true);
                Expr *e = parse_expr(ty, 0);
                LOAD_NE();

                Stmt *def = mkstmtx(DEFINITION);
                sF(def, pub) = false;
                sF(def, value) = mkxpr(ENTER);

                if (try_consume('=')) {
                        sF(def, target) = definition_lvalue(ty, e);
                        xF(sF(def, value), operand) = parse_expr(ty, 0);
                } else {
                        Expr *t = mkxpr(IDENTIFIER);
                        xF(t, identifier) = gensym();
                        xF(t, module) = NULL;
                        SYNTH(t, e->start);
                        sF(def, target) = t;
                        xF(sF(def, value), operand) = e;
                }

                def->start = e->start;
                def->end = xF(sF(def, value), operand)->end;
                sF(def, value)->start = xF(sF(def, value), operand)->start;
                sF(def, value)->end = xF(sF(def, value), operand)->end;

                rvP(defs, def);

                if (T0 == ',') {
                        next();
                } else {
                        break;
                }
        }

        make_with(ty, with, defs, parse_statement(ty, 0));

        with->end = TEnd;

        record_sugar(ty, "with", with->start, with->end);

        return with;
}

static Expr *
prefix_throw(Ty *ty)
{
        Expr *e = mkxpr(THROW);

        consume_kw(THROW);

        xF(e, throw) = parse_expr(ty, 0);

        if (T0 == ';') {
                next();
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_typeof(Ty *ty)
{
        Expr *e = mkxpr(TYPE_OF);

        consume_kw(TYPEOF);

        SAVE_TC(false);
        xF(e, operand) = parse_expr(ty, 0);
        LOAD_TC();

        e->end = TEnd;

        return e;
}

static Expr *
prefix_yield(Ty *ty)
{
        Expr *e = mkxpr(YIELD);
        vec_init(xF(e, es));

        consume_kw(YIELD);

        for (;;) {
                Expr *item;

                if (T0 == TOKEN_STAR) {
                        item = mkxpr(SPREAD);
                        next();
                        xF(item, value) = parse_expr(ty, 1);
                        item->end = TEnd;
                } else {
                        item = parse_expr(ty, 1);
                }

                rvP(xF(e, es), item);

                if (T0 != ',') {
                        break;
                }

                next();
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_match(Ty *ty)
{
        char *id = NULL;

        if (have_match_cond(ty)) {
                Expr *e = mkxpr(STATEMENT);
                xF(e, statement) = parse_match_cond(ty, have_kws(MATCH, IF));
                e->end = xF(e, statement)->end;
                return e;
        }

        if (T1 == '{') {
                Token kw = *tok();
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = id = gensym();
                putback(kw);
        }

        Expr *e = mkxpr(MATCH);

        consume_kw(MATCH);

        Location kw = TEnd;

        xF(e, subject) = parse_expr(ty, -1);
        e->end = xF(e, subject)->end = TEnd;

        if (id != NULL) {
                SYNTH(xF(e, subject), kw);
        }

        SAVE_NA(false);

        if (T0 == TOKEN_FAT_ARROW) {
                next();
                rvP(xF(e, patterns), patternize(ty, xF(e, subject)));
                xF(e, subject) = mkxpr(IDENTIFIER);
                xF(xF(e, subject), identifier) = id = gensym();
                SYNTH(xF(e, subject), kw);
                rvP(xF(e, thens), parse_expr(ty, 0));
                if (have_kw(ELSE)) {
                        Location at = tok()->start;
                        next();
                        Expr *alt = parse_expr(ty, 0);
                        Expr *any = mkid("it");
                        SYNTH(any, at);
                        rvP(xF(e, patterns), any);
                        rvP(xF(e, thens), alt);
                }
                goto End;
        }

        if (CatchError()) {
                goto End;
        }

        consume('{');

        rvP(xF(e, patterns), parse_pattern(ty));

        consume(TOKEN_FAT_ARROW);
        rvP(xF(e, thens), parse_expr(ty, 0));

        while (T0 != '}') {
                if (T0 == ',') {
                        next();
                }

                // Trailing comma is allowed
                if (T0 == '}') {
                        break;
                }

                rvP(xF(e, patterns), parse_pattern(ty));
                consume(TOKEN_FAT_ARROW);
                rvP(xF(e, thens), parse_expr(ty, 0));
        }

        consume('}');
        EndCatch();

End:
        LOAD_NA();

        e->end = TEnd;

        if (vN(xF(e, patterns)) > vN(xF(e, thens))) {
                vN(xF(e, patterns)) = vN(xF(e, thens));
        }

        if (id != NULL) {
                Expr *f = mkfunc(ty);
                rvP(xF(f, params), id);
                rvP(xF(f, dflts), NULL);
                rvP(xF(f, constraints), NULL);
                xF(f, body) = mkstmtx(EXPRESSION);
                sF(xF(f, body), expression) = e;
                f->start = xF(f, body)->start = e->start;
                f->end   = xF(f, body)->end   = e->end;
                SYNTHETIC(f);
                SYNTHETIC(xF(f, body));
                e = f;
                record_sugar(ty, "match-lambda", e->start, e->end);
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
                consume_kw(IN);
                iter = parse_expr(ty, 0);
        }

        Expr *g = mkfunc(ty);
        g->start = e->start;
        g->type = EXPRESSION_GENERATOR;
        xF(g, body) = mkstmtx(EACH_LOOP);

        if (have_kw(IF)) {
                next();
                sF(xF(g, body), each)._if = parse_expr(ty, 0);
        } else {
                sF(xF(g, body), each)._if = NULL;
        }

        if (have_kw(WHILE)) {
                next();
                sF(xF(g, body), each)._while = parse_expr(ty, 0);
        } else {
                sF(xF(g, body), each)._while = NULL;
        }

        sF(xF(g, body), each).target = target;
        sF(xF(g, body), each).array = iter;
        sF(xF(g, body), each).body = mkstmtx(EXPRESSION);
        sF(sF(xF(g, body), each).body, expression) = mkxpr(YIELD);
        sF(sF(xF(g, body), each).body, expression)->type = EXPRESSION_YIELD;
        rvP(xF(sF(sF(xF(g, body), each).body, expression), es), e);

        g->end = TEnd;

        xF(g, body)->start = e->start;
        xF(g, body)->end = g->end;
        sF(xF(g, body), each).body->start = sF(sF(xF(g, body), each).body, expression)->start = e->start;
        sF(xF(g, body), each).body->end = sF(sF(xF(g, body), each).body, expression)->end = e->end;

        return g;
}

static bool
try_parse_flag(Ty *ty, ExprVec *kwargs, StringVector *kws, ExprVec *kwconds)
{
        if (T0 != ':' && (T0 != TOKEN_BANG || !next_without_nl(ty, ':'))) {
                return false;
        }

        bool flag = (T0 == ':') || (next(), false);
        next();

        expect(TOKEN_IDENTIFIER);

        Expr *arg = mkxpr(BOOLEAN);
        xF(arg, boolean) = flag;

        rvP(*kwargs, arg);
        rvP(*kws, tok()->identifier);

        next();

        if (kwconds != NULL) {
                rvP(*kwconds, try_cond(ty));
        }

        return true;
}

static void
next_arg_(
        Ty *ty,
        ExprVec *args,
        ExprVec *conds,
        ExprVec *kwargs,
        StringVector *kws,
        ExprVec *kwconds
)
{
        if (try_parse_flag(ty, kwargs, kws, kwconds)) {
                return;
        }

        if (T0 == TOKEN_STAR) {
                Expr *arg = mkxpr(SPREAD);

                next();

                if (T0 == TOKEN_STAR) {
                        next();
                        arg->type = EXPRESSION_SPLAT;
                } else {
                        arg->type = EXPRESSION_SPREAD;
                }

                if (
                        (T0 == ',')
                     || (T0 == ')')
                     || (K0 == KEYWORD_IF)
                ) {
                        xF(arg, value) = mkxpr(IDENTIFIER);
                        xF(xF(arg, value), module) = NULL;
                        xF(xF(arg, value), identifier) = &"**"[arg->type == EXPRESSION_SPREAD];
                        arg->end = TEnd;
                        xF(arg, value)->start = arg->start;
                        xF(arg, value)->end = arg->end;
                } else {
                        xF(arg, value) = parse_expr(ty, 0);
                        arg->end = xF(arg, value)->end;
                }

                if (arg->type == EXPRESSION_SPLAT) {
                        rvP(*kwargs, arg);
                        rvP(*kws, "*");
                        if (kwconds != NULL) {
                                rvP(*kwconds, try_cond(ty));
                        }
                } else {
                        rvP(*args, arg);
                        rvP(*conds, try_cond(ty));
                }
        } else if (
                 (T0 == TOKEN_IDENTIFIER)
              && (
                         (T1 == ':')
                      || (T1 == TOKEN_EQ)
                 )
        ) {
                bool pun = (T1 == ':') && ((T2 == ',') || (T2 == ')'));
                tok()->tag = TT_PARAM;
                rvP(*kws, tok()->identifier);
                if (pun) {
                        Expr *arg = mkxpr(IDENTIFIER);
                        xF(arg, identifier) = tok()->identifier;
                        xF(arg, module)     = NULL;
                        next();
                        arg->end = TEnd;
                        next();
                        rvP(*kwargs, arg);
                } else {
                        next();
                        next();
                        rvP(*kwargs, parse_expr(ty, 0));
                }
                if (kwconds != NULL) {
                        rvP(*kwconds, try_cond(ty));
                }
        } else {
                rvP(*args, parse_expr(ty, 0));
                rvP(*conds, try_cond(ty));
        }
}

static void
next_arg(
        Ty *ty,
        ExprVec *args,
        ExprVec *conds,
        ExprVec *kwargs,
        StringVector *kws,
        ExprVec *kwconds
)
{
        Location start = tok()->start;
        usize n = vN(*kwargs);

        next_arg_(ty, args, conds, kwargs, kws, kwconds);

        if (vN(*kwargs) > n && vN(*kws) > n && strcmp(v__(*kws, n), "*") != 0) {
                record_extra(ty, "Kwarg", NULL, start, TEnd);
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
                        &xF(e, method_args),
                        &xF(e, mconds),
                        &xF(e, method_kwargs),
                        &xF(e, method_kws),
                        NULL
                );
        }

        if (have_kw(FOR)) {
                if (xF(e, method_args).count > 0) {
                        *vvL(xF(e, method_args)) = gencompr(ty, *vvL(xF(e, method_args)));
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
                        &xF(e, method_args),
                        &xF(e, mconds),
                        &xF(e, method_kwargs),
                        &xF(e, method_kws),
                        NULL
                );
        }

Close:
        consume(')');
        EndCatch();

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
        case '@':
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

        Token const *slash = token(-1);
        Location start = slash->start;
        Location end = slash->end;

        next();
        Expr *body = parse_expr(ty, 0);
        next();

        Expr *nil = mkxpr(NIL);
        nil->start = start;
        nil->end = end;

        Expr *f = mkcall(ty, nil);
        rvP(xF(f, args), body);
        rvP(xF(f, fconds), NULL);
        f->end = TEnd;
        SYNTHETIC(f);
        SYNTHETIC(nil);

        rvP(xF(e, method_args), mkpartial(ty, f));
        rvP(xF(e, mconds), NULL);

        e->end = TEnd;

        return e;
}

inline static Expr *
prefix_parenthesis(Ty *ty)
{
        /*
         * This can either be a plain old parenthesized expression, e.g., (4 + 4)
         * or it can be an identifier list for an arrow function, e.g., (a, b, c).
         */

        Location start = tok()->start;
        Expr *e;

        bool for_header = (ForParen == TokenIndex + 1);

        consume('(');

        if (
                for_header
             && (
                        (T0 == ';')
                     || (T0 == TOKEN_KEYWORD && get_prefix_parser(ty) == NULL)
                )
        ) {
                ForInit     = true;
                ForInitExpr = NULL;
                return mkxpr(NIL);
        }

        /*
         * () is an empty identifier list.
         */
        if (T0 == ')') {
                next();
                e = mkxpr(TUPLE);
                e->start = start;
                e->end = TEnd;
                xF(e, only_identifiers) = true;
                return e;
        }

        /*
         * If we have an infix operator that cannot also be a prefix
         * operator, assume this is an operator section.
         */
        if (get_infix_parser(ty) != NULL && get_prefix_parser(ty) == NULL) {
                e = mkfunc(ty);
                rvP(xF(e, params), gensym());
                rvP(xF(e, dflts), NULL);
                rvP(xF(e, constraints), NULL);

                Expr *t = mkxpr(IDENTIFIER);
                xF(t, identifier) = v_0(xF(e, params));
                xF(t, module) = NULL;
                SYNTH(t, tok()->start);

                xF(e, body) = mkstmtx(EXPRESSION);
                sF(xF(e, body), expression) = get_infix_parser(ty)(ty, t);
                xF(e, body)->start = sF(xF(e, body), expression)->start;
                xF(e, body)->end = sF(xF(e, body), expression)->end;

                consume(')');

                e->start = start;
                e->end = TEnd;
                SYNTHETIC(e);
                SYNTHETIC(xF(e, body));

                record_sugar(ty, "operator-section", start, TEnd);

                return e;
        }

        // (:a, ...)
        if (T0 == ':' && T1 == TOKEN_IDENTIFIER) {
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = token(2)->identifier;
                tok()->module = NULL;
        }

        SAVE_NI(for_header ? false : NoIn);
        SAVE_NE(true);
        SAVE_NA(false);
        SAVE_NC(false);
        if (CatchError()) {
                e = mkxpr(STATEMENT);
                xF(e, statement) = mkstmtx(NULL);
        } else {
                if (TypeContext && T0 == TOKEN_STAR) {
                        e = mkxpr(SPREAD);
                        next();
                        xF(e, value) = parse_expr(ty, 0);
                        e->end = TEnd;
                } else {
                        e = parse_expr(ty, 0);
                }
                EndCatch();
        }
        LOAD_NC();
        LOAD_NA();
        LOAD_NE();

        if (T0 == TOKEN_EQ || T0 == TOKEN_MAYBE_EQ) {
                SAVE_NA(true);
                e = infix_eq(ty, e);
                LOAD_NA();
        }

        LOAD_NI();

        if (for_header && T0 == ';') {
                ForInit     = true;
                ForInitExpr = e;
                return e;
        }

        if (
                (e->type == EXPRESSION_SPREAD)
             || (T0 == ',')
             || (T0 == ':')
             || (K0 == KEYWORD_IF)
        ) {
                Expr *list = mkxpr(TUPLE);
                list->start = start;
                xF(list, only_identifiers) = true;

                if (
                        (e->type != EXPRESSION_IDENTIFIER)
                     && (e->type != EXPRESSION_MATCH_REST)
                ) {
                        xF(list, only_identifiers) = false;
                }

                e->end = TEnd;
                rvP(xF(list, es), e);
                rvP(xF(list, names), NULL);
                rvP(xF(list, required), true);

                if (have_kw(IF)) {
                        next();
                        rvP(xF(list, tconds), parse_expr(ty, 0));
                } else {
                        rvP(xF(list, tconds), NULL);
                }

                if (T0 == ',') {
                        next();
                }

                while (T0 != ')') {
                        if (T0 == TOKEN_QUESTION) {
                                next();
                                rvP(xF(list, required), false);
                        } else {
                                rvP(xF(list, required), true);
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


                        rvP(xF(list, es), e);
                        rvP(
                                xF(list, names),
                                (e->type == EXPRESSION_SPREAD) ? "*" : NULL
                        );

                        if (have_kw(IF)) {
                                next();
                                rvP(xF(list, tconds), parse_expr(ty, 0));
                        } else {
                                rvP(xF(list, tconds), NULL);
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
        } else if (have_kw(FOR)) {
                e = gencompr(ty, e);

                consume(')');

                e->start = start;
                e->end = TEnd;

                return e;
        } else {
                consume(')');

                if (state.module != NULL && start.byte < e->start.byte) {
                        rvP(
                                state.module->extras,
                                ((SyntaxExtra) {
                                        .kind        = "Paren",
                                        .start       = start,
                                        .end         = TEnd,
                                        .inner_start = e->start,
                                        .inner_end   = e->end,
                                        .inner       = true
                                })
                        );
                }

                e->start = start;
                e->end = TEnd;

                return e;
        }
}

static Expr *
prefix_true(Ty *ty)
{
        Expr *e = mkxpr(BOOLEAN);
        xF(e, boolean) = true;

        consume_kw(TRUE);

        return e;
}

static Expr *
prefix_false(Ty *ty)
{
        Expr *e = mkxpr(BOOLEAN);
        xF(e, boolean) = false;

        consume_kw(FALSE);

        return e;
}

static Expr *
prefix_self(Ty *ty)
{

        Expr *e = mkxpr(SELF);

        consume_kw(SELF);

        return e;
}

static Expr *
prefix_nil(Ty *ty)
{

        Expr *e = mkxpr(NIL);

        consume_kw(NIL);

        return e;
}

static Expr *
prefix_regex(Ty *ty)
{
        Expr *e = mkxpr(REGEX);
        xF(e, regex) = tok()->regex;

        consume(TOKEN_REGEX);

        return e;
}

static Expr *
prefix_unterminated_regex(Ty *ty)
{
        die("unterminated regex literal");
}

static Expr *
prefix_invalid_regex_flags(Ty *ty)
{
        die("invalid regex flags: the flags are a, i, m, s, U, x, u and v; there is no g, since sub, matches and split already act on every match");
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
         * fn sum [match] {
         *      [x, *xs] => x + sum(*xs),
         *      []       => 0,
         * }
         *
         * Why not?
         */
        if (K0 == KEYWORD_MATCH && T1 == ']') {
                char *args = gensym();

                f = mkfunc(ty);
                rvP(xF(f, params), args);
                rvP(xF(f, constraints), NULL);
                rvP(xF(f, dflts), NULL);
                xF(f, rest) = 0;

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

                xF(f, body) = to_stmt(prefix_match(ty));

                return f;
        }

        int in_type = EXPRESSION_IN;
        Token lhs = *tok();

        if (T1 == TOKEN_KEYWORD) switch (K1) {
        case KEYWORD_IN:
        InSection:
                next();
                next();
                e = parse_expr(ty, 0);
                consume(']');
                f = mkfunc(ty);
                rvP(xF(f, params), gensym());
                rvP(xF(f, dflts), NULL);
                rvP(xF(f, constraints), NULL);
                xF(f, body) = mkstmtx(EXPRESSION);
                sF(xF(f, body), expression) = mkxpr(NOT_IN);
                sF(xF(f, body), expression)->type = in_type;
                xF(sF(xF(f, body), expression), left) = mkxpr(IDENTIFIER);
                xF(sF(xF(f, body), expression), left)->type = EXPRESSION_IDENTIFIER;
                xF(xF(sF(xF(f, body), expression), left), identifier) = xF(f, params).items[0];
                xF(xF(sF(xF(f, body), expression), left), module) = NULL;
                xF(sF(xF(f, body), expression), left)->start = lhs.start;
                xF(sF(xF(f, body), expression), left)->end = lhs.end;
                xF(sF(xF(f, body), expression), right) = e;
                xF(f, body)->start = sF(xF(f, body), expression)->start = lhs.start;
                xF(f, body)->end = sF(xF(f, body), expression)->end = e->end;
                f->start = start;
                f->end = TEnd;
                SYNTHETIC(f);
                SYNTHETIC(xF(f, body));
                record_sugar(ty, "in-section", start, TEnd);
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
                        Expr *item = mkxpr(SPREAD);
                        next();

                        if (T0 == ']' || T0 == ',') {
                                xF(item, value) = mkxpr(IDENTIFIER);
                                xF(xF(item, value), module) = NULL;
                                xF(xF(item, value), identifier) = "*";
                                xF(item, value)->start = item->start;
                                xF(item, value)->end = item->end = TEnd;
                        } else {
                                xF(item, value) = parse_expr(ty, 0);
                        }

                        item->end = TEnd;

                        rvP(xF(e, elements), item);
                        rvP(xF(e, optional), false);
                } else {
                        if (T0 == TOKEN_QUESTION) {
                                next();
                                rvP(xF(e, optional), true);
                        } else {
                                rvP(xF(e, optional), false);
                        }
                        rvP(xF(e, elements), parse_expr(ty, 0));
                }

                if (have_kw(IF)) {
                        next();
                        rvP(xF(e, aconds), parse_expr(ty, 0));
                } else {
                        rvP(xF(e, aconds), NULL);
                }

                if (have_kw(FOR)) {
                        e->type = EXPRESSION_ARRAY_COMPR;
                        parse_comprehension(ty, &xF(e, compr));
                        expect(']');
                } else if (T0 == ',') {
                        next();
                } else if (
                        xF(e, elements).count == 1 &&
                        get_infix_parser(ty) != NULL &&
                        (T1 == ']' || (have_not_in(ty) && token(2)->type == ']'))
                ) {
                        f = mkfunc(ty);
                        rvP(xF(f, params), gensym());
                        rvP(xF(f, dflts), NULL);
                        rvP(xF(f, constraints), NULL);
                        struct token t = *tok();
                        next();
                        struct token t2 = *tok();
                        if (t2.type != ']') {
                                next();
                        }
                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = xF(f, params).items[0];
                        tok()->module = NULL;
                        if (t2.type != ']') {
                                putback(t2);
                        }
                        putback(t);
                        xF(f, body) = mkstmtx(EXPRESSION);
                        sF(xF(f, body), expression) = get_infix_parser(ty)(ty, xF(e, elements).items[0]);
                        f->start = start;
                        e = f;
                } else {
                        expect(']');
                }
        }

        next();
        EndCatch();

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
        if (T0 == ':' && try_consume(':')) {
                Expr *type = parse_type(ty, 0);
                rvP(xF(template, template).stmts, to_stmt(type));
        }
        while (T0 != TOKEN_TEMPLATE_END) {
                rvP(xF(template, template).stmts, parse_statement(ty, 0));
        }
        next();
        template->end = TEnd;
        CurrentTemplate = save;

        return template;
}

static Expr *
prefix_template_expr(Ty *ty)
{
        if (CurrentTemplate == NULL) {
                die("stray template expression");
        }

        ExprVec  *exprs = &xF(CurrentTemplate, template).exprs;
        ExprVec  *holes = &xF(CurrentTemplate, template).holes;
        i32Vector *ctxs = &xF(CurrentTemplate, template).ctxs;

        Expr *e = mkxpr(TEMPLATE_HOLE);
        xF(e, hole).i = vN(xF(CurrentTemplate, template).holes);

        next();

        if (T0 == '(') {
                next();
                rvP(*holes, parse_expr(ty, 0));
                rvP(*ctxs, CTX_EXPR);
                consume(')');
        } else if (T0 == '{') {
                e->type = EXPRESSION_TEMPLATE_VHOLE;
                next();
                rvP(*holes, parse_expr(ty, 0));
                rvP(*ctxs, CTX_EXPR);
                consume('}');
        } else if (T0 == ':') {
                e->type = EXPRESSION_TEMPLATE_THOLE;
                next();
                rvP(*holes, parse_type(ty, 99));
                rvP(*ctxs, CTX_TYPE);
        } else if (T0 == '\\' || T0 == TOKEN_CHECK_MATCH || T0 == '!') {
                next();
                e->type = EXPRESSION_TEMPLATE_XHOLE;
                xF(e, hole).expr = parse_expr(ty, 99);
                rvP(*exprs, e);
        } else {
                SAVE_NC(true);
                rvP(*holes, parse_expr(ty, 99));
                rvP(*ctxs, CTX_EXPR);
                LOAD_NC();
                if (!NoConstraint && try_consume(':', TT_PUNCT)) {
                        SAVE_NA(true);
                        xF(e, hole).constraint = parse_type(ty, 0);
                        LOAD_NA();
                }
        }

        e->end = TEnd;

        return e;
}

static Expr *
prefix_tyx(Ty *ty)
{
#define DEBUG(fmt, ...) do { if (EnableLogging) { LOGX("|%*s" fmt, ParseDepth * 4, "" __VA_OPT__(,) __VA_ARGS__); } } while (0)
        Expr *tyx = mkxpr(FUNCTION_CALL);
        Expr *text;

        next();

        xF(tyx, function) = parse_expr(ty, 10);

        DEBUG(">> parsing tyx element: %s", show_expr(xF(tyx, function)));

        setctx(LEX_TYX);
        while (T0 != '>' && T0 != '/>') {
                setctx(LEX_PREFIX);
                expect(TOKEN_IDENTIFIER);
                DEBUG("  tyx kwarg: %s", tok()->identifier);
                rvP(xF(tyx, kws), tok()->identifier);
                next();
                consume('=');
                rvP(xF(tyx, kwargs), parse_expr(ty, 10));
                rvP(xF(tyx, fkwconds), NULL);
                setctx(LEX_TYX);
                DEBUG("  tyx prop: %s", show_expr(v_L(xF(tyx, kwargs))));
        }
        if (try_consume('/>')) {
                goto End;
        }
        consume('>');
        while (T0 != '</') {
                switch (T0) {
                case TOKEN_STRING:
                        text = mkxpr(STRING);
                        xF(text, string) = tok()->string;
                        rvP(xF(tyx, args), text);
                        rvP(xF(tyx, fconds), NULL);
                        next();
                        break;

                case '{':
                        next();
                        rvP(xF(tyx, args), parse_expr(ty, 0));
                        rvP(xF(tyx, fconds), NULL);
                        consume('}');
                        DEBUG("  tyx braced arg: %s", show_expr(v_L(xF(tyx, args))));
                        break;

                case '<':
                        rvP(xF(tyx, args), parse_expr(ty, 999));
                        rvP(xF(tyx, fconds), NULL);
                        DEBUG("  tyx child: %s", show_expr(xF(v_L(xF(tyx, args)), function)));
                        break;

                default:
                        die("unexpected token in tyx fragment: %s", token_show(ty, tok()));
                }
                setctx(LEX_TYX);
        }
        next();
        (void)parse_expr(ty, 10);
        setctx(LEX_TYX);
        consume('>');

End:
        DEBUG("<< parsed tyx element: %s", show_expr(xF(tyx, function)));
        tyx->end = TEnd;
        return tyx;
}

static Expr *
prefix_greater(Ty *ty)
{
        Expr *e = mkxpr(REF_PATTERN);

        consume('>');

        xF(e, target) = assignment_lvalue(ty, parse_expr(ty, 0));
        e->end = TEnd;

        return e;
}

static Expr *
prefix_carat(Ty *ty)
{
        Location start = tok()->start;

        consume('^');

        if (T0 == '$$' && CurrentTemplate != NULL) {
                Expr *e = mkxpr(RESOURCE_BINDING);
                e->start = start;
                xF(e, tagged) = prefix_template_expr(ty);
                e->end = TEnd;
                return e;
        }

        Expr *id = prefix_identifier(ty);
        id->type = EXPRESSION_RESOURCE_BINDING;
        id->start = start;
        return id;
}

static Expr *
prefix_dot_dot_dot(Ty *ty)
{
        Expr *e = mkxpr(DOT_DOT_DOT);

        Expr *zero = mkxpr(INTEGER);
        xF(zero, integer) = 0;

        consume(TOKEN_DOT_DOT_DOT);

        if (TypeContext && (T0 == '(')) {
                next();
                Expr *inner = parse_expr(ty, 6);

                switch (T0) {
                case '|':
                        next();
                        consume(')');
                        e->type = EXPRESSION_PACK_UNION;
                        xF(e, operand) = inner;
                        e->end = TEnd;
                        return e;

                case '&':
                        next();
                        consume(')');
                        e->type = EXPRESSION_PACK_INTERSECT;
                        xF(e, operand) = inner;
                        e->end = TEnd;
                        return e;

                default:
                        die_at(inner, "expected '|' or '&' after '...'");
                }
        }

        xF(e, left) = TypeContext ? NULL : zero;
        xF(e, right) = parse_expr(ty, 7);
        e->end = xF(e, right)->end;

        return e;
}

static Expr *
prefix_dot_dot(Ty *ty)
{
        Expr *e = mkxpr(DOT_DOT);

        Expr *zero = mkxpr(INTEGER);
        xF(zero, integer) = 0;

        consume(TOKEN_DOT_DOT);

        xF(e, left) = zero;
        xF(e, right) = no_rhs(ty, 0) ? NULL : parse_expr(ty, 7);
        e->end = TEnd;

        return e;
}

static Expr *
infix_subscript(Ty *, Expr *);

static Expr *
implicit_subscript(Ty *ty, Expr *o)
{
        Expr *f = mkfunc(ty);
        xF(f, body) = mkret(ty, infix_subscript(ty, o));

        rvP(xF(f, params), xF(o, identifier));
        rvP(xF(f, dflts), NULL);
        rvP(xF(f, constraints), NULL);

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

        if (K0 == KEYWORD_NOT) {
                next();
                unconsume(TOKEN_IDENTIFIER);
                tok()->identifier = "__not__";
                tok()->module = NULL;
        }

        Expr *o = mkxpr(IDENTIFIER);
        xF(o, identifier) = gensym();
        xF(o, module) = NULL;
        SYNTH(o, start);

        if (T0 == TOKEN_INTEGER) {
                imax k = tok()->integer;
                next();
                unconsume(']');
                unconsume(TOKEN_INTEGER);
                tok()->integer = k;
                unconsume('[');
        }

        if (T0 == '[') {
                Expr *f = implicit_subscript(ty, o);
                f->start = start;
                f->end = TEnd;
                SYNTHETIC(f);
                record_sugar(ty, "implicit-method", start, TEnd);
                return f;
        }

        Expr *e = mkxpr(MEMBER_ACCESS);
        xF(e, maybe) = try_consume('?');
        e->start = start;
        e->type = try_consume('.') ? EXPRESSION_MEMBER_ACCESS
                                   : EXPRESSION_METHOD_CALL;
        xF(e, member) = parse_member(ty);
        xF(e, object) = o;
        e->end = TEnd;

        TagTokenOf(ty, xF(e, member), TT_FUNC);

        if (e->type == EXPRESSION_METHOD_CALL) {
                e = parse_method_call(ty, e);
        }

        Expr *f = mkfunc(ty);
        xF(f, body) = mkret(ty, e);
        f->start = start;
        f->end = TEnd;
        SYNTHETIC(f);

        rvP(xF(f, params), xF(o, identifier));
        rvP(xF(f, dflts), NULL);
        rvP(xF(f, constraints), NULL);

        record_sugar(ty, "implicit-method", start, TEnd);

        return f;
}

static Expr *
prefix_implicit_lambda(Ty *ty)
{
        Location start = tok()->start;

        consume('$');
        consume('{');

        Expr *e = parse_expr(ty, 0);

        consume('}');


        Expr *f = mkfunc(ty);
        f->type = EXPRESSION_IMPLICIT_FUNCTION;
        f->start = start;
        f->end = TEnd;
        SYNTHETIC(f);
        xF(f, body) = mkstmtx(EXPRESSION);
        sF(xF(f, body), expression) = e;
        xF(f, body)->start = e->start;
        xF(f, body)->end = e->end;

        record_sugar(ty, "implicit-lambda", start, TEnd);

        return f;
}

static Expr *
prefix_bit_or(Ty *ty)
{
        Expr *e = mkxpr(LIST);
        xF(e, only_identifiers) = true;
        vec_init(xF(e, es));

        next();

        SAVE_NE(true);
        SAVE_NP(true);
        while (T0 != '|') {
                Expr *item = parse_expr(ty, 1);
                xF(e, only_identifiers) &= (item->type == EXPRESSION_IDENTIFIER);
                rvP(xF(e, es), item);
                if (T0 != '|')
                        consume(',');
        }
        LOAD_NE();
        LOAD_NP();

        consume('|');

        if (vN(xF(e, es)) == 0 && T0 != TOKEN_ARROW) {
                die("expected `->` after empty parameter list `| |`");
        }

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

        if (f->type != EXPRESSION_FUNCTION) {
                die("expected a function body after `->`");
        }

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
        Expr *e = mkxpr(NIL);

        consume(TOKEN_PERCENT);
        expect(TOKEN_IDENTIFIER);

        if (tok()->module != NULL && *tok()->module != '\0') {
                next();
                EStart = e->start;
                EEnd = TEnd;
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

static Expr *
prefix_dict(Ty *ty)
{
        Expr *e = mkxpr(DICT);

        consume(TOKEN_DICT_OPEN);

        while (T0 != '}') {
                setctx(LEX_PREFIX);

                if (T0 == TOKEN_STAR && T1 == ':') {
                        Location start = tok()->start;
                        next();
                        next();
                        unconsume(TOKEN_ARROW);
                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = "it";
                        xF(e, dflt) = parse_expr(ty, 0);
                        xF(e, dflt)->start = start;
                        xF(e, dflt)->end = TEnd;
                } else if (T0 == TOKEN_STAR) {
                        Expr *item = mkxpr(SPREAD);

                        next();

                        if (try_consume(TOKEN_STAR)) {
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
                                xF(item, value) = mkxpr(IDENTIFIER);
                                xF(xF(item, value), module) = NULL;
                                xF(xF(item, value), identifier) = &"**"[item->type == EXPRESSION_SPREAD];
                                xF(item, value)->start = item->start;
                                xF(item, value)->end = item->end = TEnd;
                        } else {
                                xF(item, value) = parse_expr(ty, 0);
                                item->end = TEnd;
                        }

                        rvP(xF(e, keys), item);
                        rvP(xF(e, values), NULL);
                } else {
                        SAVE_NC(true);
                        Expr *key = parse_expr(ty, 0);
                        rvP(xF(e, keys), key);
                        LOAD_NC();
                        if (key->type == EXPRESSION_IDENTIFIER) {
                                rvP(xF(e, values), xF(key, constraint));
                                xF(key, constraint) = NULL;
                        } else {
                                rvP(xF(e, values), NULL);
                        }
                        if (T0 == ':') {
                                next();
                                *vvL(xF(e, values)) = parse_expr(ty, 0);
                        }
                }

                if (K0 == KEYWORD_FOR) {
                        e->type = EXPRESSION_DICT_COMPR;
                        parse_comprehension(ty, &xF(e, dcompr));
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

static Expr *
prefix_set(Ty *ty)
{
        Expr *e = mkxpr(SET);

        consume(TOKEN_SET_OPEN);

        while (T0 != ']') {
                setctx(LEX_PREFIX);

                if (T0 == TOKEN_STAR) {
                        Expr *item = mkxpr(SPREAD);
                        next();
                        xF(item, value) = parse_expr(ty, 0);
                        item->end   = TEnd;
                        rvP(xF(e, elements), item);
                } else {
                        rvP(xF(e, elements), parse_expr(ty, 0));
                }

                rvP(xF(e, optional), false);

                if (have_kw(IF)) {
                        next();
                        rvP(xF(e, aconds), parse_expr(ty, 0));
                } else {
                        rvP(xF(e, aconds), NULL);
                }

                if (have_kw(FOR)) {
                        e->type = EXPRESSION_SET_COMPR;
                        parse_comprehension(ty, &xF(e, compr));
                        expect(']');
                } else if (T0 == ',') {
                        next();
                } else {
                        expect(']');
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
        Expr *call = mkxpr(FUNCTION_CALL);
        xF(call, function) = func;
        call->start = func->start;
        return call;
}

static Expr *
mkpartial(Ty *ty, Expr *sugared)
{
        Expr *fun = mkxpr(IDENTIFIER);
        xF(fun, identifier) = "__desugar_partial__";
        xF(fun, module) = "prelude";
        SYNTH(fun, sugared->start);

        Expr *call = mkcall(ty, fun);
        rvP(xF(call, args), sugared);
        rvP(xF(call, fconds), NULL);

        call->start = sugared->start;
        call->end = sugared->end;
        SYNTHETIC(call);

        record_sugar(ty, "partial", sugared->start, sugared->end);

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

        if (try_consume(')')) {
                e->end = TEnd;
                return e;
        }

        if (CatchError()) {
                goto End;
        }

        next_arg(
                ty,
                &xF(e, args),
                &xF(e, fconds),
                &xF(e, kwargs),
                &xF(e, kws),
                &xF(e, fkwconds)
        );

        if (have_kw(FOR)) {
                if (xF(e, args).count > 0) {
                        *vvL(xF(e, args)) = gencompr(ty, *vvL(xF(e, args)));
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
                        &xF(e, args),
                        &xF(e, fconds),
                        &xF(e, kwargs),
                        &xF(e, kws),
                        &xF(e, fkwconds)
                );
        }

        consume(')');

        EndCatch();

End:
        e->end = TEnd;
        return e;
}

static Expr *
infix_brace(Ty *ty, Expr *left)
{
        die("TODO");
        return left;
}

static Expr *
infix_eq(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(EQ);

        e->type = (T0 == TOKEN_EQ)
                ? EXPRESSION_EQ
                : EXPRESSION_MAYBE_EQ;

        next();

        e->start = left->start;
        xF(e, target) = assignment_lvalue(ty, left);

        SAVE_NA(true);

        if (left->type == EXPRESSION_LIST) {
                xF(e, value) = parse_expr(ty, -1);
        } else {
                xF(e, value) = parse_expr(ty, 1);
        }

        LOAD_NA();

        e->end = xF(e, value)->end;

        return e;
}

static Expr *
prefix_complement(Ty *ty)
{
        Expr *e = mkxpr(UNARY_OP);
        xF(e, uop) = "~";

        next();

        xF(e, operand) = parse_expr(ty, 8);
        e->end = TEnd;

        return e;
}

static Expr *
prefix_user_op(Ty *ty)
{
        Expr *e = mkxpr(UNARY_OP);
        xF(e, uop) = tok()->operator;

        next();

        xF(e, operand) = parse_expr(ty, 9);
        e->end = TEnd;

        return e;
}

static Expr *
infix_complement(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(USER_OP);

        e->start = left->start;
        xF(e, left) = left;
        xF(e, op_name) = "~";

        next();

        xF(e, right) = parse_expr(ty, 7);
        e->end = TEnd;

        return e;
}

static Expr *
infix_user_op(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(USER_OP);

        e->start = left->start;
        xF(e, left) = left;
        xF(e, op_name) = tok()->identifier;
        consume(TOKEN_USER_OP);

        int prec = 8;

        struct value *p = table_look(ty, &uops, xF(e, op_name));
        if (p != NULL) {
                prec = (p->z > 0) ? p->z : llabs(p->z) - 1;
        }

        struct value *sc = table_look(ty, &uopcs, xF(e, op_name));
        if (sc != NULL) {
                xF(e, sc) = sc->ptr;
        } else {
                xF(e, sc) = NULL;
        }

        xF(e, right) = parse_expr(ty, prec);
        e->end = TEnd;

        return e;
}

static Expr *
infix_type_union(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(TYPE_UNION);
        e->start = left->start;
        rvP(xF(e, es), left);

        while (T0 == '|') {
                next();
                rvP(xF(e, es), parse_type(ty, 5));
        }

        e->end = TEnd;

        return e;
}

static Expr *
infix_list(Ty *ty, Expr *left)
{

        Expr *e = mkxpr(LIST);
        e->start = left->start;
        rvP(xF(e, es), left);

        SAVE_NE(true);

        while (T0 == ',') {
                next();
                rvP(xF(e, es), parse_expr(ty, 1));
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
        xF(e, left) = left;
        xF(e, right) = NULL;
        e->end = TEnd;

        return e;
}

static Expr *
infix_subscript(Ty *ty, Expr *left)
{

        Expr *e = mkxpr(SUBSCRIPT);
        e->start = left->start;

        Location bracket = tok()->start;

        consume('[');

        if (T0 == ']') {
                char *xs = gensym();
                char *i = gensym();

                next();

                e->type = EXPRESSION_SUBSCRIPT;
                xF(e, container) = mkid(xs);
                xF(e, subscript) = mkid(i);
                SYNTH(xF(e, container), bracket);
                SYNTH(xF(e, subscript), bracket);
                e->start = bracket;
                e->end = TEnd;

                Expr *f = mkfunc(ty);
                rvP(xF(f, params), i);
                rvP(xF(f, dflts), NULL);
                rvP(xF(f, constraints), NULL);
                xF(f, body) = mkret(ty, e);
                f->start = bracket;
                f->end = TEnd;

                Stmt *def = mkstmtx(DEFINITION);
                sF(def, pub) = false;
                sF(def, target) = mkid(xs);
                SYNTH(sF(def, target), left->start);
                sF(def, value) = left;
                def->start = left->start;
                def->end = left->end;

                Stmt *multi = mkstmtx(MULTI);
                rvP(sF(multi, statements), def);
                rvP(sF(multi, statements), to_stmt(f));
                multi->start = left->start;
                multi->end = TEnd;
                SYNTHETIC(multi);
                SYNTHETIC(def);
                SYNTHETIC(f);

                record_sugar(ty, "subscript-section", left->start, TEnd);

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
                xF(e, container) = left;
                xF(e, subscript) = i;
                goto End;
        }

        consume(';');

        e->type = EXPRESSION_SLICE;
        xF(e, slice).e = left;
        xF(e, slice).i = i;
        xF(e, slice).j = NULL;
        xF(e, slice).k = NULL;

        if (T0 != ']' && T0 != ';') {
                xF(e, slice).j = parse_expr(ty, 0);
        }

        if (T0 == ']') {
                goto End;
        }

        consume(';');

        if (T0 != ']') {
                xF(e, slice).k = parse_expr(ty, 0);
        }

End:
        consume(']');

        e->end = TEnd;

        return e;
}

static Expr *
infix_safe_subscript(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(SAFE_SUBSCRIPT);

        e->start = left->start;

        consume('[');

        xF(e, container) = left;
        xF(e, subscript) = parse_expr(ty, 0);

        consume(']');

        e->end = TEnd;

        return e;
}

static Expr *
infix_as(Ty *ty, Expr *left)
{
        consume_kw(AS);

        Expr *cast = mkxpr(CAST);
        xF(cast, left) = left;
        xF(cast, right) = parse_type(ty, 1);
        cast->start = left->start;
        cast->end = TEnd;

        return cast;
}

static Expr *
infix_member_access(Ty *ty, Expr *left)
{
        bool maybe = (T0 == TOKEN_DOT_MAYBE);

        next();

        if (maybe && T0 == '[') {
                return infix_safe_subscript(ty, left);
        }

        Expr *e = mkxpr(MEMBER_ACCESS);

        e->start = left->start;
        xF(e, maybe) = maybe;

        /*
         * xs.N is syntactic sugar for xs[N]
         */
        if (T0 == TOKEN_INTEGER) {
                e->type = EXPRESSION_SUBSCRIPT;
                xF(e, container) = left;
                xF(e, subscript) = mkxpr(INTEGER);
                xF(xF(e, subscript), integer) = tok()->integer;
                next();
                e->start = left->start;
                e->end = TEnd;
                return e;
        }

        xF(e, object) = left;

        if (AllowErrors && LocLine(tok()->start) > LocLine(TEnd)) {
                xF(e, member) = mkid("");
                xF(e, member)->start = TEnd;
                xF(e, member)->end = TEnd;
                e->end = TEnd;
                return e;
        }

        if (tok()->type == '{') {
                next();
                xF(e, member) = parse_expr(ty, 1);
                consume('}');
                e->type = EXPRESSION_DYN_MEMBER_ACCESS;
        } else {
                xF(e, member) = parse_member(ty);
                TagTokenOf(ty, xF(e, member), TT_MEMBER);
        }

        if (
                !have_without_nl(ty, '(')
             && !have_without_nl(ty, '$')
             && !have_without_nl(ty, '@')
        ) {
                e->end = TEnd;
                return e;
        } else {
                e->type = (e->type == EXPRESSION_MEMBER_ACCESS)
                        ? EXPRESSION_METHOD_CALL
                        : EXPRESSION_DYN_METHOD_CALL;
                TagTokenOf(ty, xF(e, member), TT_FUNC);
                return parse_method_call(ty, e);
        }
}

static Expr *
infix_squiggly_not_nil_arrow(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(NOT_NIL_VIEW_PATTERN);

        consume('$~>');

        xF(e, left) = left;
        xF(e, right) = parse_expr(ty, 0);
        e->start = left->start;
        e->end = TEnd;

        return e;
}

static Expr *
infix_squiggly_arrow(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(VIEW_PATTERN);

        consume(TOKEN_SQUIGGLY_ARROW);

        xF(e, left) = left;
        xF(e, right) = parse_expr(ty, 0);
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
                xF(e, left) = left;
                xF(e, right) = parse_expr(ty, 0);
                e->start = left->start;
                e->end = TEnd;
                return e;
        }

        e = mkfunc(ty);
        e->start = left->start;

        xF(e, proto) = clone_span_a(ty, LocS(left->start), LocS(left->end));

        if (
                (left->type != EXPRESSION_LIST)
             && (
                        (left->type != EXPRESSION_TUPLE)
                     || !xF(left, only_identifiers)
                )
            ) {
                Expr *l = mkxpr(LIST);
                rvP(xF(l, es), left);
                l->start = left->start;
                l->end = left->end;
                left = l;
        } else {
                left->type = EXPRESSION_LIST;
        }

        Stmt *body = mkstmtx(BLOCK);
        body->start = left->start;

        for (int i = 0; i < xF(left, es).count; ++i) {
                Expr *p = xF(left, es).items[i];
                Expr *dflt = NULL;
                if (p->type == EXPRESSION_EQ) {
                        dflt = xF(p, value);
                        p = xF(p, target);
                }
                if (p->type == EXPRESSION_IDENTIFIER) {
                        rvP(xF(e, params), xF(p, identifier));
                        rvP(xF(e, constraints), xF(p, constraint));
                } else if (p->type == EXPRESSION_MATCH_REST) {
                        rvP(xF(e, params), xF(p, identifier));
                        rvP(xF(e, constraints), xF(p, constraint));
                        xF(e, rest) = i;
                } else {
                        char *name = gensym();
                        rvP(xF(e, params), name);
                        rvP(xF(e, constraints), NULL);
                        rvP(sF(body, statements), mkdef(ty, definition_lvalue(ty, p), name));
                }
                rvP(xF(e, dflts), dflt);
        }

        Stmt *last = to_stmt(parse_expr(ty, 0));

        if (sF(body, statements).count == 0) {
                xF(e, body) = last;
        } else {
                rvP(sF(body, statements), last);
                xF(e, body) = body;
        }

        e->end = body->end = TEnd;

        if (vN(sF(body, statements)) > 1) {
                SYNTHETIC(body);
                record_sugar(ty, "destructuring-params", e->start, e->end);
        }

        return e;
}

static Expr *
infix_identifier(Ty *ty, Expr *left)
{
        Expr *op = mkid(tok()->identifier);

        next();

        Expr *right = parse_expr(ty, 9);

        Expr *call = mkcall(ty, op);

        rvP(xF(call, args), left);
        rvP(xF(call, fconds), NULL);

        rvP(xF(call, args), right);
        rvP(xF(call, fconds), NULL);

        call->start = left->start;
        call->end = right->end;

        record_sugar(ty, "infix-call", call->start, call->end);

        return call;
}

static Expr *
infix_kw_or(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(CHOICE_PATTERN);


        rvP(xF(e, es), left);

        while (try_consume(KEYWORD_OR)) {
                rvP(xF(e, es), parse_expr(ty, 1));
        }

        e->start = left->start;
        e->end = TEnd;

        return e;
}

static Expr *
infix_kw_and(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(KW_AND);

        xF(e, left) = left;
        e->start = left->start;

        consume_kw(AND);

        xF(e, p_cond) = parse_condparts(ty, &(bool){false});

        e->end = TEnd;

        return e;
}

static Expr *
infix_kw_in(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(NOT_IN);
        xF(e, left) = left;
        e->start = left->start;

        if (K0 == KEYWORD_NOT) {
                next();
                e->type = EXPRESSION_NOT_IN;
        } else {
                e->type = EXPRESSION_IN;
        }

        consume_kw(IN);

        xF(e, right) = parse_expr(ty, 6);
        e->end = xF(e, right)->end;

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
        Location start = tok()->start;

        next();

        Location end = TEnd;

        next();

        Expr *body = parse_expr(ty, 0);

        Expr *nil = mkxpr(NIL);
        nil->start = start;
        nil->end = end;

        Expr *f = mkcall(ty, nil);
        rvP(xF(f, args), body);
        rvP(xF(f, fconds), NULL);

        Expr *call = mkcall(ty, left);

        next();

        f->end = call->end = TEnd;
        SYNTHETIC(f);
        SYNTHETIC(nil);

        rvP(xF(call, args), mkpartial(ty, f));
        rvP(xF(call, fconds), NULL);

        return call;
}

static Expr *
infix_conditional(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(CONDITIONAL);

        xF(e, cond) = left;
        e->start = left->start;

        consume(TOKEN_QUESTION);

        SAVE_NC(true);
        if (T0 != ':') {
                xF(e, then) = parse_expr(ty, 2);
                consume(':');
                xF(e, _else) = parse_expr(ty, 2);
        } else {
                consume(':');
                xF(e, then) = parse_expr(ty, 2);
                xF(e, _else) = mkxpr(NIL);
                SYNTH(xF(e, _else), TEnd);
        }
        LOAD_NC();

        e->end = TEnd;

        return e;
}

static Expr *
postfix_inc(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(POSTFIX_INC);
        e->start = left->start;

        consume(TOKEN_INC);

        xF(e, operand) = assignment_lvalue(ty, left);
        e->end = TEnd;

        return e;
}

static Expr *
postfix_dec(Ty *ty, Expr *left)
{
        Expr *e = mkxpr(POSTFIX_DEC);
        e->start = left->start;

        consume(TOKEN_DEC);

        xF(e, operand) = assignment_lvalue(ty, left);
        e->end = TEnd;

        return e;
}

static Expr *
postfix_bang(Ty *ty, Expr *left)
{
        next();

        left->bang = true;
        left->end = TEnd;

        return left;
}

BINARY_OPERATOR(star,         STAR,        9, false)
BINARY_OPERATOR(div,          DIV,         9, false)
BINARY_OPERATOR(percent,      PERCENT,     9, false)
BINARY_OPERATOR(plus,         PLUS,        8, false)
BINARY_OPERATOR(minus,        MINUS,       8, false)
BINARY_OPERATOR(dot_dot,      DOT_DOT,     7, false)
BINARY_OPERATOR(dot_dot_dot,  DOT_DOT_DOT, 7, false)
BINARY_OPERATOR(lt,           LT,          7, false)
BINARY_OPERATOR(gt,           GT,          7, false)
BINARY_OPERATOR(geq,          GEQ,         7, false)
BINARY_OPERATOR(leq,          LEQ,         7, false)
BINARY_OPERATOR(cmp,          CMP,         7, false)
BINARY_OPERATOR(not_eq,       NOT_EQ,      6, false)
BINARY_OPERATOR(dbl_eq,       DBL_EQ,      6, false)
BINARY_OPERATOR(and,          AND,         5, false)
BINARY_OPERATOR(xor,          XOR,         5, false)
BINARY_OPERATOR(shl,          SHL,         7, false)
BINARY_OPERATOR(shr,          SHR,         7, false)
BINARY_OPERATOR(bit_and,      BIT_AND,     5, false)
BINARY_OPERATOR(bit_or,       BIT_OR,      5, false)
BINARY_OPERATOR(or,           OR,          4, false)
BINARY_OPERATOR(wtf,          WTF,         4, false)
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
        case TOKEN_INTEGER:             return prefix_integer;
        case TOKEN_REAL:                return prefix_real;
        case TOKEN_STRING:              return prefix_string;
        case TOKEN_REGEX:               return prefix_regex;
        case TOKEN_UNTERMINATED_REGEX:  return prefix_unterminated_regex;
        case TOKEN_INVALID_REGEX_FLAGS: return prefix_invalid_regex_flags;

        case '"':                       return prefix_ss;
        case TOKEN_DYN_REGEX:           return prefix_dyn_regex;

        case TOKEN_IDENTIFIER:          return prefix_identifier;
        case TOKEN_KEYWORD:             goto Keyword;

        case '&':                       return prefix_implicit_method;
        case TOKEN_PERCENT:             return prefix_percent;
        case '#':                       return prefix_hash;

        case TOKEN_DICT_OPEN:           return prefix_dict;
        case TOKEN_SET_OPEN:            return prefix_set;
        case '(':                       return prefix_parenthesis;
        case '[':                       return prefix_array;
        case '{':                       return prefix_record;

        case '\\':                      return prefix_slash;
        case '$':                       return prefix_dollar;
        case '^':                       return prefix_carat;
        case '>':                       return prefix_greater;
        case '<':                       return prefix_tyx;

        case TOKEN_TEMPLATE_BEGIN:      return prefix_template;
        case '$$':                      return prefix_template_expr;

        case TOKEN_DOT_DOT:             return prefix_dot_dot;
        case TOKEN_DOT_DOT_DOT:         return prefix_dot_dot_dot;

        case TOKEN_QUESTION:            return prefix_is_nil;
        case TOKEN_BANG:                return prefix_bang;
        case '@':                       return prefix_at;
        case TOKEN_MINUS:               return prefix_minus;
        case TOKEN_INC:                 return prefix_inc;
        case TOKEN_DEC:                 return prefix_dec;
        case TOKEN_USER_OP:             return prefix_user_op;
        case '~':                       return prefix_complement;

        case TOKEN_ARROW:               return prefix_arrow;

        case '|':                       return prefix_bit_or;

        case TOKEN_STAR:                return prefix_star;

        case TOKEN_EXPRESSION:          return prefix_expr;

        default:                        return NULL;
        }

Keyword:

        switch (K0) {
        case KEYWORD_MATCH:     return prefix_match;
        case KEYWORD_FUNCTION:  return prefix_function;
        case KEYWORD_GENERATOR: return prefix_function;
        case KEYWORD_JIT:       return prefix_assert_jit;
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
        case KEYWORD_DBG:       return prefix_dbg;

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
        case '{':                  return infix_brace;
        case ',':                  return infix_list;
        case TOKEN_INC:            return postfix_inc;
        case TOKEN_DEC:            return postfix_dec;
        case '!':                  return postfix_bang;
        case TOKEN_ARROW:          return infix_arrow_function;
        case TOKEN_SQUIGGLY_ARROW: return infix_squiggly_arrow;
        case '$~>':                return infix_squiggly_not_nil_arrow;

        case TOKEN_DOT_DOT:        return no_rhs(ty, 1) ? infix_count_from : infix_dot_dot;
        case TOKEN_DOT_DOT_DOT:    return no_rhs(ty, 1) ? infix_count_from : infix_dot_dot_dot;

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
        case '@':      return next_without_nl(ty, '(') ? infix_at     : NULL;

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
        case '!':
                return true;
        default:
                return false;
        }
}

static int
get_infix_prec(Ty *ty)
{
        Value *p;

        setctx(LEX_INFIX);

        switch (T0) {
        case '.':
        case TOKEN_DOT_MAYBE:      return 12;

        case '[':                  return 11;
        case '(':                  return 11;

        case '{':
                return (LocS(tok()->start) == LocS(token(-1)->end)) ? 11 : -3;

        case '\\':
        case '@':
                return next_without_nl(ty, '(') ? 11 : -3;

        case TOKEN_INC:
        case TOKEN_DEC:
                return (LocSameLine(tok()->start, token(-1)->end)) ?  10 : -3;

        case TOKEN_DIV:            return 9;
        case TOKEN_STAR:           return 9;
        case TOKEN_PERCENT:        return 9;

        case TOKEN_IDENTIFIER:
                return (tok()->raw && LocSameLine(tok()->start, token(-1)->end))
                     ?  9
                     : -3;

        case TOKEN_MINUS:          return 8;
        case TOKEN_PLUS:           return 8;

        case TOKEN_DOT_DOT:        return 7;
        case TOKEN_DOT_DOT_DOT:    return 7;

        case TOKEN_CMP:            return 7;
        case TOKEN_GEQ:            return 7;
        case TOKEN_LEQ:            return 7;

        case TOKEN_GT:
        case TOKEN_LT:
                return (LocSameLine(tok()->start, token(-1)->end)) ? 7 : -3;

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

        case '$~>':                return 3;
        case TOKEN_SQUIGGLY_ARROW: return 3;
        case TOKEN_CHECK_MATCH:    return 3;

        case TOKEN_QUESTION:       return 3;
        case TOKEN_ELVIS:          return 3;

        case '!':
                return have_without_nl(ty, '!') ? 3 : -3;

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
        case KEYWORD_OR:  return NoAndOr ? -3 : 2;
        case KEYWORD_AND: return NoAndOr ? -3 : 4;

        case KEYWORD_NOT:
        case KEYWORD_IN:  return NoIn ? -3 : 6;

        case KEYWORD_AS:  return 1;

        default:          return -3;
        }

UserOp:
        if (NoLG && s_eq(tok()->operator, "</")) {
                return -3;
        }
        p = table_look(ty, &uops, tok()->operator);
        return (p != NULL) ? llabs(p->z) : 8;
}

static Expr *
wildcard(Expr *e)
{
        if (
                (xF(e, module) == NULL)
             && (xF(e, constraint) == NULL)
             && s_eq(xF(e, identifier), "_")
        ) {
                e->type = EXPRESSION_MATCH_ANY;
        }

        return e;
}

static Expr *
definition_lvalue(Ty *ty, Expr *e)
{
        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                wildcard(e);
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
        case EXPRESSION_TEMPLATE:
                return template_pattern(ty, e);
        case EXPRESSION_REF_PATTERN:
                xF(e, target) = assignment_lvalue(ty, xF(e, target));
                return e;
        case EXPRESSION_LIST:
        case EXPRESSION_CHOICE_PATTERN:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < xF(e, es).count; ++i) {
                        xF(e, es).items[i] = definition_lvalue(ty, xF(e, es).items[i]);
                }
                return e;
        case EXPRESSION_FUNCTION_CALL:
                for (int i = 0; i < xF(e, args).count; ++i) {
                        xF(e, args).items[i] = definition_lvalue(ty, xF(e, args).items[i]);
                }
                return e;
        case EXPRESSION_METHOD_CALL:
                if (xF(e, object)->type != EXPRESSION_IDENTIFIER) {
                        break;
                }
                for (int i = 0; i < xF(e, method_args).count; ++i) {
                        xF(e, method_args).items[i] = definition_lvalue(ty, xF(e, method_args).items[i]);
                }
                for (int i = 0; i < xF(e, method_kwargs).count; ++i) {
                        xF(e, method_kwargs).items[i] = definition_lvalue(ty, xF(e, method_kwargs).items[i]);
                }
                return e;
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                xF(e, right) = definition_lvalue(ty, xF(e, right));
                return e;
        case EXPRESSION_ARRAY:
                for (int i = 0; i < vN(xF(e, elements)); ++i) {
                        *v_(xF(e, elements), i) = definition_lvalue(ty, *v_(xF(e, elements), i));
                }
                return e;
        case EXPRESSION_DICT:
                if (xF(e, keys).count == 0)
                        break;
                for (usize i = 0; i < xF(e, elements).count; ++i) {
                        if (xF(e, values).items[i] == NULL) {
                                Expr *key = mkxpr(STRING);
                                if (xF(e, keys).items[i]->type != EXPRESSION_IDENTIFIER) {
                                        EStart = xF(e, keys).items[i]->start;
                                        EEnd = xF(e, keys).items[i]->end;
                                        die("shorthand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                xF(key, string).data = xF(xF(e, keys).items[i], identifier);
                                xF(key, string).length = strlen(xF(key, string).data);
                                xF(e, values).items[i] = xF(e, keys).items[i];
                                xF(e, keys).items[i] = key;
                        }
                        xF(e, values).items[i] = definition_lvalue(ty, xF(e, values).items[i]);
                }
                return e;
        }

        die_at(e, "expression is not a valid definition lvalue: %s", ExpressionTypeName(e));
}

static Expr *
patternize(Ty *ty, Expr *e)
{
        Expr *syn = syn_view_pattern(ty, e);
        if (syn != NULL) {
                return syn;
        }

        try_symbolize_application(ty, NULL, e);

        switch (e->type) {
        case EXPRESSION_IDENTIFIER:
                return wildcard(e);

        case EXPRESSION_TAG_APPLICATION:
                xF(e, tagged) = patternize(ty, xF(e, tagged));
                return e;

        case EXPRESSION_LIST:
                e->type = EXPRESSION_CHOICE_PATTERN;
        case EXPRESSION_TUPLE:
        case EXPRESSION_CHOICE_PATTERN:
                for (int i = 0; i < vN(xF(e, es)); ++i) {
                        *v_(xF(e, es), i) = patternize(ty, v__(xF(e, es), i));
                }
                return e;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < vN(xF(e, elements)); ++i) {
                        *v_(xF(e, elements), i) = patternize(ty, v__(xF(e, elements), i));
                }
                return e;

        case EXPRESSION_DICT:
                for (usize i = 0; i < vN(xF(e, keys)); ++i) {
                        Expr *k = v__(xF(e, keys), i);
                        if (v__(xF(e, values), i) == NULL) {
                                Expr *key = mkxpr(STRING);
                                if (k->type != EXPRESSION_IDENTIFIER) {
                                        EStart = key->start;
                                        EEnd = key->end;
                                        die("short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                xF(key, string).data = xF(k, identifier);
                                xF(key, string).length = strlen(xF(key, string).data);
                                *v_(xF(e, values), i) = k;
                                *v_(xF(e, keys), i) = key;
                        }
                        *v_(xF(e, values), i) = patternize(ty, v__(xF(e, values), i));
                }
                return e;

        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
                xF(e, right) = patternize(ty, xF(e, right));
                return e;

        case EXPRESSION_ALIAS_PATTERN:
                xF(e, aliased) = patternize(ty, xF(e, aliased));
                return e;

        case EXPRESSION_CAST:
        {
                Expr *alias  = xF(e, right);
                Expr *alised = xF(e, left);

                if (alias->type == EXPRESSION_IDENTIFIER) {
                        ZERO_EXPR(e);
                        e->type = EXPRESSION_ALIAS_PATTERN;
                        xF(e, identifier) = xF(alias, identifier);
                        xF(e, aliased) = patternize(ty, alised);
                }

                return e;
        }

        case EXPRESSION_KW_AND:
                xF(e, left) = patternize(ty, xF(e, left));
                return e;

        case EXPRESSION_TEMPLATE:
                return template_pattern(ty, e);

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
                if (strcmp(xF(e, identifier), "_") == 0 && xF(e, module) == NULL) {
                        // TODO: ??
                        // e->type = EXPRESSION_MATCH_ANY;
                }
                /* fallthrough */
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_SUBSCRIPT:
        case EXPRESSION_TAG_APPLICATION:
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_DYN_MEMBER_ACCESS:
        case EXPRESSION_FUNCTION_CALL:
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
        case EXPRESSION_SPREAD:
        case EXPRESSION_TEMPLATE_HOLE:
        case EXPRESSION_TEMPLATE_XHOLE:
                return e;

        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(xF(e, es)); ++i) {
                        *v_(xF(e, es), i) = assignment_lvalue(ty, v__(xF(e, es), i));
                }
                return e;

        case EXPRESSION_ARRAY:
                for (usize i = 0; i < vN(xF(e, elements)); ++i) {
                        *v_(xF(e, elements), i) = assignment_lvalue(ty, v__(xF(e, elements), i));
                }
                return e;

        case EXPRESSION_DICT:
                for (usize i = 0; i < vN(xF(e, keys)); ++i) {
                        Expr *k = v__(xF(e, keys), i);
                        if (v__(xF(e, values), i) == NULL) {
                                Expr *key = mkxpr(STRING);
                                if (k->type != EXPRESSION_IDENTIFIER) {
                                        EStart = key->start;
                                        EEnd = key->end;
                                        die("short-hand target in dict lvalue must be an identifier");
                                }
                                key->type = EXPRESSION_STRING;
                                xF(key, string).data = xF(k, identifier);
                                xF(key, string).length = strlen(xF(key, string).data);
                                *v_(xF(e, values), i) = k;
                                *v_(xF(e, keys), i) = key;
                        }
                        *v_(xF(e, values), i) = assignment_lvalue(ty, v__(xF(e, values), i));
                }
                return e;

        case EXPRESSION_REF_PATTERN:
                xF(e, target) = assignment_lvalue(ty, xF(e, target));
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
                vec_init(xF(l, es));
                rvP(xF(l, es), e);
                while (T0 == ',') {
                        next();
                        Expr *e = parse_definition_lvalue(ty, LV_SUB, NULL);
                        if (e == NULL) {
                                die("expected lvalue but found %s", token_show(ty, tok()));
                        }
                        rvP(xF(l, es), e);
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
                if (T0 != ',' && T0 != ';')
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
parse_target(Ty *ty)
{
        SAVE_NI(true);
        SAVE_NE(true);
        SAVE_NC(false);

        Expr *target = parse_expr(ty, 0);

        LOAD_NC();
        LOAD_NE();
        LOAD_NI();

        return target;
}

static Expr *
parse_target_list_from(Ty *ty, Expr *target)
{
        if (T0 != ',' && T0 != ';' && !have_kw(IN)) {
                return target;
        }

        Expr *e = mkxpr(LIST);
        Expr *item = parse_definition_lvalue(ty, LV_EACH, target);

        if (item == NULL) {
        Error:
                die("expected lvalue in for-each loop");
        }

        if (T0 == ',') {
                Expr *tuple = mkxpr(TUPLE);
                tuple->start = item->start;

                for (;;) {
                        rvP(xF(tuple, es), item);
                        rvP(xF(tuple, names), NULL);
                        rvP(xF(tuple, required), true);
                        rvP(xF(tuple, tconds), NULL);

                        if (T0 != ',') {
                                break;
                        }

                        next();

                        item = parse_definition_lvalue(ty, LV_EACH, NULL);
                        if (item == NULL) {
                                goto Error;
                        }
                }

                tuple->end = item->end;
                item = tuple;
        }

        rvP(xF(e, es), item);

        if (T0 == ';') {
                next();

                target = parse_definition_lvalue(ty, LV_EACH, NULL);
                if (target == NULL || !have_kw(IN)) {
                        goto Error;
                }

                rvP(xF(e, es), target);
        }

        e->start = v__(xF(e, es), 0)->start;
        e->end   = vvL(xF(e, es))[0]->end;

        return e;
}

static Expr *
parse_target_list(Ty *ty)
{
        return parse_target_list_from(ty, parse_target(ty));
}

inline static bool
have_index_header(Ty *ty)
{
        return (T0 == ';')
            && (T1 == TOKEN_IDENTIFIER)
            && (token(2)->type == TOKEN_KEYWORD)
            && (token(2)->keyword == KEYWORD_IN);
}

static Stmt *
parse_for_loop(Ty *ty)
{
        Stmt *s = mkstmtx(FOR_LOOP);

        consume_kw(FOR);

        bool match = try_consume(KEYWORD_MATCH);

        Expr *target = NULL;
        Expr *array = NULL;
        Stmt *init = NULL;
        bool c_style = false;
        bool parens = false;
        bool have_init = false;

        if (match) {
                ;
        } else if (T0 == ';' || (T0 == TOKEN_KEYWORD && get_prefix_parser(ty) == NULL)) {
                c_style = true;
        } else {
                ForParen = TokenIndex + 1;
                ForInit  = false;

                target = parse_target(ty);

                ForParen = 0;

                if (ForInit) {
                        ForInit   = false;
                        c_style   = true;
                        parens    = true;
                        have_init = (ForInitExpr != NULL);
                        init      = have_init ? to_stmt(ForInitExpr) : NULL;
                } else if (T0 == TOKEN_EQ || T0 == TOKEN_MAYBE_EQ) {
                        SAVE_NA(true);
                        target = infix_eq(ty, target);
                        LOAD_NA();
                        c_style   = true;
                        have_init = true;
                        init      = to_stmt(target);
                } else if (have_index_header(ty)) {
                        int save = TokenIndex;
                        Expr *list = parse_target_list_from(ty, target);
                        consume_kw(IN);
                        array = parse_expr(ty, 0);
                        if (T0 == ';') {
                                seek(ty, save);
                                array     = NULL;
                                c_style   = true;
                                have_init = true;
                                init      = to_stmt(target);
                        } else {
                                target = list;
                        }
                } else if (T0 == ';') {
                        c_style   = true;
                        have_init = true;
                        init      = to_stmt(target);
                }
        }

        if (!c_style) {
                s->type = STATEMENT_EACH_LOOP;

                if (match) {
                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_IN;

                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = gensym();
                        tok()->module = NULL;

                        sF(s, each).target = parse_target_list(ty);
                } else if (array != NULL) {
                        sF(s, each).target = target;
                } else {
                        sF(s, each).target = parse_target_list_from(ty, target);
                }

                if (array != NULL) {
                        sF(s, each).array = array;
                } else if (sF(s, each).target->type != EXPRESSION_LIST) {
                        iter_sugar(ty, &sF(s, each).target, &sF(s, each).array);
                } else {
                        consume_kw(IN);
                        sF(s, each).array = parse_expr(ty, 0);
                }

                if (T0 == TOKEN_KEYWORD && K0 == KEYWORD_IF) {
                        next();
                        sF(s, each)._if = parse_expr(ty, 0);
                } else {
                        sF(s, each)._if = NULL;
                }

                if (T0 == TOKEN_KEYWORD && K0 == KEYWORD_WHILE) {
                        next();
                        sF(s, each)._while = parse_expr(ty, 0);
                } else {
                        sF(s, each)._while = NULL;
                }

                Location brace = tok()->start;

                if (match) {
                        Expr *subject = AstClone(v__(xF(sF(s, each).target, es), 0));
                        SYNTH(subject, brace);

                        unconsume(TOKEN_EXPRESSION);
                        tok()->e = subject;

                        unconsume(TOKEN_KEYWORD);
                        tok()->keyword = KEYWORD_MATCH;
                }

                bool implicit = (sF(s, each).array != NULL)
                             && (sF(s, each).target != NULL)
                             && (sF(s, each).target->start.byte == sF(s, each).target->end.byte);

                sF(s, each).body = parse_statement(ty, -1);
                s->end = TEnd;

                if (match) {
                        sF(s, each).body->start = brace;
                        record_sugar(ty, "for-match", s->start, s->end);
                } else if (implicit) {
                        record_sugar(ty, "implicit-it", s->start, s->end);
                }

                return s;
        }

        if (have_init) {
                consume(';');
                sF(s, for_loop).init = init;
        } else {
                parens = parens || try_consume('(');
                if (!try_consume(';')) {
                        sF(s, for_loop).init = parse_statement(ty, -1);
                }
        }

        if (T0 != ';') {
                sF(s, for_loop).cond = parse_expr(ty, 0);
        }

        consume(';');

        if (T0 != ')') {
                sF(s, for_loop).next = parse_expr(ty, 0);
        }

        if (parens) {
                consume(')');
        }

        expect('{');
        sF(s, for_loop).body = parse_statement(ty, -1);
        s->end = TEnd;

        return s;
}

static struct condpart *
parse_condpart(Ty *ty)
{
        struct condpart *p = amA(sizeof *p);
        p->e = NULL;
        p->target = NULL;
        p->def = false;
        p->start = tok()->start;

        if (try_consume(KEYWORD_LET)) {
                p->def = true;
                p->target = parse_definition_lvalue(ty, LV_LET, NULL);
                consume(TOKEN_EQ);
                SAVE_NA(true);
                p->e = parse_expr(ty, -1);
                LOAD_NA();
                p->end = TEnd;
                record_extra(ty, "Condition", "let", p->start, p->end);
                return p;
        }

        SAVE_NE(true);
        Expr *e = parse_expr(ty, 0);
        LOAD_NE();

        if (try_consume('=')) {
                p->target = e;
                p->e = parse_expr(ty, -1);
                p->end = TEnd;
                record_extra(ty, "Condition", "match", p->start, p->end);
        } else {
                p->e = e;
                p->end = TEnd;
        }

        return p;
}

static condpart_vector
parse_condparts(Ty *ty, bool *negp)
{
        condpart_vector parts = {0};

        SAVE_NA(true);

        struct condpart *first = parse_condpart(ty);

        if (*negp && first->target == NULL) {
                Expr *not = mkxpr(PREFIX_BANG);
                xF(not, operand) = first->e;
                not->start = first->e->start;
                not->end = first->e->end;
                first->e = not;
                *negp = false;
        }

        bool neg = *negp;

        rvP(parts, first);

        while ((!neg && have_kw(AND)) ||
               (neg && have_kw(OR))) {

                next();

                Location kw = tok()->start;
                bool not = have_kw(NOT);
                if (not) {
                        next();
                }

                struct condpart *part = parse_condpart(ty);

                if (part->target != NULL && neg != not) {
                        die("illegal condition used as controlling expression of if statement");
                }

                if (not && part->target == NULL) {
                        Expr *not = mkxpr(PREFIX_BANG);
                        xF(not, operand) = part->e;
                        not->start = kw;
                        not->end = part->e->end;
                        part->e = not;
                }

                rvP(parts, part);
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
        if (have_kws(WHILE, MATCH)) {
                next();
                Stmt *m = parse_match_statement(ty);
                m->type = STATEMENT_WHILE_MATCH;
                m->start = start;
                return m;
        }

        Stmt *s = mkstmtx(WHILE);

        consume_kw(WHILE);

        vec_init(sF(s, _while).parts);

        SAVE_NA(true);

        rvP(sF(s, _while).parts, parse_condpart(ty));

        while (have_kw(AND)) {
                next();
                rvP(sF(s, _while).parts, parse_condpart(ty));
        }

        LOAD_NA();

        sF(s, _while).block = parse_block(ty);

        s->end = TEnd;

        return s;
}

static Stmt *
parse_if(Ty *ty)
{

        Stmt *s = mkstmtx(IF);

        consume_kw(IF);

        sF(s, _if).neg   = try_consume(KEYWORD_NOT);
        sF(s, _if).parts = parse_condparts(ty, &sF(s, _if).neg);

        sF(s, _if).then  = parse_statement(ty, -1);

        if (have_kw(ELSE)) {
                next();
                sF(s, _if)._else = parse_statement(ty, -1);
        } else {
                sF(s, _if)._else = NULL;
        }

        s->end = TEnd;

        return s;
}

static Stmt *
parse_match_statement(Ty *ty)
{
        Stmt *s = mkstmtx(MATCH);

        consume_kw(MATCH);

        sF(s, match).e = parse_expr(ty, -1);

        if (!CatchError()) {
                consume('{');
                SAVE_NA(false);
                while (T0 != '}') {
                        rvP(sF(s, match).patterns, parse_pattern(ty));
                        consume(TOKEN_FAT_ARROW);
                        rvP(sF(s, match).statements, parse_statement(ty, 0));
                        try_consume(',');
                }
                LOAD_NA();
                consume('}');
                EndCatch();
        }

        if (vN(sF(s, match).patterns) > vN(sF(s, match).statements)) {
                vN(sF(s, match).patterns) = vN(sF(s, match).statements);
        }

        s->end = TEnd;

        return s;
}

inline static bool
have_wildcard_arm(Ty *ty)
{
        return (T0 == TOKEN_IDENTIFIER)
            && (tok()->module == NULL)
            && s_eq(tok()->identifier, "_")
            && (T1 == TOKEN_FAT_ARROW);
}

static Stmt *
parse_match_cond_arm(Ty *ty, bool expr)
{
        consume(TOKEN_FAT_ARROW);
        return expr ? to_stmt(parse_expr(ty, 0)) : parse_statement(ty, 0);
}

static Stmt *
parse_match_cond(Ty *ty, bool expr)
{
        Location start = tok()->start;
        Stmt *chain = NULL;
        Stmt **tail = &chain;
        Stmt *arm;
        bool loop;

        consume_kw(MATCH);

        loop = have_kw(WHILE);
        next();

        consume('{');
        SAVE_NA(false);

        while (T0 != '}') {
                if (have_wildcard_arm(ty)) {
                        next();
                        *tail = parse_match_cond_arm(ty, expr);
                        try_consume(',');
                        goto Done;
                }

                arm = mkstmtx(IF);
                sF(arm, _if).neg   = try_consume(KEYWORD_NOT);
                sF(arm, _if).parts = parse_condparts(ty, &sF(arm, _if).neg);
                sF(arm, _if).then  = parse_match_cond_arm(ty, expr);
                sF(arm, _if)._else = NULL;

                *tail = arm;
                tail  = &sF(arm, _if)._else;

                try_consume(',');
        }

        if (loop) {
                *tail = mkstmtx(BREAK);
                sF((*tail), depth)      = 1;
                sF((*tail), expression) = NULL;
                SYNTH(*tail, TEnd);
        }

Done:
        LOAD_NA();
        consume('}');

        if (chain == NULL) {
                chain = mkstmtx(NULL);
        }

        for (arm = chain; arm != NULL && arm->type == STATEMENT_IF; arm = sF(arm, _if)._else) {
                arm->end = TEnd;
        }

        if (loop) {
                struct condpart *forever = amA(sizeof *forever);
                *forever = (struct condpart) {
                        .e     = mkxpr(BOOLEAN),
                        .start = start,
                        .end   = start
                };
                xF(forever->e, boolean) = true;
                SYNTH(forever->e, start);

                arm = mkstmtx(WHILE);
                vec_init(sF(arm, _while).parts);
                rvP(sF(arm, _while).parts, forever);
                sF(arm, _while).block = chain;
                chain = arm;
        }

        chain->start = start;
        chain->end   = TEnd;

        record_sugar(ty, loop ? "match-while" : "match-if", start, TEnd);

        return chain;
}

static Stmt *
parse_function_definition(Ty *ty)
{
        Stmt *s = mkstmtx(FUNCTION_DEFINITION);

        bool jit = try_consume(KEYWORD_JIT);

        if (K0 == KEYWORD_MACRO) {
                Token kw = *token(0);
                consume(TOKEN_KEYWORD);

                op_fixup(ty, 0);

                Token name = *token(0);
                consume(TOKEN_IDENTIFIER, TT_MACRO);

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

        sF(s, pub) = try_consume(KEYWORD_PUB);

        expect_one_of(KEYWORD_FUNCTION, KEYWORD_MACRO);

        Expr *target     = NULL;
        bool is_operator = false;

        Expr *func = parse_function(ty, &target, &is_operator);

        if (target == NULL) {
                die("anonymous function definition appears in statement context");
        }

        if (func->type == EXPRESSION_FUNCTION) {
                xF(func, must_jit) = jit;
                if (is_operator) {
                        s->type = STATEMENT_OPERATOR_DEFINITION;
                }
                if (s->type == STATEMENT_MACRO_DEFINITION) {
                        rvI(xF(func, params), "self", 0);
                        rvI(xF(func, constraints), NULL, 0);
                        rvI(xF(func, dflts), NULL, 0);
                }
        } else {
                s->type = STATEMENT_DEFINITION;
        }

        sF(s, target) = target;
        sF(s, value) = func;

        return s;
}

static Stmt *
parse_operator_directive(Ty *ty)
{
        next();

        setctx(LEX_INFIX);

        expect(TOKEN_USER_OP);
        char const *uop = S2(tok()->identifier);
        next();

        expect(TOKEN_INTEGER);
        int p = tok()->integer;
        next();

        expect(TOKEN_IDENTIFIER);
        char const *assoc = tok()->identifier;
        next();

        if (strcmp(assoc, "left") == 0) {
                table_put(ty, &uops, uop, &INTEGER(p));
        } else if (strcmp(assoc, "right") == 0) {
                table_put(ty, &uops, uop, &INTEGER(-p));
        } else {
                die("expected 'left' or 'right' in operator directive");
        }

        if (T0 != TOKEN_NEWLINE) {
                Expr *e = parse_expr(ty, 0);
                table_put(ty, &uopcs, uop, &PTR(e));
        }

        consume(TOKEN_NEWLINE);

        return mkstmtx(NULL);
}

inline static Stmt *
try_conditional_from(Ty *ty, Stmt *s)
{
        if (LocSameLine(tok()->start, TEnd) && have_kw(IF)) {
                next();

                Stmt *_if = mkstmtx(IF);
                sF(_if, _if).neg = try_consume(KEYWORD_NOT);
                sF(_if, _if).parts = parse_condparts(ty, &sF(_if, _if).neg);
                sF(_if, _if).then = s;
                sF(_if, _if)._else = NULL;
                _if->start = s->start;
                _if->end = TEnd;

                s = _if;
        }

        return s;
}

static Stmt *
parse_return_statement(Ty *ty)
{
        Stmt *s = mkstmtx(RETURN);

        next();

        if (
                (LocSameLine(tok()->start, s->start))
             && (get_prefix_parser(ty) != NULL)
             && (!have_kw(IF) || (T0 == '('))
        ) {
                sF(s, ret) = parse_expr(ty, 0);
        }

        s->end = TEnd;

        s = try_conditional_from(ty, s);

        try_consume(';');

        return s;
}

static Stmt *
parse_let_definition(Ty *ty)
{
        Stmt *s = mkstmtx(DEFINITION);

        if (try_consume(KEYWORD_CONST)) {
                sF(s, cnst) = true;
        } else {
                expect_one_of(KEYWORD_LET, KEYWORD_WHERE);
                next();
        }

        SAVE_LC(true);
        sF(s, target) = parse_definition_lvalue(ty, LV_LET, NULL);
        if (sF(s, target) == NULL) {
                die("failed to parse lvalue in 'let' definition");
        }
        LOAD_LC();

        consume(TOKEN_EQ);

        SAVE_NA(true);
        sF(s, value) = parse_expr(ty, -1);
        LOAD_NA();

        s->end = TEnd;

        if (try_consume(KEYWORD_OR)) {
                struct condpart *let = amA(sizeof *let);
                let->target = sF(s, target);
                let->e      = sF(s, value);
                let->def    = true;
                Stmt *_if = mkstmtx(IF);
                sF(_if, _if).then  = parse_statement(ty, -1);
                sF(_if, _if)._else = NULL;
                sF(_if, _if).neg   = true;
                rvP(sF(_if, _if).parts, let);
                _if->start = s->start;
                _if->end   = TEnd;
                s = _if;
        }

        while (T0 == ';') {
                next();
        }

        return s;
}

static Stmt *
parse_defer_statement(Ty *ty)
{
        Stmt *s = mkstmtx(DEFER);

        consume_kw(DEFER);

        sF(s, expression) = mkfunc(ty);
        xF(sF(s, expression), body) = parse_statement(ty, -1);
        sF(s, expression)->start = xF(sF(s, expression), body)->start;
        sF(s, expression)->end = xF(sF(s, expression), body)->end;

        if (T0 == ';') {
                next();
        }

        s->end = TEnd;

        return s;
}

static Stmt *
parse_break_statement(Ty *ty)
{
        Stmt *s = mkstmtx(BREAK);

        sF(s, depth) = 0;

        while (have_kw(BREAK)) {
                next();
                sF(s, depth) += 1;
        }

        if (
                (LocSameLine(tok()->start, s->start))
             && get_prefix_parser(ty) != NULL
             && (!have_kw(IF) || (T0 == '('))
        ) {
                sF(s, expression) = parse_expr(ty, 0);
        } else {
                sF(s, expression) = NULL;
        }

        s->end = TEnd;

        s = try_conditional_from(ty, s);

        if (T0 == ';')
                consume(';');

        return s;
}

static Stmt *
parse_continue_statement(Ty *ty)
{
        Stmt *s = mkstmtx(CONTINUE);
        sF(s, depth) = 0;

        while (have_kw(CONTINUE)) {
                next();
                sF(s, depth) += 1;
        }

        s = try_conditional_from(ty, s);

        if (T0 == ';')
                next();

        return s;
}

static Stmt *
parse_null_statement(Ty *ty)
{
        Stmt *s = mkstmtx(NULL);
        consume(';');
        return s;
}

inline static bool
should_split(Ty *ty)
{
        if (LocSameLine(tok()->start, TEnd)) {
                return false;
        }

        switch (T0) {
        case '(':
        case '[':
                return true;

        case TOKEN_DBL_EQ:
        case TOKEN_NOT_EQ:
        case TOKEN_CMP:
        case TOKEN_GEQ:
        case TOKEN_LEQ:
        case TOKEN_PLUS:
        case TOKEN_MINUS:
        case TOKEN_STAR:
        case TOKEN_DIV:
        case TOKEN_PERCENT:
        case TOKEN_USER_OP:
                return InField
                    && (T1 == '(')
                    && (LocS(token(1)->start) == LocS(tok()->end));
        }

        return false;
}

static Expr *
parse_expr(Ty *ty, int prec)
{
        setctx(LEX_PREFIX);

        PLOG("%s", "");
        PLOG(
                "%sparse_expr%s(%d): [%s] | tok()=[%s]: %s%.*s%s~%s\n",
                TERM(93),
                TERM(0),
                prec,
                token_showx(ty, token(-1), ""),
                token_showx(ty, tokenx(0), TERM(92;1)),
                TERM(97;1;3),
                (TEnd.s == NULL) ? 0 : (int)strcspn(TEnd.s, "\n"),
                TEnd.s,
                TERM(91;1),
                TERM(0)
        );

        if (++ParseDepth > 256) {
                die("exceeded maximum recursion depth of 256");
        }

        //if (AllowErrors && CatchError()) {
        //        next();
        //        --ParseDepth;
        //        return &NullExpr;
        //}

        prefix_parse_fn *f = get_prefix_parser(ty);
        if (f == NULL) {
                die(
                        "expected expression but found %s%s%s%s",
                        TERM(34),
                        token_show(ty, tok()),
                        TERM(0),
                        found_hint(ty)
                );
        }

        Expr *e = (state.last = f(ty));

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
                e = (state.last = f(ty, e));
        }

        if (have_without_nl(ty, '"')) {
                Expr *ss = prefix_ss(ty);
                xF(ss, lang) = e;
                ss->start = e->start;
                e = ss;
        }

        if (T0 == TOKEN_STRING && LocS(tok()->start) == LocS(TEnd)) {
                Expr *lit = mkxpr(LANG_LITERAL);
                lit->start    = e->start;
                xF(lit, lit).lang = e;
                xF(lit, lit).text = tok()->string;
                consume(TOKEN_STRING);
                e = lit;
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
        //        EndCatch();
        //}

        --ParseDepth;

        return (state.last = e);
}

static Stmt *
parse_block(Ty *ty)
{
        Stmt *block = mkstmtx(BLOCK);

        consume('{');

        if (try_consume('}')) {
                block->type = STATEMENT_NULL;
                block->end = TEnd;
                return block;
        }

        CompilerScopePush(ty);

        if (CatchError()) {
                goto End;
        }
        while (!try_consume('}')) {
                if (try_consume(TOKEN_COMMENT)) {
                        continue;
                }
                InList = true;
                Stmt *s = parse_statement(ty, -1);
                s->end = TEnd;
                rvP(sF(block, statements), s);
        }
        EndCatch();

End:
        CompilerScopePop(ty);

        block->end = TEnd;

        return block;
}

static int
by_member_start(void const *a, void const *b)
{
        Expr const *x = *(Expr const **)a;
        Expr const *y = *(Expr const **)b;

        if (x->start.byte != y->start.byte) {
                return (x->start.byte < y->start.byte) ? -1 : 1;
        }

        return 0;
}

static void
order_members(Ty *ty, ClassDefinition *cd)
{
        ExprVec const *groups[] = {
                &cd->methods,   &cd->getters,   &cd->setters,   &cd->fields,
                &cd->s_methods, &cd->s_getters, &cd->s_setters, &cd->s_fields
        };

        v00(cd->members);

        for (usize g = 0; g < countof(groups); ++g) {
                rvPv(cd->members, *groups[g]);
        }

        qsort(vv(cd->members), vN(cd->members), sizeof (Expr *), by_member_start);
}

static Stmt *
mktagdef(Ty *ty, char *name)
{
        Stmt *s = mkstmtx(TAG_DEFINITION);
        sF(s, tag).pub = false;
        sF(s, tag).name = name;
        vec_init(sF(s, tag).methods);
        return s;
}

static Expr *
parse_method(
        Ty *ty,
        Location start,
        Expr *decorator_macro,
        char const *doc,
        ExprVec decorators
)
{
        unconsume(TOKEN_KEYWORD);
        tok()->keyword = KEYWORD_FUNCTION;

        Expr *func = prefix_function(ty);
        func->start = start;
        xF(func, doc) = doc;
        xF(func, decorators) = decorators;

        if (decorator_macro == NULL) {
                return func;
        } else {
                rvI(xF(decorator_macro, args), func, 0);
                rvI(xF(decorator_macro, fconds), NULL, 0);
                return decorator_macro;
        }
}

static Stmt *
parse_class_definition(Ty *ty)
{
        Stmt *def;

        switch (K0) {
        case KEYWORD_CLASS:
                def = mkstmtx(CLASS_DEFINITION);
                break;

        case KEYWORD_TRAIT:
                def = mkstmtx(CLASS_DEFINITION);
                sF(def, class).is_trait = true;
                break;

        case KEYWORD_TAG:
                def = mkstmtx(TAG_DEFINITION);
                break;

        default:
                UNREACHABLE();
        }

        next();

        expect(TOKEN_IDENTIFIER);
        sF(def, class).name = tok()->identifier;
        sF(def, class).loc  = tok()->start;
        next();

        if (T0 == '[') {
                parse_type_params(ty, &sF(def, class).type_params);
        }

        SAVE_NC(true);
        sF(def, tag).super = try_consume('<') ? parse_type(ty, 0) : NULL;
        LOAD_NC();

        if (try_consume(':')) {
                do {
                        expect(TOKEN_IDENTIFIER);
                        rvP(sF(def, tag).traits, parse_type(ty, 0));
                } while (
                        try_consume(',')
                );
        }

        /* Hack to allow comma-separated tag declarations */
        if ((def->type == STATEMENT_TAG_DEFINITION) && (T0 == ',')) {
                Stmt *tags = mkstmtx(MULTI);
                tags->start = def->start;
                rvP(sF(tags, statements), def);
                while (try_consume(',')) {
                        expect(TOKEN_IDENTIFIER);
                        rvP(sF(tags, statements), mktagdef(ty, tok()->identifier));
                        next();
                }
                try_consume(';');
                tags->end = TEnd;
                return tags;
        }

        if (try_consume(';')) {
                return def;
        }

        consume('{');

        while (!try_consume('}')) {
                parse_sync_lex(ty);

                char const *doc = NULL;
                if (T0 == TOKEN_COMMENT) {
                        doc = tok()->comment;
                        next();
                }

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

                ExprVec decorators       = {0};
                ExprVec macro_decorators = {0};

                SCRATCH_SAVE();

                parse_decorators(ty, &decorators, &macro_decorators);

                Location start = tok()->start;
                bool     dbg = try_consume(KEYWORD_DBG);
                bool _static = try_consume(KEYWORD_STATIC);
                bool     jit = try_consume(KEYWORD_JIT);

                // ================/ :) /===
                setctx(LEX_NAME);
                char *name = tok()->identifier;
                if (name == NULL) {
                        die("expected a class member but found %s", token_show(ty, tok()));
                }
                next();
                setctx(LEX_PREFIX);
                // =========================

                Expr *meth;
                if (T0 == '=' && K1 == KEYWORD_USE) {
                        if (def->type != STATEMENT_CLASS_DEFINITION) {
                                die("method aliases are only supported in classes and traits");
                        }

                        if (
                                (vN(decorators) > 0)
                             || (vN(macro_decorators) > 0)
                             || (decorator_macro != NULL)
                             || dbg
                             || jit
                        ) {
                                die("method alias %s'%s'%s cannot be decorated", TERM(34), name, TERM(39));
                        }

                        next();
                        next();

                        setctx(LEX_NAME);
                        char *target = tok()->identifier;
                        if (target == NULL) {
                                die("expected a method name but found %s", token_show(ty, tok()));
                        }
                        Location end = tok()->end;
                        next();
                        setctx(LEX_PREFIX);

                        rvP(
                                sF(def, tag).aliases,
                                ((MethodAlias) {
                                        .name   = name,
                                        .target = target,
                                        .s      = _static,
                                        .start  = start,
                                        .end    = end
                                })
                        );

                        try_consume(';');
                } else if (
                        (T0 == ':')
                     || (T0 == '=' && LocS(tok()->start)[-1] == ' ')
                ) {
                        Expr *field = mkid(name);
                        field->start = start;
                        SAVE_FD(true);
                        if (try_consume(':', TT_PUNCT)) {
                                SAVE_NE(true);
                                xF(field, constraint) = parse_type(ty, 1);
                                LOAD_NE();
                        }
                        field->end = TEnd;
                        if (T0 == TOKEN_EQ) {
                                field = infix_eq(ty, field);
                        }
                        LOAD_FD();
                        if (
                                (field->type != EXPRESSION_IDENTIFIER)
                             && (field->type != EXPRESSION_EQ)
                        ) {
                                EStart = field->start;
                                EEnd = field->end;
                                die("expected a field declarator");
                        }

                        if (_static) { rvP(sF(def, tag).s_fields, field); }
                        else         { rvP(sF(def, tag).fields,   field); }

                        try_consume(';');

                        TagTokenOf(ty, field, TT_FIELD);
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

                        unconsume(TOKEN_IDENTIFIER);
                        tok()->identifier = name;

                        meth = parse_method(
                                ty,
                                start,
                                decorator_macro,
                                doc,
                                decorators
                        );

                        meth->dbg |= dbg;
                        xF(meth, must_jit) |= jit;

                        if (
                                (xF(meth, body) != NULL)
                             && (xF(meth, body)->type == STATEMENT_EXPRESSION)
                             && (sF(xF(meth, body), expression)->type == EXPRESSION_GENERATOR)
                        ) {
                                xF(sF(xF(meth, body), expression), name) = afmt("<%s:gen>", name);
                        }

                        if (_static) {
                                if      (getter)  { rvP(sF(def, tag).s_getters, meth); }
                                else if (setter)  { rvP(sF(def, tag).s_setters, meth); }
                                else              { rvP(sF(def, tag).s_methods, meth); }
                        } else {
                                if      (getter)  { rvP(sF(def, tag).getters, meth); }
                                else if (setter)  { rvP(sF(def, tag).setters, meth); }
                                else              { rvP(sF(def, tag).methods, meth); }
                        }

                        TagTokenOf(ty, meth, TT_FUNC);
                }

                SCRATCH_RESTORE();
        }

        order_members(ty, &sF(def, tag));

        def->end = TEnd;

        return def;
}

inline static void
next_name(Ty *ty, StringVector *names)
{
        expect(TOKEN_IDENTIFIER);

        if (tok()->module != NULL) {
                rvP(*names, tok()->module);
        }

        rvP(*names, tok()->identifier);

        next();
}

inline static bool
have_typedef(Ty *ty)
{
        return (T0 == TOKEN_IDENTIFIER)
            && (T1 == '=' || T1 == '[');
}

static Stmt *
type_function(Ty *ty, Stmt *use)
{
        Expr *f = mkfunc(ty);
        xF(f, name) = sF(use, class).name;
        f->start = use->start;

        for (usize i = 0; i < vN(sF(use, class).type_params); ++i) {
                Expr const *param = v__(sF(use, class).type_params, i);
                if (param->type == EXPRESSION_MATCH_REST) {
                        xF(f, rest) = (int)i;
                }
                rvP(xF(f, params), xF(param, identifier));
                rvP(xF(f, constraints), NULL);
                rvP(xF(f, dflts), NULL);
        }

        Expr *body = parse_expr(ty, 0);
        xF(f, body) = to_stmt(body);
        f->end = TEnd;

        Stmt *def = mkstmtx(FUNCTION_DEFINITION);
        sF(def, target) = mkid(sF(use, class).name);
        sF(def, target)->start = use->start;
        sF(def, value) = f;
        def->start = use->start;
        def->end = TEnd;

        return def;
}

static Stmt *
parse_use(Ty *ty)
{
        Stmt *stmt = mkstmtx(TYPE_DEFINITION);

        stmt->type = STATEMENT_USE;

        next();

        if (try_consume(KEYWORD_MATCH)) {
                stmt->type = STATEMENT_PATTERN_DEFINITION;

                expect(TOKEN_IDENTIFIER);
                sF(stmt, target) = mkid(tok()->identifier);
                next();

                try_consume('=');

                Location brace = tok()->start;

                unconsume(TOKEN_KEYWORD);
                tok()->keyword = KEYWORD_MATCH;

                sF(stmt, value) = prefix_match(ty);
                xF(sF(stmt, value), ftype) = FT_PATTERN;;
                xF(sF(stmt, value), name) = xF(sF(stmt, target), identifier);
                stmt->end = TEnd;

                Expr *f = sF(stmt, value);
                if (f->type == EXPRESSION_FUNCTION) {
                        Expr *m = sF(xF(f, body), expression);
                        f->start = xF(f, body)->start = m->start = brace;
                        SYNTH(xF(m, subject), brace);
                }

                return stmt;
        }

        if (have_typedef(ty)) {
                stmt->type = STATEMENT_TYPE_DEFINITION;
                sF(stmt, class).name   = tok()->identifier;
                sF(stmt, class).module = tok()->module;
                next();
                if (T0 == '[') {
                        parse_type_params(ty, &sF(stmt, class).type_params);
                }
                consume('=');
                if (K0 == KEYWORD_MATCH || K0 == KEYWORD_DO) {
                        sF(stmt, class).type = NULL;
                        sF(stmt, class).tfn = type_function(ty, stmt);
                } else {
                        sF(stmt, class).type = parse_type(ty, -1);
                }
                stmt->end = TEnd;
                return stmt;
        }

        do next_name(ty, &sF(stmt, use).name);
        while (T0 == '.' && (next(), 1));

        if (T0 == '(') {
                next();

                do next_name(ty, &sF(stmt, use).names);
                while (T0 == ',' && (next(), 1));

                consume(')');
        }

        stmt->end = TEnd;

        return stmt;
}

static Stmt *
parse_catch(Ty *ty)
{
        Stmt *try = mkstmtx(TRY);

        while (have_kw(CATCH)) {
                next();
                if (T0 == '{') {
                        next();
                        while (T0 != '}') {
                                SAVE_NE(true);
                                rvP(sF(try, try).patterns, parse_expr(ty, 0));
                                LOAD_NE();
                                consume(TOKEN_FAT_ARROW);
                                rvP(sF(try, try).handlers, parse_statement(ty, -1));
                                try_consume(',');
                        }
                        next();
                } else {
                        SAVE_NE(true);
                        rvP(sF(try, try).patterns, parse_expr(ty, 0));
                        LOAD_NE();
                        rvP(sF(try, try).handlers, parse_statement(ty, -1));
                }
        }

        Stmt *body = parse_statement(ty, 0);
        Stmt *multi = NULL;

        while (get_prefix_parser(ty) != NULL) {
                if (multi == NULL) {
                        multi = mkstmtx(MULTI);
                        multi->start = body->start;
                        rvP(sF(multi, statements), body);
                }
                rvP(sF(multi, statements), parse_statement(ty, 0));
                multi->end = TEnd;
        }

        sF(try, try).s = (multi != NULL) ? multi : body;
        try->end = TEnd;

        return try;
}

static Stmt *
parse_try(Ty *ty)
{
        Stmt *s = mkstmtx(TRY);

        consume_kw(TRY);

        if (T0 != '{') {
                sF(s, try).s = mkstmtx(IF);
                sF(sF(s, try).s, _if).neg = true;
                sF(sF(s, try).s, _if).parts = parse_condparts(ty, &(bool){false});
                sF(s, try).s->end = TEnd;
                SYNTHETIC(sF(s, try).s);

                while (have_kw(CATCH)) {
                        next();
                        SAVE_NE(true);
                        rvP(sF(s, try).patterns, parse_expr(ty, 0));
                        LOAD_NE();
                        rvP(sF(s, try).handlers, parse_statement(ty, -1));
                }

                Stmt *_else;

                if (try_consume(KEYWORD_ELSE)) {
                        _else = parse_statement(ty, -1);
                        sF(sF(s, try).s, _if).then = _else;
                        sF(s, try).s->end = _else->end;
                } else {
                        _else = mkstmtx(NULL);
                        SYNTH(_else, TEnd);
                        sF(sF(s, try).s, _if).then = mkstmtx(NULL);
                        sF(sF(s, try).s, _if).then->start = sF(s, try).s->end;
                        sF(sF(s, try).s, _if).then->end = sF(s, try).s->end;
                }

                sF(sF(s, try).s, _if)._else = NULL;

                Expr *any = mkid("_");
                SYNTH(any, TEnd);

                rvP(sF(s, try).patterns, any);
                rvP(sF(s, try).handlers, CompilerSyntheticClone(ty, _else, TEnd));

                sF(s, try).finally = NULL;
                s->end = TEnd;

                record_sugar(ty, "try-else", s->start, s->end);

                return s;
        }

        sF(s, try).s = parse_statement(ty, -1);

        while (have_kw(CATCH)) {
                next();
                SAVE_NE(true);
                rvP(sF(s, try).patterns, parse_expr(ty, 0));
                LOAD_NE();
                rvP(sF(s, try).handlers, parse_statement(ty, -1));
        }

        if (have_kw(FINALLY)) {
                next();
                sF(s, try).finally = parse_statement(ty, -1);
        } else {
                sF(s, try).finally = NULL;
        }

        if (vN(sF(s, try).patterns) == 0 && sF(s, try).finally == NULL) {
                Expr *any = mkid("_");
                Stmt *nop = mkstmtx(NULL);
                SYNTH(any, TEnd);
                SYNTH(nop, TEnd);
                rvP(sF(s, try).patterns, any);
                rvP(sF(s, try).handlers, nop);
        }

        s->end = TEnd;

        return s;
}

static int
DotCount(int type)
{
        switch (type) {
        case '.':               return 1;
        case TOKEN_DOT_DOT:     return 2;
        case TOKEN_DOT_DOT_DOT: return 3;
        default:                return 0;
        }
}

static Stmt *
parse_import(Ty *ty)
{
        Stmt *s = mkstmtx(IMPORT);

        sF(s, import).pub = try_consume(KEYWORD_PUB);

        consume_kw(IMPORT);

        byte_vector module = {0};

        SCRATCH_SAVE();

        int dots = 0;

        for (int n; (n = DotCount(T0)) > 0; next()) {
                dots += n;
        }

        if (dots > 0) {
                sxdf(&module, "./");
        }

        while (--dots > 0) {
                sxdf(&module, "../");
        }

        while (try_consume(KEYWORD_SUPER)) {
                consume('.');
                sxdf(&module, "../");
        }

        expect(TOKEN_IDENTIFIER);
        char *mod = tok()->module;
        char *id = tok()->identifier;
        tok()->tag = TT_MODULE;
        next();

        if (mod != NULL) {
                sxdf(&module, "%s/", mod);
        }

        sxdf(&module, "%s", id);

        while (try_consume('.')) {
                expect(TOKEN_IDENTIFIER);
                sxdf(&module, "/%s", tok()->identifier);
                tok()->tag = TT_MODULE;
                next();
        }

        sF(s, import).module = sclonea(ty, vv(module));

        SCRATCH_RESTORE();

        if (try_consume(KEYWORD_AS)) {
                expect(TOKEN_IDENTIFIER);
                sF(s, import).as = tok()->identifier;
                tok()->tag = TT_MODULE;
                next();
        } else {
                char *alias = sF(s, import).module;
                while (alias[0] == '.' || alias[0] == '/') {
                        alias++;
                }
                sF(s, import).as = alias;
        }

        if (
                (T0 == TOKEN_IDENTIFIER)
             && s_eq(tok()->identifier, "hiding")
        ) {
                sF(s, import).hiding = true;
                tok()->tag = TT_KEYWORD;
                next();
        } else {
                sF(s, import).hiding = false;
        }

        v00(sF(s, import).identifiers);
        v00(sF(s, import).aliases);

        if (try_consume('(')) {
                if (try_consume(TOKEN_DOT_DOT)) {
                        rvP(sF(s, import).identifiers, "..");
                        rvP(sF(s, import).aliases, "..");
                } else for (;;) {
                        while (T0 == '\n') {
                                next();
                        }
                        if (T0 != TOKEN_IDENTIFIER) {
                                break;
                        }
                        rvP(sF(s, import).identifiers, tok()->identifier);
                        next();
                        if (try_consume(KEYWORD_AS)) {
                                expect(TOKEN_IDENTIFIER);
                                rvP(sF(s, import).aliases, tok()->identifier);
                                next();
                        } else {
                                rvP(sF(s, import).aliases, v_L(sF(s, import).identifiers));
                        }
                        while (T0 == '\n') {
                                next();
                        }
                        if (!try_consume(',')) {
                                expect(')');
                        }
                }
                consume(')');
        }

        s->end = TEnd;

        try_consume(';');
        try_consume('\n');

        return s;
}

static bool
looks_like_record(Ty *ty)
{
        int i = 1;

        while (
                (token(i)->type == TOKEN_IDENTIFIER)
             && (token(i + 1)->type == ',')
        ) {
                i += 2;
        }

        switch (token(i)->type) {
        case '$':
        case '?':
        case TOKEN_STAR:
                return token(i + 1)->type == TOKEN_IDENTIFIER;

        case TOKEN_IDENTIFIER:
                return (token(i + 1)->type == ':')
                    || (token(i + 1)->type == '}');

        default:
                return false;
        }
}

static Stmt *
_parse_statement(Ty *ty, int prec)
{
        Stmt *s;
        bool item = InList;

        InList = false;

        setctx(LEX_PREFIX);

        switch (T0) {
        case '{':
                if (item && looks_like_record(ty)) {
                        goto Expression;
                }
                return parse_block(ty);
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
        case KEYWORD_JIT:      return parse_function_definition(ty);
        case KEYWORD_FUNCTION: return parse_function_definition(ty);
        case KEYWORD_MACRO:    return parse_function_definition(ty);
        case KEYWORD_OPERATOR: return parse_operator_directive(ty);
        case KEYWORD_MATCH:    return have_match_cond(ty)
                                    ? parse_match_cond(ty, false)
                                    : parse_match_statement(ty);
        case KEYWORD_RETURN:   return parse_return_statement(ty);
        case KEYWORD_DEFER:    return parse_defer_statement(ty);
        case KEYWORD_LET:      return parse_let_definition(ty);
        case KEYWORD_CONST:    return parse_let_definition(ty);
        case KEYWORD_BREAK:    return parse_break_statement(ty);
        case KEYWORD_CONTINUE: return parse_continue_statement(ty);
        case KEYWORD_TRY:      return parse_try(ty);
        case KEYWORD_CATCH:    return parse_catch(ty);


        case KEYWORD_DBG:
                next();
                s = parse_statement(ty, prec);
                s->dbg = true;
                return s;

        case KEYWORD_USE:
                s = parse_use(ty);
                if (
                        (s->type == STATEMENT_USE)
                     && !HAVE_COMPILER_FLAG(PARSE)
                ) {
                        CompilerDoUse(ty, s, NULL);
                }
                return s;

        default:
                goto Expression;
        }

Expression:

        s = mkstmtx(EXPRESSION);
        sF(s, expression) = parse_expr(ty, prec);
        s->end = sF(s, expression)->end;

        if (sF(s, expression)->type == EXPRESSION_STATEMENT) {
                s = xF(sF(s, expression), statement);
        }

        try_consume(';');

        return s;
}

static void
MakePublic(Ty *ty, Stmt *s)
{
        switch (s->type) {
        case STATEMENT_DEFINITION:
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_PATTERN_DEFINITION:
                sF(s, pub) = true;
                break;

        case STATEMENT_TAG_DEFINITION:
        case STATEMENT_CLASS_DEFINITION:
        case STATEMENT_TYPE_DEFINITION:
                sF(s, class).pub = true;
                break;

        case STATEMENT_MULTI:
                for (int i = 0; i < vN(sF(s, statements)); ++i) {
                        MakePublic(ty, v__(sF(s, statements), i));
                }
                break;

        case STATEMENT_EXPRESSION:
                if (sF(s, expression)->type == EXPRESSION_STATEMENT) {
                        MakePublic(ty, xF(sF(s, expression), statement));
                        break;
                }
                // fallthrough

        default:
                die("`pub` applied to unexpected statement: %s", ExpressionTypeName((Expr *)s));
        }
}

static Stmt *
parse_statement(Ty *ty, int prec)
{
        //if (AllowErrors && CatchError()) {
        //        next();
        //        return &NullStatement;
        //}

        ExprVec decorators       = {0};
        ExprVec macro_decorators = {0};
        bool item                = InList;

        InList = false;

        SCRATCH_SAVE();

        parse_decorators(ty, &decorators, &macro_decorators);

        Location start = tok()->start;
        bool pub = try_consume(KEYWORD_PUB);

        InList = item;

        Stmt *stmt = _parse_statement(ty, prec);

        if (pub) {
                stmt->start = start;
        }

        if (vN(decorators) > 0) {
                if (stmt->type != STATEMENT_FUNCTION_DEFINITION) {
                        die_at(
                                v__(decorators, 0),
                                "decorator applied to undecoratable statement"
                        );
                }
                xF(sF(stmt, value), decorators) = decorators;
        }

        while (vN(macro_decorators) > 0) {
                Expr *dec = *vvX(macro_decorators);
                v__(xF(dec, args), 0) = to_expr(stmt);
                stmt = to_stmt(dec);
                expedite_fun(ty, to_expr(stmt), NULL);
                stmt = to_stmt(stmt);
        }

        SCRATCH_RESTORE();

        if (pub) {
                MakePublic(ty, stmt);
        }

        //if (AllowErrors) {
        //        EndCatch();
        //}

        return stmt;
}

static void
define_top(Ty *ty, Stmt *s, char const *doc)
{
        if (!HAVE_COMPILER_FLAG(RESOLVE)) {
                return;
        }

        switch (s->type) {
        case STATEMENT_FUN_MACRO_DEFINITION:
                sF(s, doc) = doc;
                define_macro(ty, s, true);
                break;

        case STATEMENT_MACRO_DEFINITION:
                sF(s, doc) = doc;
                define_macro(ty, s, false);
                break;

        case STATEMENT_PATTERN_DEFINITION:
        case STATEMENT_FUNCTION_DEFINITION:
                sF(s, doc) = doc;
                xF(sF(s, value), doc) = doc;
                IntroduceDefinitions(ty, s);
                break;

        case STATEMENT_OPERATOR_DEFINITION:
                sF(s, doc) = doc;
                xF(sF(s, value), doc) = doc;
                define_operator(ty, NULL, s);
                break;

        case STATEMENT_CLASS_DEFINITION:
                sF(s, class).doc = doc;
                define_class(ty, s);
                break;

        case STATEMENT_TAG_DEFINITION:
                sF(s, tag).doc = doc;
                define_tag(ty, s);
                break;

        case STATEMENT_TYPE_DEFINITION:
                sF(s, class).doc = doc;
                define_type(ty, s, NULL);
                break;

        case STATEMENT_MULTI:
                for (int i = 0; i < vN(sF(s, statements)); ++i) {
                        define_top(ty, v__(sF(s, statements), i), doc);
                }
                break;

        case STATEMENT_DEFINITION:
                sF(s, doc) = doc;
        case STATEMENT_IF:
                IntroduceDefinitions(ty, s);
                break;

        case STATEMENT_EXPRESSION:
                if (sF(s, expression)->type == EXPRESSION_STATEMENT) {
                        define_top(ty, xF(sF(s, expression), statement), doc);
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

static void
ClaimTokens(Ty *ty, ParserState const *outer)
{
        usize base = outer->TokenBase;

        if (vC(TokenBuffer) == 0) {
                xvR(TokenBuffer, TOKEN_BUFFER_SIZE);
        }

        if (
                (vv(outer->tokens) != NULL)
             && (vv(outer->tokens) == v_(TokenBuffer, base))
        ) {
                base += vN(outer->tokens);
        }

        state.TokenBase       = base;
        state.tokens.items    = v_(TokenBuffer, base);
        state.tokens.count    = 0;
        state.tokens.capacity = vC(TokenBuffer) - base;
}

inline static void
ReleaseTokens(Ty *ty, ParserState const *outer)
{
        if (vv(outer->tokens) == NULL) {
                xvF(TokenBuffer);
                v00(TokenBuffer);
        }
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
parse_module(Ty *ty, Module *mod)
{
        lex_save(ty, &CtxCheckpoint);

        ParserState save = state;
        m0(state);

        state.module = mod;
        ClaimTokens(ty, &save);

        CompileState *cs = TyCompilerState(ty);
        Scope *scope = cs->pscope;
        ScopeVector scopes = cs->scopes;
        volatile StmtVec program = {0};
        volatile bool ok = true;

        lex_init(ty, mod->path, mod->source);

        CompilerScopePush(ty);

        if (TY_CATCH_ERROR()) {
                TY_CATCH_FAIL();
                mod->error = tokenx(0)->start;
                ok = false;
                goto Finally;
        }

        setctx(LEX_PREFIX);

        while (T0 == TOKEN_NEWLINE) {
                next();
        }

        if (HAVE_COMPILER_FLAG(EXPRESSION)) {
                rvP(program, to_stmt(parse_expr(ty, 0)));
                expect(TOKEN_END);
                goto End;
        }

        while (
                (T0 == TOKEN_COMMENT)
             || (K0 == KEYWORD_IMPORT)
             || (K0 == KEYWORD_PUB && K1 == KEYWORD_IMPORT)
        ) {
                if (try_consume(TOKEN_COMMENT)) {
                        continue;
                }

                Stmt *import = parse_import(ty);

                if (
                        !HAVE_COMPILER_FLAG(SHALLOW)
                     && !ImportModule(ty, import)
                ) {
                        mod->error = import->end;
                        ok = false;
                        goto End;
                }

                rvP(program, import);
        }

        while (TokenIndex > 0 && token(-1)->type == TOKEN_COMMENT) {
                TokenIndex -= 1;
        }

        while (T0 != TOKEN_END) {
                char const *doc = NULL;

                while (have_kw(NAMESPACE) || have_kws(PUB, NAMESPACE)) {
                        lex_need_nl(ty, true);

                        Location kw = tok()->start;
                        bool pub = have_kw(PUB) && (next(), true);

                        next();

                        expect(TOKEN_IDENTIFIER);
                        Namespace *ns = PushNS(ty, tok()->identifier, tok(), pub);
                        ns->start = kw;
                        next();

                        while (T0 == '.') {
                                next();
                                expect(TOKEN_IDENTIFIER);
                                PushNS(ty, tok()->identifier, tok(), true);
                                CurrentNamespace->braced = false;
                                CurrentNamespace->start = kw;
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

                lex_need_nl(ty, have_kw(OPERATOR));

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

                Location start = tok()->start;
                bool dbg = try_consume(KEYWORD_DBG);
                bool pub = try_consume(KEYWORD_PUB);
                if (pub) {
                        switch (K0) {
                        case KEYWORD_CLASS:
                        case KEYWORD_CONST:
                        case KEYWORD_FUNCTION:
                        case KEYWORD_MACRO:
                        case KEYWORD_TAG:
                        case KEYWORD_TRAIT:
                        case KEYWORD_USE:
                                break;

                        default:
                                unconsume(TOKEN_KEYWORD);
                                tok()->keyword = KEYWORD_LET;
                                break;
                        }
                }


                InList = true;
                Stmt *s = parse_statement(ty, -1);
                if (s == NULL) {
                        break;
                }

                // TODO: figure out if this is necessary
                while (
                        (s->type == STATEMENT_EXPRESSION)
                     && (sF(s, expression)->type == EXPRESSION_STATEMENT)
                ) {
                        s = xF(sF(s, expression), statement);
                }

                s->end = TEnd;

                if (pub || dbg) {
                        s->start = start;
                }

                if (pub) {
                        MakePublic(ty, s);
                }

                if (dbg) {
                        s->dbg = true;
                }

                SetNamespace(s, CurrentNamespace);

                u32 flags = mod->flags;
                u32 cflags = TyCompilerState(ty)->flags;
                TyCompilerState(ty)->flags &= ~TYC_FORGIVING;
                if (TY_CATCH_ERROR()) {
                        TyCompilerState(ty)->flags = cflags;
                        TY_SUPPRESS("top-level definition");
                        mod->flags = flags;
                        UnresolveExpr(ty, (Expr *)s);
                        if (s->type == STATEMENT_OPERATOR_DEFINITION) {
                                sF(s, retry) = true;
                        }
                } else {
                        define_top(ty, s, doc);
                        TY_CATCH_END();
                        TyCompilerState(ty)->flags = cflags;
                }

                rvP(program, s);

#ifdef TY_DEBUG_NAMES
                pns(s->ns, true);
#endif

                while (T0 == '}' && CurrentNamespace != NULL) {
                        while (
                                (CurrentNamespace != NULL)
                             && !CurrentNamespace->braced
                        ) {
                                CloseNS(ty, TEnd);
                        }
                        if (CurrentNamespace != NULL) {
                                next();
                                CloseNS(ty, TEnd);
                        }
                }
        }

End:
        TY_CATCH_END();

Finally:
        cs->pscope = scope;
        cs->scopes = scopes;

        for (Namespace *ns = CurrentNamespace; ns != NULL; ns = ns->next) {
                ns->end = TEnd;
                record_extra(ty, "Namespace", NULL, ns->start, ns->end);
        }

        rvP(program, NULL);
        mod->prog = vv(program);

        if (vv(TOKENS) == v_(TokenBuffer, state.TokenBase)) {
                v00(mod->tokens);
                avR(mod->tokens, vN(TOKENS));
                avPv(mod->tokens, TOKENS);
        } else {
                mod->tokens = TOKENS;
        }

        if (HAVE_COMPILER_FLAG(SNAPSHOT)) {
                syntax_snapshot(ty, mod);
        }

        mod->last = state.last;

        ReleaseTokens(ty, &save);

        state = save;
        lex_restore(ty, &CtxCheckpoint);

        return ok;
}

Stmt **
parse(Ty *ty, char const *source, char const *file)
{
        Module mod = { .source = source, .path = file };

        if (!parse_module(ty, &mod)) {
                return NULL;
        }

        return mod.prog;
}

static Expr *
parse_bare_type(Ty *ty)
{
        return parse_type(ty, 0);
}

static Expr *
parse_bare_signature(Ty *ty)
{
        Expr *f = mkfunc(ty);
        parse_function_header(ty, f);
        return f;
}

static Expr *
parse_fragment(Ty *ty, Module *mod, char const *source, Expr *(*parser)(Ty *))
{
        lex_save(ty, &CtxCheckpoint);

        ParserState save = state;
        m0(state);

        state.module = mod;
        ClaimTokens(ty, &save);

        usize n = strlen(source);
        char *src = amA(n + 2);
        src[0] = '\0';
        memcpy(src + 1, source, n + 1);

        lex_init(ty, mod->path, src + 1);

        if (TY_CATCH_ERROR()) {
                ReleaseTokens(ty, &save);
                state = save;
                lex_restore(ty, &CtxCheckpoint);
                TY_RETHROW();
        }

        setctx(LEX_PREFIX);

        Expr *e = parser(ty);
        expect(TOKEN_END);

        TY_CATCH_END();

        ReleaseTokens(ty, &save);

        state = save;
        lex_restore(ty, &CtxCheckpoint);

        return e;
}

Expr *
parse_type_source(Ty *ty, Module *mod, char const *source)
{
        return parse_fragment(ty, mod, source, parse_bare_type);
}

Expr *
parse_signature_source(Ty *ty, Module *mod, char const *source)
{
        return parse_fragment(ty, mod, source, parse_bare_signature);
}

Token
parse_get_token(Ty *ty, int i)
{
        return *token(i);
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
        Location embedded = tok()->start;

        SAVE_NI(false);
        SAVE_NE(false);

        Value v;
        Expr *e;

        if (TryParse()) {
                v = NIL;
                seek(ty, save);
        } else {
                e = parse_type(ty, prec);
                record_embedded(ty, "type", embedded, TEnd, e);
                if (!resolve) {
                        v = CToTyExpr(ty, e);
                } else {
                        compiler_symbolize_expression(ty, e, NULL);
                        v = PTR(e);
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyExpr);
                }
                TY_CATCH_END();
        }

        LOAD_NE();
        LOAD_NI();

        if (want_raw) {
                return PAIR(PTR(e), v);
        } else {
                return v;
        }
}

Value
parse_get_expr(Ty *ty, int prec, bool resolve, bool want_raw)
{
        int save = TokenIndex;
        Location embedded = tok()->start;

        SAVE_NI(false);
        SAVE_NE(false);

        Value v;
        Expr *e;

        if (TY_CATCH_ERROR()) {
                seek(ty, save);
                LOAD_NE();
                LOAD_NI();
                TY_RETHROW();
        } else {
                e = parse_expr(ty, prec);
                record_embedded(ty, "expr", embedded, TEnd, e);
                if (!resolve) {
                        v = CToTyExpr(ty, e);
                } else {
                        compiler_symbolize_expression(ty, e, NULL);
                        v = PTR(e);
                        v.type |= VALUE_TAGGED;
                        v.tags = tags_push(ty, 0, TyExpr);
                }
                TY_CATCH_END();
        }

        LOAD_NE();
        LOAD_NI();

        if (want_raw) {
                return PAIR(PTR(e), v);
        } else {
                return v;
        }
}

Value
parse_get_stmt(Ty *ty, int prec, bool want_raw)
{
        int save = TokenIndex;
        Location embedded = tok()->start;

        SAVE_NI(false);
        SAVE_NE(false);

        Value v;

        if (TY_CATCH_ERROR()) {
                seek(ty, save);
                LOAD_NE();
                LOAD_NI();
                TY_RETHROW();
        } else {
                Stmt *s = parse_statement(ty, prec);
                if (s->end.byte < TEnd.byte) {
                        s->end = TEnd;
                }
                record_embedded(ty, "stmt", embedded, TEnd, s);
                if (want_raw) {
                        v = vT(2);
                        v.items[0] = PTR(s);
                        v.items[1] = tyexpr(ty, (Expr *)s, 0);
                } else {
                        v = tyexpr(ty, (Expr *)s, 0);
                }
                TY_CATCH_END();
        }

        LOAD_NE();
        LOAD_NI();

        return v;
}

static Value
pp_eval(Ty *ty, Expr *expr)
{
        lex_save(ty, &CtxCheckpoint);
        ParserState save = state;
        v00(state.stack);

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
        LexState lx0 = *lex_state(ty);
        LexState st0 = lx0;
        st0.need_nl  = false;

        int very_start = TokenIndex;
        int lex_level  = vN(state.stack);

        int depth = 0;

        vec(Expr *)   conds = {0};
        vec(LexState) arms  = {0};

        SCRATCH_SAVE();

        nextx();

        lex_in_pp(ty, true);

        PLOG("%sPP_IF()%s: BEGIN", TERM(96;1), TERM(0));

        for (;;) {
                Token *t0 = tokenx(0);
                int kw = (t0->type == TOKEN_KEYWORD) ? t0->keyword : -1;

                PLOG(
                        "%sPP_IF()%s: [%02d] ARM %zu: %s",
                        TERM(96;1),
                        TERM(0),
                        depth,
                        vN(arms),
                        token_showx(ty, t0, "")
                );

                switch (kw) {
                case KEYWORD_ELSE:
                        next();
                        if (depth == 1) {
                                if (K0 == KEYWORD_IF) {
                                        next();
                                }
                                if (T0 != '\n') {
                                        svP(conds, parse_expr(ty, 0));
                                } else {
                                        svP(conds, NULL);
                                }
                                consume('\n');
                                st0.loc = token(0)->start;
                                svP(arms, st0);
                        }
                        break;

                case KEYWORD_IF:
                        next();
                        if (++depth == 1) {
                                svP(conds, parse_expr(ty, 0));
                                consume('\n');
                                st0.loc = token(0)->start;
                                svP(arms, st0);
                        }
                        break;

                default:
                        if (tokenx(0)->type != ']') {
                                 die(
                                        "expected `#|if` directive to end"
                                        " with `#|]` but found: %s",
                                        token_show(ty, tokenx(0))
                                );
                        }
                        if (--depth == 0) {
                                nextx();
                                nextx();
                                break;
                        }
                }

                if (depth == 0) {
                        break;
                }

                while (tokenx(0)->type != TOKEN_DIRECTIVE) {
                        if (tokenx(0)->type == TOKEN_END) {
                                expect(TOKEN_DIRECTIVE);
                                UNREACHABLE();
                        }
                        if (tokenx(0)->type == TOKEN_TEMPLATE_BEGIN) {
                                (void)prefix_template(ty);
                        } else if (tokenx(0)->type == '"') {
                                skip_ss(ty);
                        } else {
                                nextx();
                        }
                }

                if (vN(arms) > 0) {
                        vvL(arms)->end = LocS(tokenx(0)->start);
                }

                nextx();
        }

        int very_end = TokenIndex;

        PLOG("%sPP_IF()%s: END", TERM(96;1), TERM(0));
        for (int i = very_start; i < very_end; ++i) {
                v_(TOKENS, i)->ctx = LEX_HIDDEN;
                v_(TOKENS, i)->pp = true;
                PLOG(
                        "    %s[%5d]%s  (%s)",
                        TERM(95;1),
                        i,
                        TERM(0),
                        token_showx(ty, v_(TOKENS, i), "")
                );
        }

        LexState *take = NULL;

        for (int i = 0; i < vN(conds); ++i) {
                Expr *cond = v__(conds, i);
                Value val  = (cond == NULL) ? BOOLEAN(true)
                           :                  pp_eval(ty, cond);
                if (value_truthy(ty, &val)) {
                        take = v_(arms, i);
                        break;
                }
        }

        lex_in_pp(ty, false);

        vN(TOKENS) = TokenIndex;

        if (vN(state.stack) < lex_level) {
                vN(state.stack) = lex_level;
                *lex_state(ty)  = lx0;
        }

        lex_rewind(ty, &vvL(TOKENS)->end);

        if (take != NULL) {
                avP(state.stack, *lex_state(ty));
                *lex_state(ty) = *take;
                PLOG("PP_IF() took arm starting at: %.20s", take->loc.s);
        }

        SCRATCH_RESTORE();
}

void
parse_reset(Ty *ty)
{
        table_init(ty, &uops);
        table_init(ty, &uopcs);

        state.last = NULL;

        BlankID       = (Expr) { .type = EXPRESSION_IDENTIFIER };
        WildCard      = (Expr) { .type = EXPRESSION_IDENTIFIER };
        NullStatement = (Stmt) { .type = STATEMENT_NULL       };
        NullExpr      = (Expr) { .type = EXPRESSION_STATEMENT };

        xF(&BlankID,  identifier) = "";
        xF(&WildCard, identifier) = "_";
        xF(&NullExpr, statement)  = &NullStatement;
}

Module *
TyParserModule(Ty *ty)
{
        return state.module;
}

TokenVector const *
TyParserTokens(Ty *ty)
{
        return &TOKENS;
}

/* vim: set sts=8 sw=8 expandtab: */

bool
parse_mark_region(Ty *ty, char const *kind, u32 start, u32 end)
{
        Module *mod = state.module;

        if (mod == NULL || mod->source == NULL) {
                return false;
        }

        usize n = strlen(mod->source);

        if (start >= end || end > n) {
                return false;
        }

        u32      src = SourceRegister(mod->source, n);
        Location a   = MkLoc(src, start);
        Location b   = MkLoc(src, end);

        record_extra(ty, "Region", sclonea(ty, kind), a, b);

        return true;
}
