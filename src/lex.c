#include <ctype.h>
#include <setjmp.h>
#include <stdarg.h>
#include <string.h>
#include <stdbool.h>
#include <stdnoreturn.h>
#include <assert.h>
#include <errno.h>
#include <math.h>

#include "vec.h"
#include "token.h"
#include "test.h"
#include "util.h"
#include "lex.h"
#include "log.h"

enum {
        MAX_OP_LEN   = 8,
};

static char const *filename;
static struct location Start;

static jmp_buf jb;

static LexState state;
static vec(LexState) states;

#define SRC state.loc.s
#define END state.end

inline static char
C(int n)
{
        if (SRC + n < END)
                return SRC[n];
        return '\0';
}

static char const *opchars = "/=<~|!@%^&*-+>?.$";

noreturn static void
error(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        int sz = ERR_SIZE - 1;
        int n = snprintf(
                ERR,
                sz,
                "%s%sSyntaxError%s%s %s%s%s:%s%d%s:%s%d%s: ",
                TERM(1),
                TERM(31),
                TERM(22),
                TERM(39),
                TERM(34),
                filename,
                TERM(39),
                TERM(33),
                state.loc.line + 1,
                TERM(39),
                TERM(33),
                state.loc.col + 1,
                TERM(39)
        );
        n += vsnprintf(ERR + n, sz - n, fmt, ap);
        va_end(ap);

        char const *prefix = state.loc.s;
        while (prefix[-1] != '\n' && prefix[-1] != '\0')
                --prefix;

        int before = state.loc.s - prefix;
        int after = strcspn(state.loc.s + 1, "\n");

        n += snprintf(
                ERR + n,
                sz - n,
                "\n\n\tnear: %.*s%s%s%.1s%s%s%.*s\n",
                before,
                prefix,
                TERM(1),
                TERM(31),
                state.loc.s,
                TERM(22),
                TERM(39),
                after,
                state.loc.s + 1
        );

        n += snprintf(
                ERR + n,
                sz - n,
                "\t%*s%s^%s",
                6 + before,
                " ",
                TERM(31),
                TERM(39)
        );

        longjmp(jb, 1);
}

static struct token
mktoken(int type)
{
        return (struct token) {
                .type = type,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static struct token
mkid(char *id, char *module)
{
        return (struct token) {
                .type = TOKEN_IDENTIFIER,
                .identifier = id,
                .module = module,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static struct token
mkstring(char *string)
{
        return (struct token) {
                .type = TOKEN_STRING,
                .string = string,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static struct token
mkregex(char const *pat, int flags)
{
        char const *err;
        int offset;

        pcre *re = pcre_compile(pat, flags, &err, &offset, NULL);
        if (re == NULL) {
                error(
                        "error compiling regular expression: %s/%s/%s at position %d",
                        TERM(36),
                        err,
                        TERM(39),
                        offset
                );
        }

        pcre_extra *extra = pcre_study(re, PCRE_STUDY_EXTRA_NEEDED | PCRE_STUDY_JIT_COMPILE, &err);
        if (extra == NULL) {
                error(
                        "error studying regular expression: %s/%s/%s",
                        TERM(36),
                        err,
                        TERM(39)
                );
        }

        pcre_assign_jit_stack(extra, NULL, JITStack);

        struct regex *r = gc_alloc(sizeof *r);
        r->pattern = pat;
        r->pcre = re;
        r->extra = extra;

        return (struct token) {
                .type = TOKEN_REGEX,
                .regex = r,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static struct token
mkreal(float real)
{
        return (struct token) {
                .type = TOKEN_REAL,
                .real = real,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static struct token
mkinteger(intmax_t k)
{
        return (struct token) {
                .type = TOKEN_INTEGER,
                .integer = k,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static struct token
mkkw(int kw)
{
        return (struct token) {
                .type = TOKEN_KEYWORD,
                .keyword = kw,
                .start = Start,
                .end = state.loc,
		.ctx = state.ctx
        };
}

static char
nextchar(void)
{
        char c = C(0);

        if (c == '\n') {
                state.loc.line += 1;
                state.loc.col = 0;
        } else {
                state.loc.col += 1;
        }

        SRC += 1;

        return c;
}

static bool
haveid(void)
{
        if (C(0) == ':' && C(1) == ':' && isalpha(C(2)))
                return true;

        if (isalpha(C(0)) || C(0) == '_')
                return true;

        return false;
}

static bool
skipspace(void)
{
        bool nl = false;

        int n = 0;
        while (isspace(C(n))) {
                if (C(n) == '\n' && state.need_nl) {
                        nl = true;
                        state.need_nl = false;
                }
                n += 1;
        }

        if (SRC + n == END) {
                SRC += n;
        } else {
                while (n --> 0) {
                        nextchar();
                }
        }

        return nl;
}

/* lexes an identifier or a keyword */
static struct token
lexword(void)
{
        vec(char) module;
        vec(char) word;

        vec_init(module);
        vec_init(word);

        bool has_module = false;

        for (;;) {
                while (isalnum(C(0)) || C(0) == '_')
                        vec_push(word, nextchar());

                if (C(0) == ':' && C(1) == ':' && ++has_module) {
                        nextchar();
                        nextchar();

                        if (module.count != 0)
                                vec_push(module, '/');

                        if (word.count != 0)
                                vec_push_n(module, word.items, word.count);
                        word.count = 0;

                        if (!isalpha(C(0)) && C(0) != '_') {
                                error(
                                        "expected name after %s'::'%s in identifier",
                                        TERM(36),
                                        TERM(39)
                                );
                        }
                } else {
                        break;
                }
        }

        /*
         * Identifiers are allowed to end in '?' or '!'. e.g., [1, 2, 3].map!(a -> a + 1)
         */
        if (C(0) == '!' || C(0) == '?')
                vec_push(word, nextchar());

        if (has_module != 0)
                vec_push(module, '\0');

        vec_push(word, '\0');

        char *w = word.items;
        char *m = module.items;

        int keyword;
        if (keyword = keyword_get_number(w), keyword != -1) {
                state.need_nl |= (
                        keyword == KEYWORD_IMPORT
                     || keyword == KEYWORD_EXPORT
                     || keyword == KEYWORD_OPERATOR
                );
                return mkkw(keyword);
        } else {
                return mkid(w, m);
        }
}

static struct token
lexrawstr(void)
{
        vec(char) str;
        vec_init(str);

        nextchar();

        while (C(0) != '\'') {
                switch (C(0)) {
                case '\0':
                Unterminated:
                        error("unterminated string literal");
                case '\\':
                        nextchar();
                        switch (C(0)) {
                        case '\0':
                                goto Unterminated;
                        case 'n':
                                nextchar();
                                vec_push(str, '\n');
                                continue;
                        case 'r':
                                nextchar();
                                vec_push(str, '\r');
                                continue;
                        case 't':
                                nextchar();
                                vec_push(str, '\t');
                                continue;
                        }
                        // fallthrough
                default:
                           vec_push(str, nextchar());
                }
        }

        assert(nextchar() == '\'');

        vec_push(str, '\0');

        return mkstring(str.items);
}

static char const *
lexexpr(void)
{
        int depth = 1;

        for (;;) {
                switch (C(0)) {
                case '\0':
                        goto Unterminated;
                case '{':
                        depth += 1;
                        break;
                case '}':
                        if (--depth == 0)
                                goto End;
                        break;
                }
                nextchar();
        }
End:

        return SRC;

Unterminated:
        error("unterminated expression in interpolated string");
}

static struct token
lexspecialstr(void)
{
        struct token special = mktoken(TOKEN_SPECIAL_STRING);
        vec_init(special.strings);
        vec_init(special.fmts);
        vec_init(special.expressions);
        vec_init(special.starts);
        vec_init(special.ends);

        vec(char) str;
        vec_init(str);

        nextchar();

        char *fmt = NULL;

Start:

        while (C(0) != '"') {
                switch (C(0)) {
                case '\0': goto Unterminated;
                case '{':  goto Expr;
                case '%':
                        nextchar();
                        if (C(0) != '%') {
                                fmt = SRC;
                                while (C(0) != '\0' && C(0) != '{' && C(0) != '"') {
                                        nextchar();
                                }
                                if (C(0) != '{') {
                                        error("unterminated format specifier");
                                }
                        } else {
                                vec_push(str, nextchar());
                        }
                        break;
                case '\\':
                        nextchar();
                        switch (C(0)) {
                        case '\0':
                                goto Unterminated;
                        case 'n':
                                nextchar();
                                vec_push(str, '\n');
                                continue;
                        case 'r':
                                nextchar();
                                vec_push(str, '\r');
                                continue;
                        case 't':
                                nextchar();
                                vec_push(str, '\t');
                                continue;
                        }
                default:
                           vec_push(str, nextchar());
                }
        }

        assert(nextchar() == '"');

        vec_push(str, '\0');
        vec_push(special.strings, str.items);

        special.end = state.loc;
        return special;

Expr:
        vec_push(str, '\0');
        vec_push(special.strings, str.items);
        vec_init(str);

        vec_push(special.fmts, fmt);
        fmt = NULL;

        /* Eat the initial { */
        nextchar();

        LexState st = state;
        st.end = lexexpr();

        /* Eat the terminating } */
        nextchar();

        vec_push(special.expressions, st);

        goto Start;

Unterminated:

        error("unterminated string literal");
}

static struct token
lexregex(void)
{
        vec(char) pat;
        vec_init(pat);

        nextchar();

        while (C(0) != '/') {
                switch (C(0)) {
                case '\0': goto Unterminated;
                case '\\':
                        if (C(1) == '\0') {
                                goto Unterminated;
                        }
                        if (C(1) == '\\') {
                                vec_push(pat, nextchar());
                        } else if (C(1) == '/') {
                                nextchar();
                        }
                        /* fallthrough */
                default:
                           vec_push(pat, nextchar());
                }
        }

        assert(nextchar() == '/');

        int flags = 0;

        while (isalpha(C(0))) {
                switch (C(0)) {
                case 'i': flags |= PCRE_CASELESS; break;
                case 'u': flags |= PCRE_UTF8;     break;
                default:  error("invalid regex flag: %s'%c'%s", TERM(36), C(0), TERM(39));
                }
                nextchar();
        }

        vec_push(pat, '\0');

        return mkregex(pat.items, flags);

Unterminated:
        vec_push(pat, '\0');
        error("unterminated regular expression: %s/%.20s%s...", TERM(36), pat.items, TERM(39));
}

static struct token
lexnum(void)
{
        char *end;
        errno = 0;
        intmax_t integer = strtoull(SRC, &end, 0);

        int n = end - SRC;

        struct token num;

        if (errno != 0) {
                char const *err = strerror(errno);
                error("invalid numeric literal: %c%s", tolower(err[0]), err + 1);
        }

        if (C(n) == '.' && !isalpha(C(n + 1)) && C(n + 1) != '_' && C(n + 1) != '.') {
                errno = 0;
                float real = strtof(SRC, &end);
                n = end - SRC;

                if (errno != 0) {
                        char const *err = strerror(errno);
                        error("invalid numeric literal: %c%s", tolower(err[0]), err + 1);
                }

                if (isalnum(C(n))) {
                        error(
                                "trailing character after numeric literal: %s'%c'%s",
                                TERM(36),
                                C(n),
                                TERM(39)
                        );
                }

                while (SRC != end) nextchar();

                num = mkreal(real);
        } else if (C(n) == 'r') {
                errno = 0;
                integer = strtoull(end + 1, &end, integer);
                if (errno != 0) {
                        error("what are you doing step bro?");
                }
                while (SRC != end) nextchar();
                num = mkinteger(integer);
        } else {
                if (isalnum(C(n))) {
                        error(
                                "trailing character after numeric literal: %s'%c'%s",
                                TERM(36),
                                C(n),
                                TERM(39)
                        );
                }
                while (SRC != end) nextchar();
                num = mkinteger(integer);
        }

        return num;
}

static struct token
lexop(void)
{
        char op[MAX_OP_LEN + 1] = {0};
        size_t i = 0;

        while (contains(opchars, C(0)) || (C(0) == ':' && (C(-1) != '*' || i > 1 || (contains(opchars, C(1)) && C(1) != '-')))) {
                if (i == MAX_OP_LEN) {
                        error(
                                "operator contains too many characters: %s'%s...'%s",
                                TERM(36),
                                op,
                                TERM(39)
                        );
                } else {
                        op[i++] = nextchar();
                }
        }

        int toktype = operator_get_token_type(op);
        if (toktype == -1) {
                struct token t = mktoken(TOKEN_USER_OP);
                t.identifier = sclone(op);
                return t;
        }

        return mktoken(toktype);
}

static bool
lexlinecomment(void)
{
        // skip the leading slashes
        nextchar();
        nextchar();

        bool need_nl = state.need_nl;

        while (C(0) != '\n' && C(0) != '\0') {
                nextchar();
        }

        nextchar();

        state.need_nl = false;
        Start = state.loc;

        return need_nl;
}

static void
lexcomment(void)
{
        // skip the /*
        nextchar();
        nextchar();

        int level = 1;

        while (C(0) != '\0' && level != 0) {
                if (C(0) == '/' && C(1) == '*')
                        ++level;
                if (C(0) == '*' && C(1) == '/')
                        --level;
                nextchar();
        }

        if (level != 0)
                error("unterminated comment");

        // skip the final /
        nextchar();

        Start = state.loc;
}

struct token
lex_token(LexContext ctx)
{
        if (setjmp(jb) != 0)
                return (struct token) { .type = TOKEN_ERROR, .start = Start, .end = state.loc, .ctx = state.ctx };

        if (skipspace()) {
                return mktoken(TOKEN_NEWLINE);
        }

        Start = state.loc;
        state.ctx = ctx;

        while (SRC < END) {
                if (C(0) == '/' && C(1) == '*') {
                        lexcomment();
                        if (skipspace()) {
                                return mktoken(TOKEN_NEWLINE);
                        }
                } else if (C(0) == '/' && C(1) == '/') {
                        if (lexlinecomment() || skipspace()) {
                                return mktoken(TOKEN_NEWLINE);
                        }
                } else if (ctx == LEX_PREFIX && C(0) == '/') {
                        return lexregex();
                } else if (haveid()) {
                        return lexword();
                } else if (C(0) == ':' && C(1) == ':' && !contains(opchars, C(2))) {
                        nextchar();
                        nextchar();
                        return mktoken(TOKEN_CHECK_MATCH);
                } else if (C(0) == '-' && C(1) == '>' && ctx == LEX_PREFIX) {
                        nextchar();
                        nextchar();
                        return mktoken(TOKEN_ARROW);
                } else if (C(0) == '-' && C(1) != '-' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken(TOKEN_MINUS);
                } else if (C(0) == '#' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken('#');
                } else if (C(0) == '&' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken('&');
                } else if (C(0) == '*' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken(TOKEN_STAR);
                } else if (C(0) == '!' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken(TOKEN_BANG);
                } else if (C(0) == '?' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken(TOKEN_QUESTION);
                } else if (C(0) == '$' && ctx == LEX_PREFIX) {
                        nextchar();
                        return mktoken('$');
                } else if (contains(opchars, C(0)) || (C(0) == ':' && contains(opchars, C(1)) && C(1) != '-')) {
                        return lexop();
                } else if (isdigit(C(0))) {
                        return lexnum();
                } else if (C(0) == '\'') {
                        return lexrawstr();
                } else if (C(0) == '"') {
                        return lexspecialstr();
                } else if (C(0) == '.' && C(1) == '.') {
                        nextchar();
                        nextchar();
                        if (C(0) == '.')
                                return nextchar(), mktoken(TOKEN_DOT_DOT_DOT);
                        else
                                return mktoken(TOKEN_DOT_DOT);
                } else {
                        return mktoken(nextchar());
                }
        }

        struct location start = Start;
        struct location end = state.loc;
        return (struct token) { .type = TOKEN_END, .start = start, .end = end, .ctx = state.ctx };
}

char const *
lex_error(void)
{
        return ERR;
}

void
lex_init(char const *file, char const *src)
{
        filename = file;

        state = (LexState) {
                .loc = (struct location) {
                        .s = src,
                        .line = 0,
                        .col = 0
                },
                .end = src + strlen(src),
                .need_nl = false,
                .ctx = LEX_PREFIX
        };

        Start = state.loc;

        vec_init(states);

        /*
         * Eat the shebang if there is one.
         */
        if (C(0) == '#' && C(1) == '!')
                while (SRC != END && C(0) != '\n')
                        nextchar();
}

void
lex_start(LexState const *st)
{
        vec_push(states, state);
        state = *st;
}

void
lex_save(LexState *s)
{
        *s = state;
}

void
lex_rewind(struct location const *where)
{
        state.loc = *where;
}

void
lex_end(void)
{
        state = *vec_pop(states);
}

static struct token *
lex(char const *s)
{
        LexState st = {
                .loc = (struct location) { 0 },
                .end = s + strlen(s)
        };

        lex_start(&st);

        struct token *t = malloc(sizeof *t);
        *t = lex_token(LEX_INFIX);

        lex_end();

        return t;
}
