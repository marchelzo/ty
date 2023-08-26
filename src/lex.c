#include <ctype.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include <stdnoreturn.h>
#include <assert.h>
#include <errno.h>
#include <math.h>

#include <utf8proc.h>

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

inline static unsigned char
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
        int after = (state.loc.s[0] == '\0') ? 0 : strcspn(state.loc.s + 1, "\n");

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

        if (JITStack != NULL)
                pcre_assign_jit_stack(extra, NULL, JITStack);

        struct regex *r = gc_alloc(sizeof *r);
        r->pattern = pat;
        r->pcre = re;
        r->extra = extra;
        r->gc = false;

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

        if (isalpha(C(0)) || C(0) == '_' || (C(0) > 0xC0))
                return true;

        return false;
}

static bool
skipspace(void)
{
        bool nl = false;

        int n = 0;
        while (isspace(C(n))) {
                nl |= (C(n) == '\n');
                n += 1;
        }

        if (SRC + n == END) {
                SRC += n;
        } else {
                while (n --> 0) {
                        nextchar();
                }
        }

        nl &= state.need_nl;
        state.need_nl &= !nl;

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
                while (isalnum(C(0)) || C(0) == '_' || (C(0) & 0x80))
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
         * Also, macro names end in $
         */
        if (C(0) == '!' || C(0) == '?' || C(0) == '$')
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

static bool
end_of_docstring(char c, int ndelim)
{
        for (int i = 0; i < ndelim; ++i) {
                if (C(i) != c) {
                        return false;
                }
        }

        return true;
}

static bool
eat_line_ending(void)
{
        if (C(0) == '\n') {
                nextchar();
                return true;
        }

        if (C(0) == '\r' && C(1) == '\n') {
                nextchar();
                nextchar();
                return true;
        }

        return false;
}

static struct token
lexdocstring(void)
{
        vec(char *) lines;
        vec(char) line;

        vec_init(lines);
        vec_init(line);

        int ndelim = 0;
        while (C(0) == '\'') {
                nextchar();
                ndelim += 1;
        }

        eat_line_ending();

        while (!end_of_docstring('\'', ndelim) && C(0) != '\0') {
                if (eat_line_ending()) {
                        vec_push(line, '\0');
                        vec_push(lines, line.items);
                        vec_init(line);
                } else {
                        vec_push(line, nextchar());
                }
        }

        if (!end_of_docstring('\'', ndelim)) {
                error("unterminated docstring starting on line %d", Start.line);
        }

        // The only characters on this line before the docstring terminator should be whitespace
        for (int i = 0; i < line.count; ++i) {
                if (!isspace(line.items[i])) {
                        error("illegal docstring terminator on line %d", state.loc.line);
                }
        }

        while (ndelim --> 0) {
                nextchar();
        }

        int nstrip = line.count;
        vec_empty(line);

        vec(char) s;
        vec_init(s);

        for (int i = 0; i < lines.count; ++i) {
                int off = 0;
                while (off < nstrip && isspace(lines.items[i][off])) {
                        off += 1;
                }
                while (lines.items[i][off] != '\0') {
                        vec_push(s, lines.items[i][off++]);
                }
                if (i + 1 != lines.count) {
                        vec_push(s, '\n');
                }
                gc_free(lines.items[i]);
        }

        vec_push(s, '\0');

        return mkstring(s.items);
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
                        error("unterminated string literal starting on line %d", Start.line);
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

inline static bool
readhex(int ndigits, unsigned long long *k)
{
        char b[32];

        for (int i = 0; i < ndigits; ++i) {
                if (!isxdigit(C(i))) {
                        return false;
                } else  {
                        b[i] = C(i);
                }
        }

        b[ndigits] = '\0';

        if (sscanf(b, "%llx", k) != 1) {
                return false;
        }

        while (ndigits --> 0) {
                nextchar();
        }

        return true;
}

struct SDSLine {
        vec(char *) strs;
        vec(char *) fmts;
        vec(LexState) exprs;
};

static struct token
lexspecialdocstring(void)
{
        vec(struct SDSLine) lines;
        vec_init(lines);

        vec(char) str;
        vec_init(str);

        vec_push(lines, (struct SDSLine){0});

        char *fmt = NULL;

        int ndelim = 0;
        while (C(0) == '"') {
                nextchar();
                ndelim += 1;
        }

        eat_line_ending();

        while (!end_of_docstring('"', ndelim) && C(0) != '\0') {
                if (eat_line_ending()) {
                        vec_push(str, '\n');
                        vec_push(str, '\0');
                        vec_push(vec_last(lines)->strs, str.items);
                        vec_init(str);
                        vec_push(lines, (struct SDSLine){0});
                } else if (C(0) == '{') {
                        vec_push(str, '\0');
                        vec_push(vec_last(lines)->strs, str.items);
                        vec_init(str);
                        nextchar();
                        LexState st = state;
                        st.end = lexexpr();
                        nextchar();
                        vec_push(vec_last(lines)->fmts, NULL);
                        vec_push(vec_last(lines)->exprs, st);
                } else switch (C(0)) {
                        case '\0': goto Unterminated;
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
                                        printf("Appending \\r\n");
                                        nextchar();
                                        vec_push(str, '\r');
                                        continue;
                                case 't':
                                        nextchar();
                                        vec_push(str, '\t');
                                        continue;
                                case 'x':
                                        {
                                                unsigned long long b;

                                                nextchar();

                                                if (!readhex(2, &b)) {
                                                        error("invalid hexadecimal byte value in string: \\x%.2s", SRC);
                                                }

                                                vec_push(str, b);

                                                continue;
                                        }
                                case 'u':
                                case 'U':
                                        {
                                                int c = C(0);
                                                int ndigits = (c == 'u') ? 4 : 8;
                                                unsigned long long codepoint;

                                                nextchar();

                                                if (!readhex(ndigits, &codepoint)) {
                                                        error("expected %d hexadecimal digits after \\%c in string", ndigits, c, SRC);
                                                }

                                                if (!utf8proc_codepoint_valid(codepoint)) {
                                                        error("invalid Unicode codepoint in string: %u", codepoint);
                                                }

                                                unsigned char bytes[4];
                                                int n = utf8proc_encode_char(codepoint, bytes);
                                                vec_push_n(str, (char *)bytes, n);

                                                continue;
                                        }
                                }
                        default:
                                vec_push(str, nextchar());
                }
        }

        if (!end_of_docstring('"', ndelim)) {
                error("unterminated docstring starting on line %d", Start.line);
        }

        // The only characters on this line before the docstring terminator should be whitespace
        for (int i = 0; i < str.count; ++i) {
                if (!isspace(str.items[i])) {
                        error("illegal docstring terminator on line %d", state.loc.line);
                }
        }

        while (ndelim --> 0) {
                nextchar();
        }

        int nstrip = str.count;
        vec_empty(str);

        struct token special = mktoken(TOKEN_SPECIAL_STRING);
        vec_init(special.strings);
        vec_init(special.fmts);
        vec_init(special.expressions);
        vec_init(special.starts);
        vec_init(special.ends);

        vec_pop(lines);

        for (int i = 0; i < lines.count; ++i) {
                int off = 0;
                while (off < nstrip && isspace(lines.items[i].strs.items[0][off])) {
                        off += 1;
                }
                printf("Adding str of len %zu\n", strlen(lines.items[i].strs.items[0] + off));
                if (i == 0) {
                        vec_push(special.strings, lines.items[i].strs.items[0] + off);
                } else {
                        char const *s = gc_alloc(strlen(*vec_last(special.strings)) + strlen(lines.items[i].strs.items[0] + off) + 1);
                        strcpy(s, *vec_last(special.strings));
                        strcat(s, lines.items[i].strs.items[0] + off);
                        *vec_last(special.strings) = s;
                }
                for (int j = 0; j < lines.items[i].exprs.count; ++j) {
                        vec_push(special.expressions, lines.items[i].exprs.items[j]);
                        vec_push(special.fmts, lines.items[i].fmts.items[j]);
                        vec_push(special.strings, lines.items[i].strs.items[j + 1]);
                        printf("Adding str of len %zu\n", strlen(lines.items[i].strs.items[j + 1]));
                }
        }

        *strrchr(*vec_last(special.strings), '\n') = '\0';

        return special;

Unterminated:
        error("unterminated docstring literal starting on line %d", special.start.line);
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
                        case 'x':
                                {
                                        unsigned long long b;

                                        nextchar();

                                        if (!readhex(2, &b)) {
                                                error("invalid hexadecimal byte value in string: \\x%.2s", SRC);
                                        }

                                        vec_push(str, b);

                                        continue;
                                }
                        case 'u':
                        case 'U':
                                {
                                        int c = C(0);
                                        int ndigits = (c == 'u') ? 4 : 8;
                                        unsigned long long codepoint;

                                        nextchar();

                                        if (!readhex(ndigits, &codepoint)) {
                                                error("expected %d hexadecimal digits after \\%c in string", ndigits, c, SRC);
                                        }

                                        if (!utf8proc_codepoint_valid(codepoint)) {
                                                error("invalid Unicode codepoint in string: %u", codepoint);
                                        }

                                        unsigned char bytes[4];
                                        int n = utf8proc_encode_char(codepoint, bytes);
                                        vec_push_n(str, (char *)bytes, n);

                                        continue;
                                }
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
        error("unterminated string literal starting on line %d", special.start.line);
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
                case 'i': flags |= PCRE_CASELESS;  break;
                case 'u': flags |= PCRE_UTF8;      break;
                case 'm': flags |= PCRE_MULTILINE; break;
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

static intmax_t
uatou(char const *s, char const **end, int base)
{
        char num[128];
        int n = 0;
        int i = 0;

        for (;; ++i) {
                if (n == sizeof num - 1) {
                        error("invalid numeric literal: %.*s", n, num);
                }
                if (isxdigit(s[i]) || ((base == 0) && s[i] == 'x' && i == 1)) {
                        num[n++] = s[i];
                } else if (s[i] != '_') {
                        break;
                }
        }

        num[n] = '\0';

        *end = s + i;

        return strtoull(num, NULL, base);
}

static struct token
lexnum(void)
{
        char *end;
        errno = 0;
        int base;

        intmax_t integer;
        // Allow integer constants like 0b10100010
        if (C(0) == '0' && C(1) == 'b') {
                integer = uatou(SRC + 2, &end, 2);
        } else {
                integer = uatou(SRC, &end, 0);
        }

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
                if (integer < INT_MIN ||
                    integer > INT_MAX ||
                    ((integer = strtoull(end + 1, &end, (base = integer)), errno != 0))) {
                        error(
                                "invalid base %s%.*s%s used in integer literal",
                                TERM(36),
                                n,
                                SRC,
                                TERM(39)
                        );
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

static struct token
lexlinecomment(void)
{
        // skip the leading slashes
        nextchar();
        nextchar();

        while (isspace(C(0)) && C(0) != '\n') {
                nextchar();
        }

        vec(char) comment;
        vec_init(comment);

        while (C(0) != '\n' && C(0) != '\0') {
                vec_push(comment, nextchar());
        }

        while (comment.count > 0 && isspace(*vec_last(comment))) {
                vec_pop(comment);
        }

        vec_push(comment, '\0');

        struct token t = mktoken(TOKEN_COMMENT);
        t.comment = comment.items;

        return t;
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

        Start = state.loc;

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
                        struct token t = lexlinecomment();
                        if (state.keep_comments) {
                                return t;
                        } else if (skipspace()) {
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
                        if (C(1) == '\'' && C(2) == '\'') {
                                return lexdocstring();
                        } else {
                                return lexrawstr();
                        }
                } else if (C(0) == '"') {
                        if (C(1) == '"' && C(2) == '"') {
                                return lexspecialdocstring();
                        } else {
                                return lexspecialstr();
                        }
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
                .keep_comments = false,
                .ctx = LEX_PREFIX
        };

        Start = state.loc;

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
lex_need_nl(void)
{
        state.need_nl = true;
}

bool
lex_keep_comments(bool b)
{
        bool old = state.keep_comments;
        state.keep_comments = b;
        return old;
}

void
lex_end(void)
{
        state = *vec_pop(states);
}

struct location
lex_pos(void)
{
        return state.loc;
}

int
lex_peek_char(char *out)
{

        int gstate = 0;

        int cp1;
        int cp2;

        char const *s = SRC;

        int n = utf8proc_iterate((uint8_t *)s, END - s, &cp1);

        if (n == -1) {
                return 0;
        }

        for (;;) {
                while (n --> 0) {
                        *out++ = *s++;
                }

                n = utf8proc_iterate((uint8_t *)s, END - s, &cp2);
                if (n == -1) {
                        break;
                }

                if (utf8proc_grapheme_break_stateful(cp1, cp2, &gstate)) {
                        break;
                }
        }

        *out++ = '\0';

        return s - SRC;
}

bool
lex_next_char(char *out)
{
        int n = lex_peek_char(out);

        if (n == 0) {
                return false;
        }

        while (n --> 0) {
                nextchar();
        }

        return true;
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
