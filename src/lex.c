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

#include <pcre2.h>
#include <utf8proc.h>

#include "vec.h"
#include "token.h"
#include "test.h"
#include "util.h"
#include "lex.h"
#include "log.h"

static Token
dotoken(Ty *ty, int ctx);

enum {
        MAX_OP_LEN = 8,
};

static char const *filename;
static Location Start;

static jmp_buf jb;

LexState *lxst;
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

noreturn static void
error(Ty *ty, char const *fmt, ...)
{
        va_list ap;

        ErrorBuffer.count = 0;

        dump(
                &ErrorBuffer,
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

        va_start(ap, fmt);
        vdump(&ErrorBuffer, fmt, ap);
        va_end(ap);

        char const *prefix = state.loc.s;
        while (prefix[-1] != '\n' && prefix[-1] != '\0')
                --prefix;

        int before = state.loc.s - prefix;
        int after = (state.loc.s[0] == '\0') ? 0 : strcspn(state.loc.s + 1, "\n");

        dump(
                &ErrorBuffer,
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

        dump(
                &ErrorBuffer,
                "\t%*s%s^%s",
                6 + before,
                " ",
                TERM(31),
                TERM(39)
        );

        longjmp(jb, 1);
}

static Token
mktoken(Ty *ty, int type)
{
        return (Token) {
                .type = type,
                .start = Start,
                .end = state.loc,
                .ctx = state.ctx,
                .nl = (state.need_nl || type == TOKEN_NEWLINE)
        };
}

static Token
mkid(Ty *ty, char *id, char *module, bool raw)
{
        return (Token) {
                .type = TOKEN_IDENTIFIER,
                .identifier = id,
                .module = module,
                .start = Start,
                .end = state.loc,
                .nl = state.need_nl,
                .ctx = state.ctx,
                .raw = raw
        };
}

static Token
mkstring(Ty *ty, char *string)
{
        return (Token) {
                .type = TOKEN_STRING,
                .string = string,
                .start = Start,
                .end = state.loc,
                .nl = state.need_nl,
                .ctx = state.ctx
        };
}

static Token
mkregex(Ty *ty, char const *pat, int flags, bool detailed)
{
        int err;
        size_t offset;
        char err_buf[256];

        pcre2_code *re = pcre2_compile(
                (PCRE2_SPTR)pat,
                PCRE2_ZERO_TERMINATED,
                flags,
                &err,
                &offset,
                NULL
        );

        if (re == NULL) {
                pcre2_get_error_message(err, (uint8_t *)err_buf, sizeof err_buf);
                error(
                        ty,
                        "error compiling regular expression: %s/%s/%s at position %zu: %s",
                        TERM(36),
                        pat,
                        TERM(39),
                        offset,
                        err_buf
                );
        }

        err = pcre2_jit_compile(re, PCRE2_JIT_COMPLETE);
        if (err < 0) {
                pcre2_get_error_message(err, (uint8_t *)err_buf, sizeof err_buf);
                error(
                        ty,
                        "error JIT-compiling regular expression: %s/%s/%s: %s",
                        TERM(36),
                        pat,
                        TERM(39),
                        err_buf
                );
        }

        Regex *r = amA(sizeof *r);
        r->pattern = pat;
        r->pcre2 = re;
        r->gc = false;
        r->detailed = detailed;

        pcre2_pattern_info(re, PCRE2_INFO_CAPTURECOUNT, &r->ncap);

        return (Token) {
                .type = TOKEN_REGEX,
                .regex = r,
                .start = Start,
                .end = state.loc,
                .ctx = state.ctx
        };
}

static Token
mkreal(Ty *ty, float real)
{
        return (Token) {
                .type = TOKEN_REAL,
                .real = real,
                .start = Start,
                .end = state.loc,
                .nl = state.need_nl,
                .ctx = state.ctx
        };
}

static Token
mkinteger(Ty *ty, intmax_t k)
{
        return (Token) {
                .type = TOKEN_INTEGER,
                .integer = k,
                .start = Start,
                .end = state.loc,
                .nl = state.need_nl,
                .ctx = state.ctx
        };
}

static Token
mkkw(Ty *ty, int kw)
{
        return (Token) {
                .type = TOKEN_KEYWORD,
                .keyword = kw,
                .start = Start,
                .end = state.loc,
                .nl = state.need_nl,
                .ctx = state.ctx
        };
}

static unsigned char
nextchar(Ty *ty)
{
        // TODO: Column address should probably just be codepoint offset
#if 0
        if (n < 0) {
                error(
                        ty,
                        "source is not valid UTF-8: "
                        "decoding failed at byte offset %jd: "
                        "%#hhx %#hhx",
                        SRC - state.start,

                );
        }
#endif
        unsigned char c = C(0);

        switch (c) {
        case '\0':
                return '\0';

        case '\n':
                state.loc.line += 1;
                state.loc.col = 0;
                state.blank_line = true;

        default:
                state.blank_line = false;
        case '\t':
        case ' ':
                state.loc.col += 1;
        }

        SRC += 1;
        state.loc.byte += 1;

        return c;
}

inline static bool
starts_id(int c)
{
        return isalpha(c)
            || (c == '_')
            || (c > 0xC0)
            || (c == '`');
}

inline static int
_count(Ty *ty, int i)
{
        int n = 0;

        while (C(i + n) == '_') {
                n += 1;
        }

        return n;
}

static bool
haveid(Ty *ty)
{
        return starts_id(C(0))
            || (C(0) == ':' && C(1) == ':' && starts_id(C(2)))
            || (C(0) == '$' && isdigit(C(1 + _count(ty, 1))));
}

static bool
skipspace(Ty *ty)
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
                        nextchar(ty);
                }
        }

        nl &= state.need_nl;
        state.need_nl &= !nl;

        Start = state.loc;

        return nl;
}

inline static bool
idchar(int c)
{
        return isalnum(c) || c == '_' || (c & 0x80);
}

/* lexes an identifier or a keyword */
static Token
lexword(Ty *ty)
{
        vec(char) module;
        vec(char) word;

        vec_init(module);
        vec_init(word);

        bool raw = false;
        bool has_module = false;

        for (;;) {
                if (C(0) == '$') {
                        avP(word, nextchar(ty));

                        while (C(0) == '_') {
                                avP(word, nextchar(ty));
                        }

                        while (isdigit(C(0))) {
                                avP(word, nextchar(ty));
                        }

                        continue;
                }

                if (C(0) == '`') {
                        raw = true;

                        nextchar(ty);

                        while (C(0) != '`') {
                                if (C(0) == '\0') {
                                        error(ty, "unterminated raw identifier");
                                }

                                avP(word, nextchar(ty));
                        }

                        nextchar(ty);
                }

                for (;;) {
                        if (idchar(C(0))) {
                                avP(word, nextchar(ty));
                        } else if (C(0) == '-' && idchar(C(1))) {
                                nextchar(ty);
                                avP(word, toupper(nextchar(ty)));
                        } else {
                                break;
                        }
                }

                if (C(0) == ':' && C(1) == ':' && ++has_module) {
                        nextchar(ty);
                        nextchar(ty);

                        if (module.count != 0)
                                avP(module, '/');

                        if (word.count != 0)
                                avPn(module, word.items, word.count);
                        word.count = 0;

                        if (!haveid(ty)) {
                                error(
                                        ty,
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
                avP(word, nextchar(ty));

        if (has_module)
                avP(module, '\0');

        avP(word, '\0');

        char *w = word.items;
        char *m = module.items;

        int keyword;
        if (!raw && (keyword = keyword_get_number(w)) != -1) {
                state.need_nl |= (
                        keyword == KEYWORD_IMPORT
                     || keyword == KEYWORD_OPERATOR
                     || keyword == KEYWORD_NAMESPACE
                );
                return mkkw(ty, keyword);
        }

        return mkid(ty, w, m, raw);
}

static bool
end_of_docstring(Ty *ty, char c, int ndelim)
{
        for (int i = 0; i < ndelim; ++i) {
                if (C(i) != c) {
                        return false;
                }
        }

        return true;
}

static bool
eat_line_ending(Ty *ty)
{
        if (C(0) == '\n') {
                nextchar(ty);
                return true;
        }

        if (C(0) == '\r' && C(1) == '\n') {
                nextchar(ty);
                nextchar(ty);
                return true;
        }

        return false;
}

static Token
lexdocstring(Ty *ty)
{
        vec(char *) lines;
        vec(char) line;

        vec_init(lines);
        vec_init(line);

        int ndelim = 0;
        while (C(0) == '\'') {
                nextchar(ty);
                ndelim += 1;
        }

        eat_line_ending(ty);

        while (!end_of_docstring(ty, '\'', ndelim) && C(0) != '\0') {
                if (eat_line_ending(ty)) {
                        avP(line, '\0');
                        avP(lines, line.items);
                        vec_init(line);
                } else {
                        avP(line, nextchar(ty));
                }
        }

        if (!end_of_docstring(ty, '\'', ndelim)) {
                error(ty, "unterminated docstring starting on line %d", Start.line + 1);
        }

        // The only characters on this line before the docstring terminator should be whitespace
        for (int i = 0; i < line.count; ++i) {
                if (!isspace(line.items[i])) {
                        error(ty, "illegal docstring terminator on line %d", state.loc.line + 1);
                }
        }

        while (ndelim --> 0) {
                nextchar(ty);
        }

        int nstrip = line.count;

        vec(char) s;
        vec_init(s);

        for (int i = 0; i < lines.count; ++i) {
                int off = 0;
                while (off < nstrip && isspace(lines.items[i][off])) {
                        off += 1;
                }
                while (lines.items[i][off] != '\0') {
                        avP(s, lines.items[i][off++]);
                }
                if (i + 1 != lines.count) {
                        avP(s, '\n');
                }
        }

        avP(s, '\0');

        return mkstring(ty, s.items);
}

static Token
lexrawstr(Ty *ty)
{
        vec(char) str;
        vec_init(str);

        nextchar(ty);

        while (C(0) != '\'') {
                switch (C(0)) {
                case '\0':
                Unterminated:
                        error(ty, "unterminated string literal starting on line %d", Start.line + 1);
                case '\\':
                        nextchar(ty);
                        switch (C(0)) {
                        case '\0':
                                goto Unterminated;
                        case 'n':
                                nextchar(ty);
                                avP(str, '\n');
                                continue;
                        case 'r':
                                nextchar(ty);
                                avP(str, '\r');
                                continue;
                        case 't':
                                nextchar(ty);
                                avP(str, '\t');
                                continue;
                        }
                        // fallthrough
                default:
                           avP(str, nextchar(ty));
                }
        }

        nextchar(ty);

        avP(str, '\0');

        return mkstring(ty, str.items);
}

static void
skiptoken(Ty *ty)
{
        LexState save = state;

        SAVE_(jmp_buf, jb);

        static int d = -1;

        d += 1;

        if (setjmp(jb) != 0) {
                state = save;
                nextchar(ty);
        } else {
                Token t = dotoken(ty, LEX_PREFIX);
                printf("%*sSkipped: %s\n", d * 4, "", token_show(ty, &t));
        }

        d -= 1;

        RESTORE_(jb);
}

static char const *
lexexpr(Ty *ty)
{
        for (int depth = 1; depth > 0;) {
                switch (C(0)) {
                case '\0':
                        error(ty, "unterminated expression in interpolated string");

                case '{': depth += 1; break;
                case '}': depth -= 1; break;

                case '/':
                case '\'':
                case '"':
                case '`':
                        skiptoken(ty);
                        continue;
                }
                nextchar(ty);
        }

        return SRC - 1;
}

inline static bool
readhex(Ty *ty, int ndigits, unsigned long long *k)
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
                nextchar(ty);
        }

        return true;
}

struct SDSLine {
        vec(char *) strs;
        vec(LexState) exprs;
};

static Token
lexspecialdocstring(Ty *ty)
{
        vec(struct SDSLine) lines;
        vec_init(lines);

        vec(char) str;
        vec_init(str);

        avP(lines, ((struct SDSLine){0}));

        int ndelim = 0;
        while (C(0) == '"') {
                nextchar(ty);
                ndelim += 1;
        }

        eat_line_ending(ty);

        Location start = Start;

        while (!end_of_docstring(ty, '"', ndelim) && C(0) != '\0') {
                if (eat_line_ending(ty)) {
                        avP(str, '\n');
                        avP(str, '\0');
                        avP(vvL(lines)->strs, str.items);
                        vec_init(str);
                        avP(lines, (struct SDSLine){0});
                } else if (C(0) == '{') {
                        avP(str, '\0');
                        avP(vvL(lines)->strs, str.items);
                        vec_init(str);
                        nextchar(ty);
                        LexState st = state;
                        st.end = lexexpr(ty);
                        avP(vvL(lines)->exprs, st);
                } else switch (C(0)) {
                        case '\0': goto Unterminated;
                        case '\\':
                                nextchar(ty);
                                switch (C(0)) {
                                case '\0':
                                        goto Unterminated;
                                case 'n':
                                        nextchar(ty);
                                        avP(str, '\n');
                                        continue;
                                case 'r':
                                        nextchar(ty);
                                        avP(str, '\r');
                                        continue;
                                case 't':
                                        nextchar(ty);
                                        avP(str, '\t');
                                        continue;
                                case 'x':
                                        {
                                                unsigned long long b;

                                                nextchar(ty);

                                                if (!readhex(ty, 2, &b)) {
                                                        error(ty, "invalid hexadecimal byte value in string: \\x%.2s", SRC);
                                                }

                                                avP(str, b);

                                                continue;
                                        }
                                case 'u':
                                case 'U':
                                        {
                                                int c = C(0);
                                                int ndigits = (c == 'u') ? 4 : 8;
                                                unsigned long long codepoint;

                                                nextchar(ty);

                                                if (!readhex(ty, ndigits, &codepoint)) {
                                                        error(ty, "expected %d hexadecimal digits after \\%c in string", ndigits, c, SRC);
                                                }

                                                if (!utf8proc_codepoint_valid(codepoint)) {
                                                        error(ty, "invalid Unicode codepoint in string: %u", codepoint);
                                                }

                                                unsigned char bytes[4];
                                                int n = utf8proc_encode_char(codepoint, bytes);
                                                avPn(str, (char *)bytes, n);

                                                continue;
                                        }
                                }
                        default:
                                avP(str, nextchar(ty));
                }
        }

        if (!end_of_docstring(ty, '"', ndelim)) {
                error(ty, "unterminated docstring starting on line %d", Start.line + 1);
        }

        // The only characters on this line before the docstring terminator should be whitespace
        for (int i = 0; i < str.count; ++i) {
                if (!isspace(str.items[i])) {
                        error(ty, "illegal docstring terminator on line %d", state.loc.line + 1);
                }
        }

        while (ndelim --> 0) {
                nextchar(ty);
        }

        int nstrip = str.count;

        SpecialString *special = amA0(sizeof *special);

        vvX(lines);

        for (int i = 0; i < lines.count; ++i) {
                int off = 0;
                while (off < nstrip && strchr("\t ", (lines.items[i].strs.items[0][off])) != NULL) {
                        off += 1;
                }
                if (i == 0) {
                        avP(special->strings, lines.items[i].strs.items[0] + off);
                } else {
                        char *s = amA(strlen(*vvL(special->strings)) + strlen(lines.items[i].strs.items[0] + off) + 1);
                        strcpy(s, *vvL(special->strings));
                        strcat(s, lines.items[i].strs.items[0] + off);
                        *vvL(special->strings) = s;
                }
                for (int j = 0; j < lines.items[i].exprs.count; ++j) {
                        avP(special->expressions, lines.items[i].exprs.items[j]);
                        avP(special->strings, lines.items[i].strs.items[j + 1]);
                }
        }

        *strrchr(*vvL(special->strings), '\n') = '\0';

        Token t = mktoken(ty, TOKEN_SPECIAL_STRING);
        t.special = special;
        t.start = start;

        return t;

Unterminated:
        error(ty, "unterminated docstring literal starting on line %d", Start.line + 1);
}

Token
lexspecialstr(Ty *ty)
{
        return (Token) {0};
}

static Token
lex_ss_string(Ty *ty)
{
        vec(char) str = {0};

        for (;;) {
                switch (C(0)) {
                case '\0':
                        goto Unterminated;

                case '"':
                case '{':
                case '}':
                        avP(str, '\0');
                        return mkstring(ty, str.items);

                case '\\':
                        nextchar(ty);
                        switch (C(0)) {
                        case '\0':
                                goto Unterminated;
                        case 'n':
                                nextchar(ty);
                                avP(str, '\n');
                                continue;
                        case 'r':
                                nextchar(ty);
                                avP(str, '\r');
                                continue;
                        case 't':
                                nextchar(ty);
                                avP(str, '\t');
                                continue;
                        case 'x':
                                {
                                        unsigned long long b;

                                        nextchar(ty);

                                        if (!readhex(ty, 2, &b)) {
                                                error(ty, "invalid hexadecimal byte value in string: \\x%.2s", SRC);
                                        }

                                        avP(str, b);

                                        continue;
                                }
                        case 'u':
                        case 'U':
                                {
                                        int c = C(0);
                                        int ndigits = (c == 'u') ? 4 : 8;
                                        unsigned long long codepoint;

                                        nextchar(ty);

                                        if (!readhex(ty, ndigits, &codepoint)) {
                                                error(ty, "expected %d hexadecimal digits after \\%c in string", ndigits, c, SRC);
                                        }

                                        if (!utf8proc_codepoint_valid(codepoint)) {
                                                error(ty, "invalid Unicode codepoint in string: %u", codepoint);
                                        }

                                        unsigned char bytes[4];
                                        int n = utf8proc_encode_char(codepoint, bytes);
                                        avPn(str, (char *)bytes, n);

                                        continue;
                                }
                        case '>':
                                nextchar(ty);

                                while (str.count > 0 && isspace(*vvL(str))) {
                                        if (*vvL(str) == '\n') break;
                                        str.count -= 1;
                                }

                                continue;
                        case '<':
                                nextchar(ty);
                                nextchar(ty);
                                continue;
                        }
                        /* fallthrough */
                default:
                        avP(str, nextchar(ty));
                        break;

                }
        }

Unterminated:
        error(
                ty,
                "unterminated string literal starting on line %d",
                Start.line + 1
        );
}

static Token
lexregex(Ty *ty)
{
        vec(char) pat;
        vec_init(pat);

        nextchar(ty);

        while (C(0) != '/') {
                switch (C(0)) {
                case '\0': goto Unterminated;
                case '\\':
                        if (C(1) == '\0') {
                                goto Unterminated;
                        }
                        if (C(1) == '\\') {
                                avP(pat, nextchar(ty));
                        } else if (C(1) == '/') {
                                nextchar(ty);
                        }
                        /* fallthrough */
                default:
                           avP(pat, nextchar(ty));
                }
        }

        nextchar(ty) == '/';

        int flags = 0;
        bool detailed = false;

        while (isalpha(C(0))) {
                switch (C(0)) {
                case 'i': flags |= PCRE2_CASELESS;  break;
                case 'u': flags |= PCRE2_UTF;       break;
                case 'm': flags |= PCRE2_MULTILINE; break;
                case 'x': flags |= PCRE2_EXTENDED;  break;
                case 'v': detailed = true;          break;
                default:  error(ty, "invalid regex flag: %s'%c'%s", TERM(36), C(0), TERM(39));
                }
                nextchar(ty);
        }

        avP(pat, '\0');

        return mkregex(ty, pat.items, flags, detailed);

Unterminated:
        avP(pat, '\0');
        error(ty, "unterminated regular expression: %s/%.20s%s...", TERM(36), pat.items, TERM(39));
}

static intmax_t
uatou(Ty *ty, char const *s, char const **end, int base)
{
        char num[128];
        int n = 0;
        int i = 0;

        for (;; ++i) {
                if (n == sizeof num - 1) {
                        error(ty, "invalid numeric literal: %.*s", n, num);
                }
                if (
                        (isdigit(s[i]) && (s[i] - '0') < base)
                     || (base == 16 && isxdigit(s[i]))
                ) {
                        num[n++] = s[i];
                } else if (s[i] != '_') {
                        break;
                }
        }

        num[n] = '\0';
        *end = s + i;

        errno = 0;

        return strtoull(num, NULL, base);
}

static Token
lexnum(Ty *ty, bool float_ok)
{
        char *end;

        int base = (C(0) != '0') ? 10 : (
                   (C(1) == 'b') ? (nextchar(ty), nextchar(ty), 2)
                 : (C(1) == 'o') ? (nextchar(ty), nextchar(ty), 8)
                 : (C(1) == 'x') ? (nextchar(ty), nextchar(ty), 16)
                 : /*----------------------------------------*/ 8
        );

        intmax_t integer = uatou(ty, SRC, (char const **)&end, base);

        if (errno != 0) {
                char const *err = strerror(errno);
                error(ty, "invalid numeric literal: %c%s", tolower(err[0]), err + 1);
        }

        int n = end - SRC;
        Token num;

        if (
                float_ok && (
                        (C(n) == 'e')
                     || (C(n) == 'E')
                     || (
                                C(n) == '.'
                             && !isalpha(C(n + 1))
                             && C(n + 1) != '_'
                             && C(n + 1) != '.'
                        )
                )
        ) {
                errno = 0;
                double real = strtod(SRC, &end);
                n = end - SRC;

                if (errno != 0) {
                        char const *err = strerror(errno);
                        error(ty, "invalid numeric literal: %c%s", tolower(err[0]), err + 1);
                }

                if (isalnum(C(n))) {
                        error(
                                ty,
                                "trailing character after numeric literal: %s'%c'%s",
                                TERM(36),
                                C(n),
                                TERM(39)
                        );
                }

                while (SRC != end) nextchar(ty);

                num = mkreal(ty, real);
        } else if (C(n) == 'r') {
                if (integer < INT_MIN ||
                    integer > INT_MAX ||
                    ((integer = strtoull(end + 1, &end, (base = integer)), errno != 0))) {
                        error(
                                ty,
                                "invalid base %s%.*s%s used in integer literal",
                                TERM(36),
                                n,
                                SRC,
                                TERM(39)
                        );
                }
                while (SRC != end) nextchar(ty);
                num = mkinteger(ty, integer);
        } else {
                if (isalnum(C(n))) {
                        error(
                                ty,
                                "trailing character after numeric literal: %s'%c'%s",
                                TERM(36),
                                C(n),
                                TERM(39)
                        );
                }

                while (SRC != end) nextchar(ty);

                num = mkinteger(ty, integer);
        }

        return num;
}

static Token
lexop(Ty *ty)
{
        char op[MAX_OP_LEN + 1] = {0};
        size_t i = 0;
        int type;

        bool touching_id = idchar(C(-1))
                        || C(-1) == '?'
                        || C(-1) == '!';

        while (
                contains(OperatorCharset, C(0)) ||
                (
                        C(0) == ':' &&
                        (
                                C(-1) != '*' ||
                                i > 1 ||
                                (
                                        contains(OperatorCharset, C(1)) &&
                                        C(1) != '-'
                                )
                        )
                )
        ) {
                /* Special case to make dict literals less annoying (e.g. apply(f, kwargs=%{}) */
                if (C(0) == '%' && C(1) == '{' && i != 0)
                        break;

                /* Another one: --@i should decrement @i, not apply --@ to i */
                if (i > 0 && C(0) == '@' && idchar(C(1)))
                        break;

                /* Another one :^) We want a=#self to mean a = #self, not a #= self...
                 * This comes up primarily with default function arguments.
                 */
                if (
                        touching_id
                     && i == 1
                     && C(-1) == '='
                     && (C(0) != '=' || contains(OperatorCharset, C(1)))
                ) {
                        return mktoken(ty, '=');
                }

                if (i == MAX_OP_LEN) {
                        error(
                                ty,
                                "operator contains too many characters: %s'%s...'%s",
                                TERM(36),
                                op,
                                TERM(39)
                        );
                } else {
                        op[i++] = nextchar(ty);
                }
        }

        if (
                (type = operator_get_token_type(op)) == -1
             || (
                        (strcmp(op, ".") == 0)
                     && isspace(C(-2))
                     && isspace(C(0))
                )
        ) {
                Token t = mktoken(ty, TOKEN_USER_OP);
                t.identifier = sclonea(ty, op);
                return t;
        }

        return mktoken(ty, type);
}

static Token
lexlinecomment(Ty *ty)
{
        // skip the leading slashes
        nextchar(ty);
        nextchar(ty);

        while (isspace(C(0)) && C(0) != '\n') {
                nextchar(ty);
        }

        vec(char) comment;
        vec_init(comment);

        while (C(0) != '\n' && C(0) != '\0') {
                avP(comment, nextchar(ty));
        }

        while (comment.count > 0 && isspace(*vvL(comment))) {
                vvX(comment);
        }

        avP(comment, '\0');

        Token t = mktoken(ty, TOKEN_COMMENT);
        t.comment = comment.items;

        Start = state.loc;

        return t;
}

static Token
lexcomment(Ty *ty)
{
        // skip the /*
        nextchar(ty);
        nextchar(ty);

        int level = 1;

        vec(char) comment;
        vec_init(comment);

        while (C(0) != '\0' && level != 0) {
                if (C(0) == '/' && C(1) == '*')
                        ++level;
                else if (C(0) == '*' && C(1) == '/')
                        --level;
                char c = nextchar(ty);
                if (level != 0)
                        avP(comment, c);
        }

        if (level != 0)
                error(ty, "unterminated comment");

        avP(comment, '\0');

        // skip the final /
        nextchar(ty);

        Token t = mktoken(ty, TOKEN_COMMENT);
        t.comment = comment.items;

        Start = state.loc;

        return t;
}

static Token
dotoken(Ty *ty, int ctx)
{
        Location start = Start = state.loc;

        state.ctx = ctx;

        if (ctx == LEX_FMT) {
                return lex_ss_string(ty);
        }

        if (skipspace(ty)) {
                Start = start; // :^)
                return mktoken(ty, TOKEN_NEWLINE);
        }

        if (SRC >= END) {
                return (Token) {
                        .type = TOKEN_END,
                        .start = start,
                        .end = state.loc,
                        .ctx = state.ctx
                };
        }

        if (C(0) == '/' && C(1) == '*') {
                Token t = lexcomment(ty);
                if (state.keep_comments) {
                        return t;
                } else if (skipspace(ty)) {
                        return mktoken(ty, TOKEN_NEWLINE);
                } else {
                        return dotoken(ty, ctx);
                }
        } else if (C(0) == '/' && C(1) == '/') {
                Token t = lexlinecomment(ty);
                if (state.keep_comments) {
                        return t;
                } else if (skipspace(ty)) {
                        return mktoken(ty, TOKEN_NEWLINE);
                } else {
                        return dotoken(ty, ctx);
                }
        } else if (C(0) == '#' && C(1) == '|') {
                nextchar(ty);
                nextchar(ty);
                state.need_nl = true;
                return mktoken(ty, TOKEN_DIRECTIVE);
        } else if (ctx == LEX_PREFIX && C(0) == '/') {
                return lexregex(ty);
        } else if (haveid(ty)) {
                return lexword(ty);
        } else if (C(0) == ':' && C(1) == ':' && !contains(OperatorCharset, C(2))) {
                nextchar(ty);
                nextchar(ty);
                return mktoken(ty, TOKEN_CHECK_MATCH);
        } else if (C(0) == '-' && C(1) == '>' && ctx == LEX_PREFIX) {
                nextchar(ty);
                nextchar(ty);
                return mktoken(ty, TOKEN_ARROW);
        } else if (C(0) == '-' && C(1) != '-' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, TOKEN_MINUS);
        } else if (C(0) == '#' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, '#');
        } else if (C(0) == '&' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, '&');
        } else if (C(0) == '*' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, TOKEN_STAR);
        } else if (C(0) == '!' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, TOKEN_BANG);
        } else if (C(0) == '$' && C(1) == '$' && C(2) == '[') {
                nextchar(ty);
                nextchar(ty);
                nextchar(ty);
                return mktoken(ty, TOKEN_TEMPLATE_BEGIN);
        } else if (C(0) == '$' && C(1) == '$' && C(2) == ']') {
                nextchar(ty);
                nextchar(ty);
                nextchar(ty);
                return mktoken(ty, TOKEN_TEMPLATE_END);
        } else if (C(0) == '$' && C(1) == '$') {
                nextchar(ty);
                nextchar(ty);
                return mktoken(ty, '$$');
        } else if (C(0) == '?' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, TOKEN_QUESTION);
        } else if (C(0) == '$' && C(1) == '"') {
                nextchar(ty);

                Token t = dotoken(ty, ctx);

                for (int i = 0; i < t.special->expressions.count; ++i) {
                        char *dollar = strrchr(t.special->strings.items[i], '$');
                        if (dollar != NULL && dollar[1] == '\0') {
                                *dollar = '\0';
                                avP(t.special->e_is_param, true);
                        } else {
                                avP(t.special->e_is_param, false);
                        }
                }

                t.start = start;
                t.type = TOKEN_FUN_SPECIAL_STRING;

                return t;
        } else if (C(0) == '$' && ctx == LEX_PREFIX) {
                nextchar(ty);
                return mktoken(ty, '$');
        } else if (
                contains(OperatorCharset, C(0))
             || (
                        C(0) == ':'
                     && (
                                isspace(C(-1))
                             || (
                                        contains(OperatorCharset, C(1))
                                     && C(1) != '-'
                                     && C(1) != '*'
                                     && C(1) != '+'
                                     && C(1) != '.'
                                     && C(1) != '%'
                                )
                        )
                )
        ) {
                return lexop(ty);
        } else if (isdigit(C(0))) {
                return lexnum(ty, ctx == LEX_PREFIX);
        } else if (C(0) == '\'') {
                if (C(1) == '\'' && C(2) == '\'') {
                        return lexdocstring(ty);
                } else {
                        return lexrawstr(ty);
                }
        } else if (C(0) == '"') {
                nextchar(ty);
                return mktoken(ty, '"');
        } else if (C(0) == '"') {
                if (C(1) == '"' && C(2) == '"') {
                        return lexspecialdocstring(ty);
                } else {
                        return lexspecialstr(ty);
                }
        } else if (C(0) == '.' && C(1) == '.') {
                nextchar(ty);
                nextchar(ty);
                if (C(0) == '.')
                        return nextchar(ty), mktoken(ty, TOKEN_DOT_DOT_DOT);
                else
                        return mktoken(ty, TOKEN_DOT_DOT);
        } else {
                return mktoken(ty, nextchar(ty));
        }
}

Token
lex_token(Ty *ty, LexContext ctx)
{
        if (setjmp(jb) != 0) {
                return (Token) {
                        .type = TOKEN_ERROR,
                        .start = Start,
                        .end = state.loc,
                        .nl = state.need_nl,
                        .ctx = state.ctx
                };
        }

        return dotoken(ty, ctx);
}

void
lex_init(Ty *ty, char const *file, char const *src)
{
        lxst = &state;

        filename = file;

        state = (LexState) {
                .loc = (Location) {
                        .s = src,
                        .byte = 0,
                        .line = 0,
                        .col = 0
                },
                .start = src,
                .end = src + strlen(src),
                .need_nl = false,
                .keep_comments = true,
                .ctx = LEX_PREFIX
        };

        Start = state.loc;

        /*
         * Eat the shebang if there is one.
         */
        if (C(0) == '#' && C(1) == '!') {
                while (SRC != END && C(0) != '\n') {
                        nextchar(ty);
                }
        }
}

void
lex_start(Ty *ty, LexState const *st)
{
        avP(states, state);
        state = *st;
}

void
lex_save(Ty *ty, LexState *s)
{
        *s = state;
}

void
lex_rewind(Ty *ty, Location const *where)
{
        state.loc = *where;
}

void
lex_need_nl(Ty *ty, bool need)
{
        //PLOG("lex_need_nl(%d): %.*s~", (int)need, (int)strcspn(SRC, "\n"), SRC);
        state.need_nl = need;
}

bool
lex_keep_comments(Ty *ty, bool keep)
{
        SWAP(bool, keep, state.keep_comments);
        return keep;
}

void
lex_end(Ty *ty)
{
        state = *vvX(states);
}

Location
lex_pos(Ty *ty)
{
        return state.loc;
}

int
lex_peek_byte(Ty *ty)
{
        return C(0);
}

int
lex_peek_char(Ty *ty, char *out)
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
lex_next_char(Ty *ty, char *out)
{
        int n = lex_peek_char(ty, out);

        if (n == 0) {
                return false;
        }

        while (n --> 0) {
                nextchar(ty);
        }

        return true;
}

/* vim: set sts=8 sw=8 expandtab: */
