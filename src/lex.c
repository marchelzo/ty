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
        MAX_ERR_LEN  = 2048
};

struct location startloc;
struct location loc;

jmp_buf jb;
bool keep_next_newline;

char errbuf[MAX_ERR_LEN + 1];

static vec(char const *) states;
static char const *chars;

static char const *opchars = "/=<~|!@$%^&*-+>";

noreturn static void
error(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        char *err = errbuf;
        err += sprintf(err, "SyntaxError at %d:%d: ", loc.line + 1, loc.col + 1);
        err[vsnprintf(err, MAX_ERR_LEN, fmt, ap)] = '\0';

        va_end(ap);

        longjmp(jb, 1);
}

static struct token
mktoken(int type)
{
        return (struct token) {
                .type = type,
                .loc  = startloc,
        };
}

static struct token
mkid(char *id, char *module)
{
        return (struct token) {
                .type = TOKEN_IDENTIFIER,
                .identifier = id,
                .module = module,
                .loc  = startloc,
        };
}

static struct token
mktag(char *tag, char *module)
{
        return (struct token) {
                .type = TOKEN_TAG,
                .tag  = tag,
                .module = module,
                .loc  = startloc,
        };
}

static struct token
mkstring(char *string)
{
        return (struct token) {
                .type = TOKEN_STRING,
                .string = string,
                .loc  = startloc,
        };
}

static struct token
mkregex(char const *pat, int flags)
{
        char const *err;
        int offset;

        pcre *re = pcre_compile(pat, flags, &err, &offset, NULL);
        if (re == NULL) {
                error("error compiling regular expression: %s: %s", err, pat + offset);
        }

        pcre_extra *extra = pcre_study(re, PCRE_STUDY_EXTRA_NEEDED | PCRE_STUDY_JIT_COMPILE, &err);
        if (extra == NULL) {
                error("error studying regular expression: %s", err);
        }

        return (struct token) {
                .type = TOKEN_REGEX,
                .regex = re,
                .extra = extra,
                .pattern = pat,
                .loc = startloc
        };
}

static struct token
mkreal(float real)
{
        return (struct token) {
                .type = TOKEN_REAL,
                .real = real,
                .loc = startloc
        };
}

static struct token
mkinteger(intmax_t k)
{
        return (struct token) {
                .type = TOKEN_INTEGER,
                .integer = k,
                .loc = startloc
        };
}

static struct token
mkkw(int kw)
{
        return (struct token) {
                .type = TOKEN_KEYWORD,
                .keyword = kw,
                .loc  = startloc,
        };
}

static char
nextchar(void)
{
        char c = *chars;

        if (c == '\n') {
                loc.line += 1;
                loc.col = 0;
        } else {
                loc.col += 1;
        }

        chars += 1;

        return c;
}

static bool
skipspace(void)
{
        bool ret = false;

        int n = 0;
        while (isspace(chars[n])) {
                if (chars[n] == '\n' && keep_next_newline) {
                        ret = true;
                        keep_next_newline = false;
                }
                n += 1;
        }

        if (chars[n] == '\0') {
                chars += n;
        } else {
                while (n --> 0) {
                        nextchar();
                }
        }

        return ret;
}

// lexes an identifier or a keyword
static struct token
lexword(void)
{
        vec(char) module;
        vec(char) word;

        vec_init(module);
        vec_init(word);

        bool tag = isupper(*chars);

        for (;;) {
                while (isalnum(*chars) || *chars == '_') {
                        vec_push(word, nextchar());
                }

                if (chars[0] == ':' && chars[1] == ':') {
                        nextchar();
                        nextchar();
                        
                        if (module.count != 0) {
                                vec_push(module, '/');
                        }

                        vec_push_n(module, word.items, word.count);
                        word.count = 0;

                        if (!isalpha(*chars) && *chars != '_') {
                                error("expected name after '::' in identifier");
                        } else {
                                tag = isupper(*chars);
                        }
                } else {
                        break;
                }
        }

        /*
         * Identifiers are allowed to end in '?' or '!'. e.g., [1, 2, 3].map!(a -> a + 1)
         */
        if (*chars == '!') {
                vec_push(word, nextchar());
        } else if (*chars == '?') {
                vec_push(word, nextchar());
        }

        if (module.count != 0) {
                vec_push(module, '\0');
        }

        vec_push(word, '\0');

        char *w = word.items;
        char *m = module.items;

        int keyword;
        if (keyword = keyword_get_number(w), keyword != -1) {
                keep_next_newline |= (keyword == KEYWORD_IMPORT);
                return mkkw(keyword);
        } else if (tag) {
                return mktag(w, m);
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

        while (*chars != '\'') {
                switch (*chars) {
                case '\0': goto unterminated;
                case '\\':
                           nextchar();
                           if (*chars == '\0') goto unterminated;
                           // fallthrough
                default:
                           vec_push(str, nextchar());
                }
        }

        assert(nextchar() == '\'');

        vec_push(str, '\0');

        return mkstring(str.items);

unterminated:

        error("unterminated string literal");
}

static char *
lexexpr(void)
{
        vec(char) e;
        vec_init(e);

        nextchar();
        while (*chars != '}') {
                switch (*chars) {
                case '\0': goto unterminated;
                case '\\':
                           nextchar();
                           if (*chars == '\0') goto unterminated;
                           if (*chars == 'n') {
                                   nextchar();
                                   vec_push(e, '\n');
                                   break;
                           }
                           // fallthrough
                default:
                           vec_push(e, nextchar());
                }
        }

        assert(nextchar() == '}');

        vec_push(e, '\0');

        return e.items;

unterminated:
        error("unterminated expression in interpolated string");
}

static struct token
lexspecialstr(void)
{
        struct token special = mktoken(TOKEN_SPECIAL_STRING);
        vec_init(special.strings);
        vec_init(special.expressions);
        vec_init(special.locations);

        vec(char) str;
        vec_init(str);


        nextchar();

start:

        while (*chars != '"') {
                switch (*chars) {
                case '\0': goto unterminated;
                case '{':  goto expr;
                case '\\':
                           nextchar();
                           if (*chars == '\0') goto unterminated;
                           if (*chars == 'n') {
                                   nextchar();
                                   vec_push(str, '\n');
                                   break;
                           }
                           // fallthrough
                default:
                           vec_push(str, nextchar());
                }
        }

        assert(nextchar() == '"');

        vec_push(str, '\0');
        vec_push(special.strings, str.items);

        return special;

expr:
        vec_push(str, '\0');
        vec_push(special.strings, str.items);
        vec_init(str);
        vec_push(special.locations, loc);
        vec_push(special.expressions, lexexpr());

        goto start;

unterminated:

        error("unterminated string literal");
}

static struct token
lexregex(void)
{
        vec(char) pat;
        vec_init(pat);

        nextchar();

        while (*chars != '/') {
                switch (*chars) {
                case '\0': goto unterminated;
                case '\\':
                           if (chars[1] == '\0') goto unterminated;
                           if (chars[1] == '/') nextchar();
                           // fallthrough
                default:
                           vec_push(pat, nextchar());
                }
        }

        assert(nextchar() == '/');

        int flags = 0;

        while (isalpha(*chars)) {
                switch (*chars) {
                case 'i': flags |= PCRE_CASELESS; break;
                default:  error("invalid regex flag: '%c'", *chars);
                }
                nextchar();
        }

        vec_push(pat, '\0');

        return mkregex(pat.items, flags);

unterminated:

        error("unterminated regular expression");
}

static struct token
lexnum(void)
{
        char *end;
        errno = 0;
        intmax_t integer = strtoull(chars, &end, 0);

        struct token num;

        if (errno != 0) {
                char const *err = strerror(errno);
                error("invalid numeric literal: %c%s", tolower(err[0]), err + 1);
        }

        if (*end == '.') {
                errno = 0;
                float real = strtof(chars, &end);

                if (errno != 0) {
                        char const *err = strerror(errno);
                        error("invalid numeric literal: %c%s", tolower(err[0]), err + 1);
                }

                if (isalnum(*end)) {
                        error("invalid trailing character after numeric literal: %c", *end);
                }

                num = mkreal(real);
        } else {
                if (isalnum(*end)) {
                        error("invalid trailing character after numeric literal: %c", *end);
                }

                num = mkinteger(integer);
        }

        while (chars != end) {
                nextchar();
        }

        return num;
}

static struct token
lexop(void)
{
        char op[MAX_OP_LEN + 1] = {0};
        size_t i = 0;
        
        while (contains(opchars, *chars)) {
                if (i == MAX_OP_LEN) {
                        error("operator contains too many characters: '%s...'", op);
                } else {
                        op[i++] = nextchar();
                }
        }

        int toktype = operator_get_token_type(op);
        if (toktype == -1) {
                // this is kinda bad
                if (op[0] == '|') {
                        chars -= (i - 1);
                        loc.col -= (i - 1);
                        return mktoken(TOKEN_BIT_OR);
                }
                error("invalid operator encountered: '%s'", op);
        }

        return mktoken(toktype);
}

static void
lexcomment(void)
{
        // skip the /*
        nextchar();
        nextchar();

        int level = 1;

        while (*chars && level != 0) {
                if (chars[0] == '/' && chars[1] == '*')
                        ++level;
                if (chars[0] == '*' && chars[1] == '/')
                        --level;
                nextchar();
        }

        if (level != 0) {
                error("unterminated comment");
        }

        // skip the final /
        nextchar();
}

struct token
lex_token(enum lex_context ctx)
{
        if (setjmp(jb) != 0) {
                return (struct token) { .type = TOKEN_ERROR, .loc = loc };
        }

        while (*chars != '\0') {
                startloc = loc;
                if (chars[0] == '/' && chars[1] == '*') {
                        lexcomment();
                } else if (ctx == LEX_PREFIX && chars[0] == '/') {
                        return lexregex();
                } else if (contains(opchars, *chars)) {
                        return lexop();
                } else if (isalpha(*chars) || *chars == '_') {
                        return lexword();
                } else if (isdigit(*chars)) {
                        return lexnum();
                } else if (*chars == '\'') {
                        return lexrawstr();
                } else if (*chars == '"') {
                        return lexspecialstr();
                } else if (chars[0] == '.' && chars[1] == '.') {
                        nextchar(); nextchar();
                        return mktoken(TOKEN_DOT_DOT);
                } else if (isspace(*chars)) {
                        if (skipspace()) {
                                return mktoken(TOKEN_NEWLINE);
                        }
                } else {
                        return mktoken(nextchar());
                }
        }

        return (struct token) { .type = TOKEN_END, .loc = loc };
}

char const *
lex_error(void)
{
        return errbuf;
}

void
lex_init(void)
{
        loc = (struct location) { 0, 0 };
        keep_next_newline = false;
        vec_init(states);
        chars = NULL;
}

void
lex_start(char const *s)
{
        vec_push(states, chars);
        chars = s;
}

void
lex_end(void)
{
        chars = *vec_pop(states);
}

static struct token *
lex(char const *s)
{
        lex_start(s);
        struct token *t = malloc(sizeof *t);
        *t = lex_token(LEX_INFIX);
        lex_end();
        return t;
}

TEST(bigop)
{
        claim(lex("\n\n+++++++++++++++++")->type == TOKEN_ERROR);
}

TEST(op)
{
        struct token op = (lex_start("&&"), lex_token(LEX_INFIX));
        claim(op.type == TOKEN_AND);
}

TEST(id)
{
        struct token id = (lex_start("_abc123"), lex_token(LEX_INFIX));
        claim(id.type == TOKEN_IDENTIFIER);
        claim(strcmp(id.identifier, "_abc123") == 0);
}

TEST(str)
{
        struct token *str = lex("'test'");
        claim(str->type == TOKEN_STRING);
        claim(strcmp(str->string, "test") == 0);

        str = lex("'test\\'ing'");
        claim(str != NULL);
        claim(str->type == TOKEN_STRING);
        claim(strcmp(str->string, "test'ing") == 0);

        str = lex("\"test'ing\"");
        claim(str != NULL);
        claim(str->type == TOKEN_SPECIAL_STRING);
        claim(strcmp(str->strings.items[0], "test'ing") == 0);
}

TEST(integer)
{
        struct token *integer = lex("010");
        claim(integer != NULL);
        claim(integer->type == TOKEN_INTEGER);
        claim(integer->integer == 010);

        integer = lex("0xFF");
        claim(integer != NULL);
        claim(integer->type == TOKEN_INTEGER);
        claim(integer->integer == 0xFF);

        integer = lex("1283");
        claim(integer != NULL);
        claim(integer->type == TOKEN_INTEGER);
        claim(integer->integer == 1283);

        integer = lex("1283ssd");

        claim(integer->type == TOKEN_ERROR);
        claim(strstr(lex_error(), "trailing") != NULL);
}

TEST(special)
{
        struct token *s = lex("\"4 + 5 = {4 + 5}\"");
        claim(s->type == TOKEN_SPECIAL_STRING);
        claim(s->strings.count == 2);
        claim(s->expressions.count == 1);
}

TEST(real)
{
#define almostequal(a, b) (fabs((a) - (b)) <= 0.001)
        struct token *real = lex("10.0");
        claim(real != NULL);
        claim(real->type == TOKEN_REAL);
        claim(almostequal(real->real, 10.0));

        real = lex("0.123");
        claim(real != NULL);
        claim(real->type == TOKEN_REAL);
        claim(almostequal(real->real, 0.123));

        real = lex("0.4");
        claim(real != NULL);
        claim(real->type == TOKEN_REAL);
        claim(almostequal(real->real, 0.4));
#undef almostequal
}

TEST(keyword)
{
        struct token kw;

        lex_start("return");
        kw = lex_token(LEX_INFIX);
        claim(kw.type == TOKEN_KEYWORD);
        claim(kw.keyword == KEYWORD_RETURN);

        lex_start("break;");
        kw = lex_token(LEX_INFIX);
        claim(kw.type == TOKEN_KEYWORD);
        claim(kw.keyword == KEYWORD_BREAK);

        lex_start("break_ing_news");
        kw = lex_token(LEX_INFIX);
        claim(kw.type == TOKEN_IDENTIFIER);
        claim(strcmp(kw.identifier, "break_ing_news") == 0);
}

TEST(invalid_op)
{
        struct token t;

        lex_start("a <$> b;");
        t = lex_token(LEX_INFIX);
        t = lex_token(LEX_INFIX);
        claim(t.type == TOKEN_ERROR);
        claim(strstr(lex_error(), "invalid operator") != NULL);
}

TEST(comment)
{
        claim((lex_start("/* /* good comment */ */"), lex_token(LEX_INFIX).type != TOKEN_ERROR));
        claim((lex_start("/* /* /* bad comment */ */"), lex_token(LEX_INFIX).type == TOKEN_ERROR));
        claim(strstr(lex_error(), "unterminated comment") != NULL);
}
