#include <ctype.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>

#include "token.h"
#include "compiler.h"
#include "highlight.h"
#include "str.h"
#include "xd.h"
#include "ty.h"

enum {
        SC_NONE,
        SC_IDENT,
        SC_PUNCT,
        SC_KEYWORD,
        SC_OPERATOR,
        SC_TYPE,
        SC_DECL,
        SC_STRING,
        SC_FUNCTION,
        SC_FIELD,
        SC_BUILTIN,
        SC_REGEX,
        SC_COMMENT,
        SC_LITERAL,
        SC_PREPROC,
        SC_COUNT
};

struct highlight {
        byte_vector *out;
        LiteralStyle style;
        usize pos;
        usize start;
        usize end;
};

typedef struct regex_token_ctx {
        char const *pattern;
        usize length;
        usize scan;
        bool seen;
        bool quoted;
        u8 *literal;
} RegexTokenContext;

#define emit(s, k, d) ((emit)(ty, (s), (k), (d)))
static void
(emit)(Ty *ty, Bytes s, StringPart kind, void *data)
{
        struct highlight *h = data;

        char const *styles[] = {
                h->style.text,
                h->style.escape,
                h->style.invalid
        };

        usize start = max(h->pos, h->start);
        usize end = zminu(h->pos + s.length, h->end);

        if (start < end) {
                char const *style = styles[kind];
                svPn(*h->out, style, strlen(style));
                svPn(*h->out, s.data + start - h->pos, end - start);
        }

        h->pos += s.length;
}

void
highlight_string(Ty *ty, byte_vector *out, Bytes string, LiteralStyle style)
{
        struct highlight h = { .out = out, .style = style, .end = SIZE_MAX };

        emit(z_bytes("'"), STRING_TEXT, &h);
        str_escape(ty, string, '\'', (emit), &h);
        emit(z_bytes("'"), STRING_TEXT, &h);
}

static usize
source_escape_length(Bytes source, usize i, bool rich)
{
        usize left = source.length - i;
        i32 cp;
        int n;

        if (left == 1) {
                return 1;
        }

        if (rich) {
                switch (source.data[i + 1]) {
                case 'x': return min(4, left);
                case 'u': return min(6, left);
                case 'U': return min(10, left);
                case '<': return min(3, left);
                }
        }

        n = utf8proc_iterate(b_(source, i + 1), left - 1, &cp);

        return 1 + max(n, 1);
}

static void
string_parts(Ty *ty, Token const *token, Bytes source, struct highlight *h)
{
        bool rich = (token->ctx == LEX_FMT)
                  | (token->ctx == LEX_XFMT)
                  | (token->ctx == LEX_DOC)
                  ;
        bool doc = (source.length >= 3)
                && (memcmp(source.data, "'''", 3) == 0);

        usize start = 0;
        usize i = 0;

        while (!doc && i < source.length) {
                if (source.data[i] != '\\') {
                        i += 1;
                        continue;
                }

                emit(b_sub(source, start, i - start), STRING_TEXT, h);
                usize n = source_escape_length(source, i, rich);
                emit(b_sub(source, i, n), STRING_ESCAPE, h);
                i += n;
                start = i;
        }

        emit(b_drop(source, start), STRING_TEXT, h);
}

static int
regex_token(pcre2_callout_enumerate_block *token, void *data)
{
        RegexTokenContext *ctx = data;
        usize i = min((usize)token->pattern_position, ctx->length);

        if (ctx->seen && i <= ctx->scan) {
                return 0;
        }

        while (ctx->quoted && ctx->scan + 1 < i) {
                if (
                        (ctx->pattern[ctx->scan] == '\\')
                     && (ctx->pattern[ctx->scan + 1] == 'E')
                ) {
                        ctx->quoted = false;
                }
                ctx->scan += 1;
        }

        if (
                !ctx->quoted
             && (i >= 2)
             && (ctx->pattern[i - 2] == '\\')
             && (ctx->pattern[i - 1] == 'Q')
        ) {
                ctx->quoted = true;
        }

        ctx->scan = i;
        ctx->seen = true;

        if (
                (i == ctx->length)
             || (!ctx->quoted && contains("\\.^$|([)", ctx->pattern[i]))
        ) {
                return 0;
        }

        i32 cp;
        int n = utf8proc_iterate(
                (u8 const *)ctx->pattern + i,
                ctx->length - i,
                &cp
        );
        memset(ctx->literal + i, 1, max(n, 1));

        return 0;
}

static u8 *
regex_literal_map(Ty *ty, Regex const *regex, usize n)
{
        u8 *literal = smA0(max(n, 1));
        u32 options = 0;
        int error;
        usize offset;
        pcre2_code *tokens;

        pcre2_pattern_info(regex->pcre2, PCRE2_INFO_ARGOPTIONS, &options);
        tokens = pcre2_compile(
                (u8 const *)regex->pattern,
                n,
                options | PCRE2_AUTO_CALLOUT,
                &error,
                &offset,
                NULL
        );

        if (tokens != NULL) {
                RegexTokenContext ctx = {
                        .pattern = regex->pattern,
                        .length  = n,
                        .literal = literal
                };
                pcre2_callout_enumerate(tokens, regex_token, &ctx);
                pcre2_code_free(tokens);
        }

        return literal;
}

static void
regex_parts(Ty *ty, Regex const *regex, struct highlight *h)
{
        usize n = strlen(regex->pattern);
        u8 *literal = s_eq(h->style.text, h->style.escape)
                    ? NULL
                    : regex_literal_map(ty, regex, n);
        byte_vector buf = {0};
        StringPart prev = STRING_TEXT;
        usize i = 0;

        while (i < n) {
                i32 cp;
                isize w = utf8proc_iterate((u8 const *)regex->pattern + i, n - i, &cp);
                StringPart kind = STRING_ESCAPE;
                char esc[12];
                char c = 0;
                Bytes part = BYTES(esc, 0);

                if (w < 0) {
                        w = 1;
                        kind = STRING_INVALID;
                        part.length = ty_snprintf(
                                esc,
                                sizeof esc,
                                "\\x%02x",
                                (unsigned)(u8)regex->pattern[i]
                        );
                        goto Emit;
                }

                switch (cp) {
                case '\a': c = 'a'; break;
                case '\f': c = 'f'; break;
                case '\n': c = 'n'; break;
                case '\r': c = 'r'; break;
                case '\t': c = 't'; break;
                case '/':  c = '/'; break;
                }

                if (c != 0) {
                        esc[0] = '\\';
                        esc[1] = c;
                        part.length = 2;
                        goto Emit;
                }

                switch (utf8proc_category(cp)) {
                case UTF8PROC_CATEGORY_CN:
                case UTF8PROC_CATEGORY_CC:
                case UTF8PROC_CATEGORY_CF:
                case UTF8PROC_CATEGORY_ZL:
                case UTF8PROC_CATEGORY_ZP:
                        if (cp < 0x80) {
                                part.length = ty_snprintf(esc, sizeof esc, "\\x%02x", (unsigned)cp);
                        } else {
                                part.length = ty_snprintf(esc, sizeof esc, "\\x{%x}", (unsigned)cp);
                        }
                        break;

                default:
                        kind = (literal == NULL || literal[i]) ? STRING_TEXT : STRING_ESCAPE;
                        part = BYTES(regex->pattern + i, w);
                        break;
                }

Emit:
                if (kind != prev && vN(buf) != 0) {
                        emit(v_bytes(buf), prev, h);
                        vN(buf) = 0;
                }
                svPn(buf, part.data, part.length);
                prev = kind;
                i += w;
        }

        if (vN(buf) != 0) {
                emit(v_bytes(buf), prev, h);
        }
}

void
highlight_regex(Ty *ty, byte_vector *out, Regex const *regex, LiteralStyle style)
{
        struct highlight h = {
                .out   = out,
                .style = style,
                .end   = SIZE_MAX
        };

        regex_parts(ty, regex, &h);
}

static void
highlight_token(Ty *ty, Token const *token, Bytes source, struct highlight *h)
{
        switch (token->type) {
        case TOKEN_STRING:
        case TOKEN_SPECIAL_STRING:
        case TOKEN_FUN_SPECIAL_STRING:
                string_parts(ty, token, source, h);
                break;

        case TOKEN_REGEX:
                emit(b_take(source, 1), STRING_TEXT, h);
                regex_parts(ty, token->regex, h);
                emit(b_drop(source, h->pos), STRING_TEXT, h);
                break;

        default:
                emit(source, STRING_TEXT, h);
                break;
        }
}

inline static void
hex_to_rgb(char const *hex, int *r, int *g, int *b)
{
        unsigned rgb;
        sscanf(hex + 1, "%06x", &rgb);
        *r = (rgb >> 16) & 0xFF;
        *g = (rgb >>  8) & 0xFF;
        *b = (rgb >>  0) & 0xFF;
}

static char palette_buf[SC_COUNT][32];

static char const **
build_palette(char const *hexes[SC_COUNT])
{
        static char const *result[SC_COUNT];

        result[SC_NONE] = "";

        if (hexes == NULL) {
                result[SC_IDENT]    = "";
                result[SC_PUNCT]    = "\x1b[2m";
                result[SC_KEYWORD]  = "\x1b[1;31m";
                result[SC_OPERATOR] = "\x1b[33m";
                result[SC_TYPE]     = "\x1b[1;33m";
                result[SC_DECL]     = "\x1b[33m";
                result[SC_STRING]   = "\x1b[32m";
                result[SC_FUNCTION] = "\x1b[92m";
                result[SC_FIELD]    = "\x1b[34m";
                result[SC_BUILTIN]  = "\x1b[1;34m";
                result[SC_REGEX]    = "\x1b[36m";
                result[SC_COMMENT]  = "\x1b[90m";
                result[SC_LITERAL]  = "\x1b[35m";
                result[SC_PREPROC]  = "\x1b[95m";
                return result;
        }

        for (int i = 1; i < SC_COUNT; ++i) {
                if (hexes[i] == NULL) {
                        result[i] = "";
                        continue;
                }

                int r, g, b;
                hex_to_rgb(hexes[i], &r, &g, &b);

                if (i == SC_TYPE) {
                        snprintf(
                                palette_buf[i],
                                sizeof palette_buf[i],
                                "\x1b[1;38;2;%d;%d;%dm",
                                r, g, b
                        );
                } else {
                        snprintf(
                                palette_buf[i],
                                sizeof palette_buf[i],
                                "\x1b[38;2;%d;%d;%dm",
                                r, g, b
                        );
                }

                result[i] = palette_buf[i];
        }

        return result;
}



static char const *gruvbox[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#ebdbb2",
        [SC_PUNCT]    = "#a89984",
        [SC_KEYWORD]  = "#fb4934",
        [SC_OPERATOR] = "#fe8019",
        [SC_TYPE]     = "#fabd2f",
        [SC_DECL]     = "#fabd2f",
        [SC_STRING]   = "#b8bb26",
        [SC_FUNCTION] = "#8ec07c",
        [SC_FIELD]    = "#83a598",
        [SC_BUILTIN]  = "#83a598",
        [SC_REGEX]    = "#8ec07c",
        [SC_COMMENT]  = "#928374",
        [SC_LITERAL]  = "#d3869b",
        [SC_PREPROC]  = "#d3869b",
};

static char const *gruvbox_material[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#d4be98",
        [SC_PUNCT]    = "#a89984",
        [SC_KEYWORD]  = "#ea6962",
        [SC_OPERATOR] = "#e78a4e",
        [SC_TYPE]     = "#d8a657",
        [SC_DECL]     = "#d8a657",
        [SC_STRING]   = "#a9b665",
        [SC_FUNCTION] = "#89b482",
        [SC_FIELD]    = "#7daea3",
        [SC_BUILTIN]  = "#7daea3",
        [SC_REGEX]    = "#89b482",
        [SC_COMMENT]  = "#928374",
        [SC_LITERAL]  = "#d3869b",
        [SC_PREPROC]  = "#d3869b",
};

static char const *gruvbox_material_light[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#654735",
        [SC_PUNCT]    = "#a89984",
        [SC_KEYWORD]  = "#9d0006",
        [SC_OPERATOR] = "#9d0006",
        [SC_TYPE]     = "#b57614",
        [SC_DECL]     = "#b57614",
        [SC_STRING]   = "#3c7319",
        [SC_FUNCTION] = "#076678",
        [SC_FIELD]    = "#654735",
        [SC_BUILTIN]  = "#076678",
        [SC_REGEX]    = "#3c7319",
        [SC_COMMENT]  = "#a89984",
        [SC_LITERAL]  = "#8f3f71",
        [SC_PREPROC]  = "#af2528",
};

static char const *github_light[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#24292e",
        [SC_PUNCT]    = "#24292e",
        [SC_KEYWORD]  = "#d73a49",
        [SC_OPERATOR] = "#d73a49",
        [SC_TYPE]     = "#6f42c1",
        [SC_DECL]     = "#6f42c1",
        [SC_STRING]   = "#032f62",
        [SC_FUNCTION] = "#6f42c1",
        [SC_FIELD]    = "#005cc5",
        [SC_BUILTIN]  = "#005cc5",
        [SC_REGEX]    = "#032f62",
        [SC_COMMENT]  = "#6a737d",
        [SC_LITERAL]  = "#005cc5",
        [SC_PREPROC]  = "#d73a49",
};

static char const *github_dark[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#c9d1d9",
        [SC_PUNCT]    = "#c9d1d9",
        [SC_KEYWORD]  = "#ff7b72",
        [SC_OPERATOR] = "#ff7b72",
        [SC_TYPE]     = "#ffa657",
        [SC_DECL]     = "#ffa657",
        [SC_STRING]   = "#a5d6ff",
        [SC_FUNCTION] = "#d2a8ff",
        [SC_FIELD]    = "#79c0ff",
        [SC_BUILTIN]  = "#79c0ff",
        [SC_REGEX]    = "#a5d6ff",
        [SC_COMMENT]  = "#8b949e",
        [SC_LITERAL]  = "#79c0ff",
        [SC_PREPROC]  = "#ff7b72",
};

static char const *monokai[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#f8f8f2",
        [SC_PUNCT]    = "#f8f8f2",
        [SC_KEYWORD]  = "#f92672",
        [SC_OPERATOR] = "#f92672",
        [SC_TYPE]     = "#a6e22e",
        [SC_DECL]     = "#66d9ef",
        [SC_STRING]   = "#e6db74",
        [SC_FUNCTION] = "#a6e22e",
        [SC_FIELD]    = "#f8f8f2",
        [SC_BUILTIN]  = "#66d9ef",
        [SC_REGEX]    = "#e6db74",
        [SC_COMMENT]  = "#75715e",
        [SC_LITERAL]  = "#ae81ff",
        [SC_PREPROC]  = "#f92672",
};

static char const *one_dark[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#abb2bf",
        [SC_PUNCT]    = "#abb2bf",
        [SC_KEYWORD]  = "#c678dd",
        [SC_OPERATOR] = "#56b6c2",
        [SC_TYPE]     = "#e5c07b",
        [SC_DECL]     = "#e5c07b",
        [SC_STRING]   = "#98c379",
        [SC_FUNCTION] = "#61afef",
        [SC_FIELD]    = "#e06c75",
        [SC_BUILTIN]  = "#61afef",
        [SC_REGEX]    = "#98c379",
        [SC_COMMENT]  = "#5c6370",
        [SC_LITERAL]  = "#d19a66",
        [SC_PREPROC]  = "#c678dd",
};

static char const *catppuccin_mocha[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#cdd6f4",
        [SC_PUNCT]    = "#bac2de",
        [SC_KEYWORD]  = "#cba6f7",
        [SC_OPERATOR] = "#89dceb",
        [SC_TYPE]     = "#f9e2af",
        [SC_DECL]     = "#f9e2af",
        [SC_STRING]   = "#a6e3a1",
        [SC_FUNCTION] = "#89b4fa",
        [SC_FIELD]    = "#f38ba8",
        [SC_BUILTIN]  = "#89b4fa",
        [SC_REGEX]    = "#a6e3a1",
        [SC_COMMENT]  = "#6c7086",
        [SC_LITERAL]  = "#fab387",
        [SC_PREPROC]  = "#f5c2e7",
};

static char const *dracula[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#f8f8f2",
        [SC_PUNCT]    = "#f8f8f2",
        [SC_KEYWORD]  = "#ff79c6",
        [SC_OPERATOR] = "#ff79c6",
        [SC_TYPE]     = "#8be9fd",
        [SC_DECL]     = "#8be9fd",
        [SC_STRING]   = "#f1fa8c",
        [SC_FUNCTION] = "#50fa7b",
        [SC_FIELD]    = "#f8f8f2",
        [SC_BUILTIN]  = "#8be9fd",
        [SC_REGEX]    = "#f1fa8c",
        [SC_COMMENT]  = "#6272a4",
        [SC_LITERAL]  = "#bd93f9",
        [SC_PREPROC]  = "#ff79c6",
};

static char const *nord[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#d8dee9",
        [SC_PUNCT]    = "#eceff4",
        [SC_KEYWORD]  = "#81a1c1",
        [SC_OPERATOR] = "#81a1c1",
        [SC_TYPE]     = "#8fbcbb",
        [SC_DECL]     = "#8fbcbb",
        [SC_STRING]   = "#a3be8c",
        [SC_FUNCTION] = "#88c0d0",
        [SC_FIELD]    = "#d8dee9",
        [SC_BUILTIN]  = "#88c0d0",
        [SC_REGEX]    = "#ebcb8b",
        [SC_COMMENT]  = "#616e88",
        [SC_LITERAL]  = "#b48ead",
        [SC_PREPROC]  = "#5e81ac",
};

static char const *solarized_dark[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#839496",
        [SC_PUNCT]    = "#586e75",
        [SC_KEYWORD]  = "#859900",
        [SC_OPERATOR] = "#859900",
        [SC_TYPE]     = "#b58900",
        [SC_DECL]     = "#b58900",
        [SC_STRING]   = "#2aa198",
        [SC_FUNCTION] = "#268bd2",
        [SC_FIELD]    = "#839496",
        [SC_BUILTIN]  = "#268bd2",
        [SC_REGEX]    = "#2aa198",
        [SC_COMMENT]  = "#586e75",
        [SC_LITERAL]  = "#d33682",
        [SC_PREPROC]  = "#cb4b16",
};

static char const *solarized_light[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#657b83",
        [SC_PUNCT]    = "#93a1a1",
        [SC_KEYWORD]  = "#859900",
        [SC_OPERATOR] = "#859900",
        [SC_TYPE]     = "#b58900",
        [SC_DECL]     = "#b58900",
        [SC_STRING]   = "#2aa198",
        [SC_FUNCTION] = "#268bd2",
        [SC_FIELD]    = "#657b83",
        [SC_BUILTIN]  = "#268bd2",
        [SC_REGEX]    = "#2aa198",
        [SC_COMMENT]  = "#93a1a1",
        [SC_LITERAL]  = "#d33682",
        [SC_PREPROC]  = "#cb4b16",
};

static char const *tokyonight[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#c0caf5",
        [SC_PUNCT]    = "#a9b1d6",
        [SC_KEYWORD]  = "#bb9af7",
        [SC_OPERATOR] = "#89ddff",
        [SC_TYPE]     = "#2ac3de",
        [SC_DECL]     = "#e0af68",
        [SC_STRING]   = "#9ece6a",
        [SC_FUNCTION] = "#7aa2f7",
        [SC_FIELD]    = "#73daca",
        [SC_BUILTIN]  = "#7aa2f7",
        [SC_REGEX]    = "#9ece6a",
        [SC_COMMENT]  = "#565f89",
        [SC_LITERAL]  = "#ff9e64",
        [SC_PREPROC]  = "#bb9af7",
};

static char const *rose_pine[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#e0def4",
        [SC_PUNCT]    = "#908caa",
        [SC_KEYWORD]  = "#31748f",
        [SC_OPERATOR] = "#908caa",
        [SC_TYPE]     = "#f6c177",
        [SC_DECL]     = "#f6c177",
        [SC_STRING]   = "#ebbcba",
        [SC_FUNCTION] = "#9ccfd8",
        [SC_FIELD]    = "#c4a7e7",
        [SC_BUILTIN]  = "#9ccfd8",
        [SC_REGEX]    = "#ebbcba",
        [SC_COMMENT]  = "#6e6a86",
        [SC_LITERAL]  = "#eb6f92",
        [SC_PREPROC]  = "#c4a7e7",
};

static char const *muted[SC_COUNT] = {
        [SC_NONE]     = NULL,
        [SC_IDENT]    = "#8a8a8a",
        [SC_PUNCT]    = "#707070",
        [SC_KEYWORD]  = "#a0a0a0",
        [SC_OPERATOR] = "#909090",
        [SC_TYPE]     = "#9a9a8a",
        [SC_DECL]     = "#9a9a8a",
        [SC_STRING]   = "#8a9a7a",
        [SC_FUNCTION] = "#8a9a9a",
        [SC_FIELD]    = "#7a8a9a",
        [SC_BUILTIN]  = "#7a8a9a",
        [SC_REGEX]    = "#8a9a7a",
        [SC_COMMENT]  = "#606060",
        [SC_LITERAL]  = "#9a8a9a",
        [SC_PREPROC]  = "#9a8a9a",
};

static struct {
        char const *name;
        char const **palette;
} const themes[] = {
        { "gruvbox",                   gruvbox                },
        { "gruvbox-material",          gruvbox_material       },
        { "gruvbox-material-light",    gruvbox_material_light },
        { "github-light",              github_light           },
        { "github-dark",               github_dark            },
        { "monokai",                   monokai                },
        { "muted",                     muted                  },
        { "one-dark",                  one_dark               },
        { "catppuccin-mocha",          catppuccin_mocha       },
        { "catppuccin",                catppuccin_mocha       },
        { "dracula",                   dracula                },
        { "nord",                      nord                   },
        { "solarized-dark",            solarized_dark         },
        { "solarized",                 solarized_dark         },
        { "solarized-light",           solarized_light        },
        { "tokyonight",                tokyonight             },
        { "tokyo-night",               tokyonight             },
        { "rose-pine",                 rose_pine              },
};

static char const **
find_palette(char const *name)
{
        if (name == NULL) {
                name = getenv("TY_DEFAULT_COLORS");
        }

        if (name == NULL) {
                return NULL;
        }

        for (int i = 0; i < countof(themes); ++i) {
                if (s_eq(name, themes[i].name)) {
                        return themes[i].palette;
                }
        }

        return NULL;
}



static bool
probably_a_type(char const *id)
{
        if (!isupper((u8)id[0])) {
                return false;
        }

        for (usize i = 1; id[i] != '\0'; ++i) {
                if (islower((u8)id[i])) {
                        return true;
                }
        }
        
        return false;
}

static int
keyword_color(int kw)
{
        switch (kw) {
        case KEYWORD_TRUE:
        case KEYWORD_FALSE:
        case KEYWORD_NIL:
        case KEYWORD_IMPORT:
        case KEYWORD_USE:
                return SC_LITERAL;

        case KEYWORD_CLASS:
        case KEYWORD_TAG:
        case KEYWORD_TRAIT:
                return SC_DECL;

        case KEYWORD_TYPEOF:
        case KEYWORD_SET_TYPE:
                return SC_BUILTIN;

        case KEYWORD_DEFINED:
                return SC_PREPROC;

        default:
                return SC_KEYWORD;
        }
}

static int
identifier_color(Token const *t, char const *source)
{
        switch (t->tag) {
        case TT_OPERATOR: return SC_OPERATOR;
        case TT_KEYWORD:  return SC_KEYWORD;
        case TT_TYPE:     return SC_TYPE;
        case TT_MACRO:    return SC_PREPROC;
        case TT_MODULE:   return SC_DECL;
        case TT_PARAM:    return SC_DECL;
        case TT_PUNCT:    return SC_COMMENT;
        default:          break;
        }

        if (probably_a_type(t->identifier)) {
                return SC_TYPE;
        }

        if (t->end.s != NULL && source != NULL) {
                char const *p = t->end.s;
                while (*p == ' ' || *p == '\t') {
                        ++p;
                }
                if (*p == '(') {
                        return SC_FUNCTION;
                }
        }

        switch (t->tag) {
        case TT_FUNC:   return SC_FUNCTION;
        case TT_CALL:   return SC_FUNCTION;
        case TT_MEMBER: return SC_FIELD;
        case TT_FIELD:  return SC_FIELD;
        default:        return SC_IDENT;
        }
}

static int
token_color(Token const *t, char const *source)
{
        switch (t->type) {
        case TOKEN_IDENTIFIER:
                return identifier_color(t, source);

        case TOKEN_KEYWORD:
                return keyword_color(t->keyword);

        case TOKEN_INTEGER:
        case TOKEN_REAL:
                return SC_LITERAL;

        case TOKEN_STRING:
                return SC_STRING;

        case TOKEN_SPECIAL_STRING:
        case TOKEN_FUN_SPECIAL_STRING:
                return SC_STRING;

        case TOKEN_COMMENT:
                return SC_COMMENT;

        case TOKEN_REGEX:
                return SC_REGEX;

        case TOKEN_DIRECTIVE:
                return SC_PREPROC;

        case TOKEN_TEMPLATE_BEGIN:
        case TOKEN_TEMPLATE_END:
        case '$$':
                return SC_PREPROC;

        case '(':
                return (t->tag == TT_CALL) ? SC_FUNCTION : SC_PUNCT;

        case ')':
                return (t->tag == TT_CALL) ? SC_FUNCTION : SC_PUNCT;

        case '[':
        case ']':
        case '{':
        case '}':
        case '.':
        case ',':
                return SC_PUNCT;

        case TOKEN_DOT_MAYBE:
        case TOKEN_ARROW:
                return SC_PUNCT;

        case ';':
                return SC_COMMENT;
        case ':':
                return (t->tag == TT_PUNCT) ? SC_COMMENT : SC_OPERATOR;

        case '"':
                return SC_STRING;

        case TOKEN_EQ:
        case TOKEN_DBL_EQ:
        case TOKEN_INC:
        case TOKEN_DEC:
        case TOKEN_PLUS:
        case TOKEN_MINUS:
        case TOKEN_STAR:
        case TOKEN_DIV:
        case TOKEN_PERCENT:
        case '^':
        case '|':
        case '&':
        case TOKEN_LEQ:
        case TOKEN_GEQ:
        case TOKEN_PLUS_EQ:
        case TOKEN_MINUS_EQ:
        case TOKEN_STAR_EQ:
        case TOKEN_DIV_EQ:
        case TOKEN_MOD_EQ:
        case TOKEN_AT:
        case '#':
        case TOKEN_AND:
        case TOKEN_OR:
        case TOKEN_CMP:
        case TOKEN_BANG:
        case '~':
        case TOKEN_SQUIGGLY_ARROW:
        case TOKEN_FAT_ARROW:
        case '$~>':
        case TOKEN_GT:
        case TOKEN_LT:
        case TOKEN_NOT_EQ:
        case TOKEN_WTF:
        case TOKEN_SHR:
        case TOKEN_SHL:
        case TOKEN_SHL_EQ:
        case TOKEN_SHR_EQ:
        case TOKEN_CHECK_MATCH:
        case TOKEN_MAYBE_EQ:
        case TOKEN_OR_EQ:
        case TOKEN_AND_EQ:
        case TOKEN_XOR_EQ:
        case TOKEN_QUESTION:
        case TOKEN_ELVIS:
        case TOKEN_DOT_DOT:
        case TOKEN_DOT_DOT_DOT:
        case '$':
        case TOKEN_USER_OP:
        case '</':
        case '/>':
                return SC_OPERATOR;

        case TOKEN_NEWLINE:
        case TOKEN_END:
                return SC_NONE;

        default:
                return SC_NONE;
        }
}

static isize
find_first(TokenVector const *tokens, usize pos)
{
        isize lo = 0;
        isize hi = vN(*tokens);

        while (lo < hi) {
                isize mid = (lo + hi) / 2;
                Token const *t = v_(*tokens, mid);
                if (t->end.byte <= pos) {
                        lo = mid + 1;
                } else {
                        hi = mid;
                }
        }

        return lo;
}

bool
syntax_highlight(
        Ty *ty,
        byte_vector *out,
        char const *source,
        TokenVector const *tokens,
        usize start,
        usize end,
        char const *attr,
        char const *theme
)
{
        Bytes src = z_bytes(source);

        char const **pal = build_palette(find_palette(theme));
        char const *attr_on = attr ? attr : "";
        char const *attr_off = attr ? "\x1b[0m" : "";
        usize pos = start;

        if (start > end || end > bN(src)) {
                return false;
        }

        for (isize i = find_first(tokens, pos); i < vN(*tokens); ++i) {
                Token const *t = v_(*tokens, i);
                if (
                        (t->ctx == LEX_FAKE)
                     || (t->type == TOKEN_END || t->start.byte >= end)
                ) {
                        break;
                }
                usize tstart = max(pos, t->start.byte);
                usize tend   = min(end, t->end.byte);

                if (tstart >= tend) {
                        continue;
                }

                sxdf(out, "%s%.*s%s", attr_on, (int)(tstart - pos), source + pos, attr_off);

                int sc = token_color(t, source);
                int special = (t->type == TOKEN_REGEX) ? SC_BUILTIN : SC_LITERAL;
                struct highlight h = {
                        .out = out,
                        .style = {
                                .text    = sfmt("%s%s", pal[sc],      attr_on),
                                .escape  = sfmt("%s%s", pal[special], attr_on),
                                .invalid = sfmt("%s%s", pal[special], attr_on)
                        },
                        .start = tstart - t->start.byte,
                        .end   = tend   - t->start.byte
                };


                Bytes span = b_sub(src, t->start.byte, t->end.byte - t->start.byte);
                highlight_token(ty, t, span, &h);

                if (pal[sc][0] != '\0' || attr != NULL) {
                        svPn(*out, "\x1b[0m", 4);
                }

                pos = tend;
        }

        sxdf(out, "%s%.*s%s", attr_on, (int)(end - pos), source + pos, attr_off);
        svP(*out, '\0');
        vXx(*out);

        return true;
}
