#include <ctype.h>
#include <string.h>
#include <stdio.h>

#include "token.h"
#include "compiler.h"
#include "xd.h"
#include "ty.h"

enum {
        SC_NONE,
        SC_IDENT,       /* default identifiers */
        SC_PUNCT,       /* brackets, dots, commas, arrows */
        SC_KEYWORD,     /* control flow: if, for, while, let, return, ... */
        SC_OPERATOR,    /* +, -, ==, =>, ... */
        SC_TYPE,        /* type references (PascalCase, tagged as type) */
        SC_DECL,        /* class/tag/trait keywords, module names, params */
        SC_STRING,      /* string and interpolated string literals */
        SC_FUNCTION,    /* function names and calls */
        SC_FIELD,       /* member and field access */
        SC_BUILTIN,     /* typeof, __set_type__ */
        SC_REGEX,       /* regex literals */
        SC_COMMENT,     /* comments, semicolons */
        SC_LITERAL,     /* true, false, nil, numbers, import, use */
        SC_PREPROC,     /* preprocessor, macros, template syntax */
        SC_COUNT
};

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

/*
 * If hexes is NULL, return a palette using the native 16-color
 * terminal palette (works everywhere, respects the user's theme).
 * Otherwise, build 24-bit true-color escape sequences from hex codes.
 */
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

/* ── Palettes ───────────────────────────────────────────────────────── */

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

/* ── Theme lookup ──────────────────────────────────────────────────── */

static struct {
        char const *name;
        char const **palette;
} const themes[] = {
        { "gruvbox",           gruvbox           },
        { "gruvbox-material",  gruvbox_material  },
        { "github-light",      github_light      },
        { "github-dark",       github_dark       },
        { "monokai",           monokai           },
        { "one-dark",          one_dark          },
        { "catppuccin-mocha",  catppuccin_mocha  },
        { "catppuccin",        catppuccin_mocha  },
        { "dracula",           dracula           },
        { "nord",              nord              },
        { "solarized-dark",    solarized_dark    },
        { "solarized",         solarized_dark    },
        { "tokyonight",        tokyonight        },
        { "tokyo-night",       tokyonight        },
        { "rose-pine",         rose_pine         },
};

static char const **
find_palette(char const *name)
{
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

/* ── Token classification ───────────────────────────────────────────── */

static bool
is_type_name(char const *id)
{
        if (id == NULL || !isupper((unsigned char)id[0]))
                return false;

        for (char const *p = id + 1; *p != '\0'; ++p) {
                if (*p == '_')
                        return false;
        }

        return true;
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

        if (is_type_name(t->identifier))
                return SC_TYPE;

        /* Check if followed by '(' => function call */
        if (t->end.s != NULL && source != NULL) {
                char const *p = t->end.s;
                while (*p == ' ' || *p == '\t') ++p;
                if (*p == '(')
                        return SC_FUNCTION;
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

        /* Punctuation */
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

        /* Operators */
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

/* ── Public API ─────────────────────────────────────────────────────── */

void
syntax_highlight(
        Ty *ty,
        byte_vector *out,
        Module const *mod,
        usize start,
        usize end,
        char const *attr,
        char const *theme
)
{
        char const *source = mod->source;

        if (source == NULL)
                return;

        TokenVector const *tokens = &mod->all_tokens;
        char const **pal = build_palette(find_palette(theme));

        char const *attr_on = attr ? attr : "";
        char const *attr_off = attr ? "\x1b[0m" : "";

        usize pos = start;

        for (isize i = find_first(tokens, pos); i < vN(*tokens); ++i) {
                Token const *t = v_(*tokens, i);

                if (t->ctx == LEX_FAKE)
                        continue;

                if (t->type == TOKEN_END)
                        break;

                u32 tstart = t->start.byte;
                u32 tend   = t->end.byte;

                /* Skip tokens outside the expression range */
                if (tend <= start)
                        continue;
                if (tstart >= end)
                        break;

                /* Clamp to expression range */
                if (tstart < start) tstart = start;
                if (tend > end)     tend = end;

                /* Emit uncolored source between previous position and this token */
                if (tstart > pos) {
                        sxdf(
                                out,
                                "%s%.*s%s",
                                attr_on,
                                tstart - pos,
                                source + pos,
                                attr_off
                        );
                }

                int sc = token_color(t, source);

                if (sc != SC_NONE && pal[sc][0] != '\0') {
                        sxdf(
                                out,
                                "%s%s%.*s%s",
                                pal[sc],
                                attr_on,
                                tend - tstart,
                                source + tstart,
                                "\x1b[0m"
                        );
                } else {
                        sxdf(
                                out,
                                "%s%.*s%s",
                                attr_on,
                                tend - tstart,
                                source + tstart,
                                attr_off
                        );
                }

                pos = tend;
        }

        /* Emit any remaining source after the last token */
        if (pos < end) {
                sxdf(
                        out,
                        "%s%.*s%s",
                        attr_on,
                        end - pos,
                        source + pos,
                        attr_off
                );
        }

        svP(*out, '\0');
        vvX(*out);
}
