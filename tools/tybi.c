#include <ctype.h>
#include <errno.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
        char *s;
        size_t n;
        size_t cap;
} Buf;

typedef struct {
        char **items;
        size_t count;
        size_t cap;
} StrVec;

typedef struct {
        char *module;
        char *name;
        Buf sig;
} Entry;

typedef struct {
        bool typed;
        char *cname;
        char *file;
        int line;
        char *cond;
        char *doc;
        StrVec lines;
        Entry *entries;
        size_t nentries;
} Builtin;

typedef struct {
        StrVec chain;
        char *cur;
} Frame;

enum {
        P_INT,
        P_FLOAT,
        P_BOOL,
        P_STRING,
        P_BLOB,
        P_PATH,
        P_ANY
};

typedef struct {
        char *name;
        char *cname;
        int kind;
        bool nullable;
        bool required;
        char *dflt;
} Param;

static Builtin *Builtins;
static size_t NBuiltins;
static size_t CapBuiltins;
static int Errors;

static char const *CKeywords[] = {
        "auto", "break", "case", "char", "const", "continue", "default", "do",
        "double", "else", "enum", "extern", "float", "for", "goto", "if",
        "inline", "int", "long", "register", "restrict", "return", "short",
        "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
        "unsigned", "void", "volatile", "while", "bool", "true", "false",
        "ty", "argc", "kwargs", "_name__", "noreturn", "new"
};

static void *
xrealloc(void *p, size_t n)
{
        void *q = realloc(p, n);

        if (q == NULL) {
                fprintf(stderr, "tybi: out of memory\n");
                exit(1);
        }

        return q;
}

static char *
xstrndup(char const *s, size_t n)
{
        char *d = xrealloc(NULL, n + 1);

        memcpy(d, s, n);
        d[n] = '\0';

        return d;
}

static char *
xstrdup(char const *s)
{
        return xstrndup(s, strlen(s));
}

static void
bputn(Buf *b, char const *s, size_t n)
{
        if (b->n + n + 1 > b->cap) {
                b->cap = (b->n + n + 1) * 2;
                b->s = xrealloc(b->s, b->cap);
        }

        memcpy(b->s + b->n, s, n);
        b->n += n;
        b->s[b->n] = '\0';
}

static void
bputs(Buf *b, char const *s)
{
        bputn(b, s, strlen(s));
}

static void
bputc(Buf *b, char c)
{
        bputn(b, &c, 1);
}

static void
bprintf(Buf *b, char const *fmt, ...)
{
        va_list ap;
        char tmp[4096];
        int n;

        va_start(ap, fmt);
        n = vsnprintf(tmp, sizeof tmp, fmt, ap);
        va_end(ap);

        if (n < 0 || (size_t)n >= sizeof tmp) {
                fprintf(stderr, "tybi: formatted output too long\n");
                exit(1);
        }

        bputn(b, tmp, n);
}

static void
spush(StrVec *v, char *s)
{
        if (v->count == v->cap) {
                v->cap = v->cap ? v->cap * 2 : 8;
                v->items = xrealloc(v->items, v->cap * sizeof *v->items);
        }

        v->items[v->count++] = s;
}

static void
fail(Builtin const *b, char const *fmt, ...)
{
        va_list ap;

        fprintf(stderr, "%s:%d: ", b->file, b->line);
        va_start(ap, fmt);
        vfprintf(stderr, fmt, ap);
        va_end(ap);
        fputc('\n', stderr);

        Errors += 1;
}

static char *
slurp(char const *path)
{
        FILE *f = fopen(path, "rb");
        Buf b = {0};
        char tmp[65536];
        size_t n;

        if (f == NULL) {
                fprintf(stderr, "tybi: %s: %s\n", path, strerror(errno));
                exit(1);
        }

        while ((n = fread(tmp, 1, sizeof tmp, f)) > 0) {
                bputn(&b, tmp, n);
        }

        fclose(f);

        if (b.s == NULL) {
                bputs(&b, "");
        }

        return b.s;
}

static char *
trim(char const *s, char const *e)
{
        while (s < e && isspace((unsigned char)*s)) {
                s += 1;
        }

        while (e > s && isspace((unsigned char)e[-1])) {
                e -= 1;
        }

        return xstrndup(s, e - s);
}

static char *
strip_comments(char const *s)
{
        Buf b = {0};

        bputs(&b, "");

        while (*s != '\0') {
                if (s[0] == '/' && s[1] == '*') {
                        char const *end = strstr(s + 2, "*/");
                        s = (end == NULL) ? s + strlen(s) : end + 2;
                        bputc(&b, ' ');
                } else if (s[0] == '/' && s[1] == '/') {
                        break;
                } else {
                        bputc(&b, *s++);
                }
        }

        char *t = trim(b.s, b.s + b.n);

        free(b.s);

        return t;
}

static char *
current_cond(Frame const *stack, size_t n)
{
        Buf b = {0};

        bputs(&b, "");

        for (size_t i = 0; i < n; ++i) {
                if (i > 0) {
                        bputs(&b, " && ");
                }
                bprintf(&b, "(%s)", stack[i].cur);
        }

        return b.s;
}

static char *
negate_chain(StrVec const *chain)
{
        Buf b = {0};

        bputs(&b, "");

        for (size_t i = 0; i < chain->count; ++i) {
                if (i > 0) {
                        bputs(&b, " && ");
                }
                bprintf(&b, "!(%s)", chain->items[i]);
        }

        return b.s;
}

static void
directive(char const *text, Frame **stack, size_t *n, size_t *cap)
{
        char *d = strip_comments(text + 1);
        char *p = d;
        char *arg;
        Frame *top;

        while (isspace((unsigned char)*p)) {
                p += 1;
        }

        size_t kw = 0;
        while (isalpha((unsigned char)p[kw])) {
                kw += 1;
        }

        arg = trim(p + kw, p + strlen(p));

        if (
                (kw == 2 && strncmp(p, "if", 2) == 0)
             || (kw == 5 && strncmp(p, "ifdef", 5) == 0)
             || (kw == 6 && strncmp(p, "ifndef", 6) == 0)
        ) {
                if (*n == *cap) {
                        *cap = *cap ? *cap * 2 : 8;
                        *stack = xrealloc(*stack, *cap * sizeof **stack);
                }

                Buf e = {0};

                switch (kw) {
                case 2:  bprintf(&e, "%s", arg);           break;
                case 5:  bprintf(&e, "defined(%s)", arg);  break;
                default: bprintf(&e, "!defined(%s)", arg); break;
                }

                top = &(*stack)[(*n)++];
                memset(top, 0, sizeof *top);
                top->cur = e.s;
                spush(&top->chain, xstrdup(e.s));
        } else if (kw == 4 && strncmp(p, "elif", 4) == 0 && *n > 0) {
                top = &(*stack)[*n - 1];

                Buf e = {0};
                char *neg = negate_chain(&top->chain);

                bprintf(&e, "%s && (%s)", neg, arg);
                free(neg);

                top->cur = e.s;
                spush(&top->chain, xstrdup(arg));
        } else if (kw == 4 && strncmp(p, "else", 4) == 0 && *n > 0) {
                top = &(*stack)[*n - 1];
                top->cur = negate_chain(&top->chain);
        } else if (kw == 5 && strncmp(p, "endif", 5) == 0 && *n > 0) {
                *n -= 1;
        }

        free(arg);
        free(d);
}

static char const *
skip_space(char const *p)
{
        for (;;) {
                if (isspace((unsigned char)*p)) {
                        p += 1;
                } else if (p[0] == '/' && p[1] == '*') {
                        char const *end = strstr(p + 2, "*/");
                        p = (end == NULL) ? p + strlen(p) : end + 2;
                } else if (p[0] == '/' && p[1] == '/') {
                        while (*p != '\0' && *p != '\n') {
                                p += 1;
                        }
                } else {
                        return p;
                }
        }
}

static int
line_of(char const *base, char const *p)
{
        int line = 1;

        for (char const *c = base; c < p; ++c) {
                line += (*c == '\n');
        }

        return line;
}

static void
add_builtin(Builtin b)
{
        if (NBuiltins == CapBuiltins) {
                CapBuiltins = CapBuiltins ? CapBuiltins * 2 : 64;
                Builtins = xrealloc(Builtins, CapBuiltins * sizeof *Builtins);
        }

        Builtins[NBuiltins++] = b;
}

static int
bracket_depth(char const *s)
{
        int depth = 0;

        for (char const *p = s; *p != '\0'; ++p) {
                switch (*p) {
                case '(': case '[': case '{':
                        depth += 1;
                        break;

                case ')': case ']': case '}':
                        depth -= 1;
                        break;

                case '\'': case '"':
                {
                        char q = *p;
                        while (p[1] != '\0' && p[1] != q) {
                                p += (p[1] == '\\' && p[2] != '\0') + 1;
                        }
                        p += (p[1] != '\0');
                        break;
                }
                }
        }

        return depth;
}

static void
comment_lines(char const *raw, StrVec *out)
{
        bool block = (strncmp(raw, "/*", 2) == 0);
        char const *p = raw;

        while (*p != '\0') {
                char const *eol = strchr(p, '\n');
                if (eol == NULL) {
                        eol = p + strlen(p);
                }

                char const *s = p;
                char const *e = eol;

                while (s < e && (*s == ' ' || *s == '\t')) {
                        s += 1;
                }

                if (block) {
                        if (p == raw) {
                                s += 2;
                                while (s < e && *s == '*') {
                                        s += 1;
                                }
                        } else if (s < e && *s == '*' && !(s + 1 < e && s[1] == '/')) {
                                s += 1;
                        }
                        if (e - s >= 2 && e[-2] == '*' && e[-1] == '/') {
                                e -= 2;
                        }
                } else if (e - s >= 2 && s[0] == '/' && s[1] == '/') {
                        s += 2;
                }

                if (s < e && *s == ' ') {
                        s += 1;
                }

                while (e > s && isspace((unsigned char)e[-1])) {
                        e -= 1;
                }

                spush(out, xstrndup(s, e - s));

                p = (*eol == '\0') ? eol : eol + 1;
        }

        while (out->count > 0 && out->items[0][0] == '\0') {
                free(out->items[0]);
                memmove(out->items, out->items + 1, --out->count * sizeof *out->items);
        }

        while (out->count > 0 && out->items[out->count - 1][0] == '\0') {
                free(out->items[--out->count]);
        }
}

static bool
sig_head(char const *s)
{
        if (!(isalpha((unsigned char)*s) || *s == '_')) {
                return false;
        }

        while (isalnum((unsigned char)*s) || strchr("_./?!-", *s) != NULL) {
                s += 1;
        }

        return (*s == '(' || *s == '[');
}

static char const *match_close(char const *p, char open, char close);

static bool
is_signature(char const *sig)
{
        char const *p = sig;

        while (*p != '(' && *p != '[') {
                p += 1;
        }

        if (*p == '[') {
                p = match_close(p, '[', ']');
                if (p == NULL || p[1] != '(') {
                        return false;
                }
                p += 1;
        }

        char const *close = match_close(p, '(', ')');
        if (close == NULL) {
                return false;
        }

        char const *rest = close + 1;
        while (*rest == ' ') {
                rest += 1;
        }

        if (strncmp(rest, "->", 2) == 0) {
                return true;
        }

        return (*rest == '\0') && (memchr(p, ':', close - p) != NULL);
}

static char *
normalize(char const *s)
{
        Buf b = {0};

        bputs(&b, "");

        for (char const *p = s; *p != '\0'; ++p) {
                if (isspace((unsigned char)*p)) {
                        while (isspace((unsigned char)p[1])) {
                                p += 1;
                        }
                        if (b.n > 0 && b.s[b.n - 1] != '(' && b.s[b.n - 1] != '[' && p[1] != ')' && p[1] != ']' && p[1] != '\0') {
                                bputc(&b, ' ');
                        }
                } else {
                        bputc(&b, *p);
                }
        }

        return b.s;
}

static void
parse_comment(Builtin *b, char const *raw)
{
        StrVec lines = {0};
        bool prose = false;

        comment_lines(raw, &lines);

        for (size_t i = 0; i < lines.count; ++i) {
                char const *line = lines.items[i];

                if (!sig_head(line)) {
                        prose |= (*line != '\0');
                        continue;
                }

                Buf sig = {0};
                size_t j = i;

                bputs(&sig, line);

                for (;;) {
                        while (bracket_depth(sig.s) > 0 && j + 1 < lines.count) {
                                bputc(&sig, ' ');
                                bputs(&sig, lines.items[++j]);
                        }

                        char *next = (j + 1 < lines.count) ? trim(lines.items[j + 1], lines.items[j + 1] + strlen(lines.items[j + 1])) : NULL;
                        bool arrow = (next != NULL) && (strncmp(next, "->", 2) == 0);
                        free(next);

                        if (!arrow) {
                                break;
                        }

                        bputc(&sig, ' ');
                        bputs(&sig, lines.items[++j]);
                }

                char *norm = normalize(sig.s);
                free(sig.s);

                if (bracket_depth(norm) == 0 && is_signature(norm)) {
                        spush(&b->lines, norm);
                        i = j;
                } else {
                        free(norm);
                        prose = true;
                }
        }

        if (prose) {
                Buf doc = {0};
                for (size_t i = 0; i < lines.count; ++i) {
                        if (i > 0) {
                                bputc(&doc, '\n');
                        }
                        bputs(&doc, lines.items[i]);
                }
                b->doc = doc.s;
        }

        for (size_t i = 0; i < lines.count; ++i) {
                free(lines.items[i]);
        }

        free(lines.items);
}

static char const *
invocation(char const *base, char const *p, char const *file, bool typed, char *cond, char const *comment)
{
        Builtin b = {0};

        b.typed = typed;
        b.file  = xstrdup(file);
        b.line  = line_of(base, p);
        b.cond  = cond;

        p = skip_space(p + 1);

        char const *id = p;
        while (isalnum((unsigned char)*p) || *p == '_') {
                p += 1;
        }

        b.cname = xstrndup(id, p - id);
        p = skip_space(p);

        if (*b.cname == '\0') {
                fail(&b, "expected a C function name in %s()", typed ? "TY_BUILTIN" : "TY_BUILTIN_RAW");
        }

        if (*p != ')') {
                fail(&b, "%s: signatures belong in the comment above the definition", b.cname);
                while (*p != '\0' && *p != ')') {
                        p += 1;
                }
        }

        if (comment != NULL) {
                parse_comment(&b, comment);
        }

        add_builtin(b);

        return p + (*p == ')');
}

static bool
adjacent(char const *s, char const *e)
{
        int newlines = 0;

        while (s < e) {
                if (*s == '\n') {
                        newlines += 1;
                        s += 1;
                } else if (isspace((unsigned char)*s)) {
                        s += 1;
                } else if (
                        (strncmp(s, "noreturn", 8) == 0)
                     && !(isalnum((unsigned char)s[8]) || s[8] == '_')
                ) {
                        s += 8;
                } else {
                        return false;
                }
        }

        return newlines <= 1;
}

static void
scan(char const *file)
{
        char *src = slurp(file);
        char const *p = src;
        Frame *stack = NULL;
        size_t n = 0;
        size_t cap = 0;
        bool bol = true;
        Buf comment = {0};
        char const *comment_end = NULL;
        bool comment_line = false;

        while (*p != '\0') {
                if (bol) {
                        char const *q = p;
                        while (*q == ' ' || *q == '\t') {
                                q += 1;
                        }
                        if (*q == '#') {
                                Buf d = {0};
                                while (*q != '\0' && *q != '\n') {
                                        if (q[0] == '\\' && q[1] == '\n') {
                                                q += 2;
                                                continue;
                                        }
                                        bputc(&d, *q++);
                                }
                                directive(d.s, &stack, &n, &cap);
                                free(d.s);
                                p = q;
                                continue;
                        }
                }

                if (*p == '\n') {
                        bol = true;
                        p += 1;
                        continue;
                }

                bol = false;

                if (p[0] == '/' && p[1] == '*') {
                        char const *end = strstr(p + 2, "*/");
                        char const *stop = (end == NULL) ? p + strlen(p) : end + 2;
                        comment.n = 0;
                        bputn(&comment, p, stop - p);
                        comment_end  = stop;
                        comment_line = false;
                        p = stop;
                } else if (p[0] == '/' && p[1] == '/') {
                        char const *start = p;
                        while (*p != '\0' && *p != '\n') {
                                p += 1;
                        }
                        if (comment_line && comment_end != NULL && adjacent(comment_end, start)) {
                                bputc(&comment, '\n');
                        } else {
                                comment.n = 0;
                        }
                        bputn(&comment, start, p - start);
                        comment_end  = p;
                        comment_line = true;
                } else if (*p == '"' || *p == '\'') {
                        char q = *p++;
                        while (*p != '\0' && *p != q) {
                                p += (*p == '\\' && p[1] != '\0') + 1;
                        }
                        p += (*p != '\0');
                } else if (isalpha((unsigned char)*p) || *p == '_') {
                        char const *id = p;
                        while (isalnum((unsigned char)*p) || *p == '_') {
                                p += 1;
                        }
                        size_t len = p - id;
                        bool raw   = (len == 14 && strncmp(id, "TY_BUILTIN_RAW", 14) == 0);
                        bool typed = (len == 10 && strncmp(id, "TY_BUILTIN", 10) == 0);
                        bool head  = (id == src) || !(isalnum((unsigned char)id[-1]) || id[-1] == '_');
                        if ((raw || typed) && head && *skip_space(p) == '(') {
                                bool attached = (comment_end != NULL) && adjacent(comment_end, id);
                                p = invocation(
                                        src,
                                        skip_space(p),
                                        file,
                                        typed,
                                        current_cond(stack, n),
                                        attached ? comment.s : NULL
                                );
                                comment_end = NULL;
                        }
                } else {
                        p += 1;
                }
        }

        free(comment.s);
        free(stack);
        free(src);
}

static char *
camel(char const *s, char const *e)
{
        Buf b = {0};

        bputs(&b, "");

        for (char const *c = s; c < e; ++c) {
                if (*c == '-' && c + 1 < e && isalnum((unsigned char)c[1])) {
                        c += 1;
                        bputc(&b, toupper((unsigned char)*c));
                } else {
                        bputc(&b, *c);
                }
        }

        return b.s;
}

static bool
head_split(char const *line, char **module, char **name, char const **rest)
{
        char const *p = line;

        while (*p != '\0' && *p != '(' && *p != '[' && !isspace((unsigned char)*p)) {
                p += 1;
        }

        if (*p != '(' && *p != '[') {
                return false;
        }

        char const *dot = NULL;
        for (char const *c = line; c < p; ++c) {
                if (*c == '.') {
                        dot = c;
                }
        }

        if (dot == NULL) {
                *module = NULL;
                *name   = camel(line, p);
        } else {
                *module = xstrndup(line, dot - line);
                *name   = camel(dot + 1, p);
        }

        *rest = p;

        return **name != '\0';
}

static bool
same(char const *a, char const *b)
{
        return (a == NULL || b == NULL) ? (a == b) : (strcmp(a, b) == 0);
}

static void
group(Builtin *b)
{
        if (b->lines.count == 0) {
                fail(b, "%s has no signature (put one in a comment directly above it)", b->cname);
                return;
        }

        for (size_t i = 0; i < b->lines.count; ++i) {
                char const *line = b->lines.items[i];
                char *module;
                char *name;
                char const *rest;

                if (!head_split(line, &module, &name, &rest)) {
                        fail(b, "%s: malformed signature: %s", b->cname, line);
                        continue;
                }

                Entry *e = NULL;
                for (size_t j = 0; j < b->nentries; ++j) {
                        if (same(b->entries[j].module, module) && strcmp(b->entries[j].name, name) == 0) {
                                e = &b->entries[j];
                        }
                }

                if (e == NULL) {
                        b->entries = xrealloc(b->entries, (b->nentries + 1) * sizeof *b->entries);
                        e = &b->entries[b->nentries++];
                        memset(e, 0, sizeof *e);
                        e->module = module;
                        e->name   = name;
                }

                if (e->sig.n > 0) {
                        bputc(&e->sig, '\n');
                }

                bputs(&e->sig, rest);
        }
}

static void
c_quote(Buf *out, char const *s)
{
        bputc(out, '"');

        for (; *s != '\0'; ++s) {
                switch (*s) {
                case '"':  bputs(out, "\\\""); break;
                case '\\': bputs(out, "\\\\"); break;
                case '\n': bputs(out, "\\n\" \""); break;
                case '\t': bputs(out, "\\t"); break;
                default:   bputc(out, *s); break;
                }
        }

        bputc(out, '"');
}

static char const *
match_close(char const *p, char open, char close)
{
        int depth = 0;

        for (; *p != '\0'; ++p) {
                if (*p == '\'' || *p == '"') {
                        char q = *p++;
                        while (*p != '\0' && *p != q) {
                                p += (*p == '\\' && p[1] != '\0') + 1;
                        }
                        if (*p == '\0') {
                                return NULL;
                        }
                        continue;
                }
                if (*p == open) {
                        depth += 1;
                } else if (*p == close) {
                        depth -= 1;
                        if (depth == 0) {
                                return p;
                        }
                }
        }

        return NULL;
}

static void
split_params(char const *s, char const *e, StrVec *out)
{
        int depth = 0;
        char const *start = s;

        for (char const *p = s; p < e; ++p) {
                switch (*p) {
                case '(': case '[': case '{':
                        depth += 1;
                        break;

                case ')': case ']': case '}':
                        depth -= 1;
                        break;

                case '\'': case '"':
                {
                        char q = *p++;
                        while (p < e && *p != q) {
                                p += (*p == '\\') + 1;
                        }
                        break;
                }

                case ',':
                        if (depth == 0) {
                                char *t = trim(start, p);
                                if (*t != '\0') {
                                        spush(out, t);
                                }
                                start = p + 1;
                        }
                        break;
                }
        }

        char *t = trim(start, e);
        if (*t != '\0') {
                spush(out, t);
        }
}

static char const *
find_default(char const *s)
{
        int depth = 0;

        for (char const *p = s; *p != '\0'; ++p) {
                switch (*p) {
                case '(': case '[': case '{': depth += 1; break;
                case ')': case ']': case '}': depth -= 1; break;
                case '=':
                        if (
                                depth == 0
                             && p > s
                             && p[-1] == ' '
                             && p[1] == ' '
                        ) {
                                return p;
                        }
                }
        }

        return NULL;
}

static char *
param_cname(char const *name)
{
        Buf b = {0};

        bputs(&b, "");

        for (char const *c = name; *c != '\0'; ++c) {
                if (*c == '-') {
                        bputc(&b, '_');
                } else if (isalnum((unsigned char)*c) || *c == '_') {
                        bputc(&b, *c);
                }
        }

        for (size_t i = 0; i < sizeof CKeywords / sizeof *CKeywords; ++i) {
                if (strcmp(b.s, CKeywords[i]) == 0) {
                        bputc(&b, '_');
                        break;
                }
        }

        return b.s;
}

static bool
int_literal(char const *s, long long *out)
{
        char digits[128];
        size_t n = 0;
        bool neg = (*s == '-');
        int base = 10;

        s += neg;

        if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
                base = 16;
                s += 2;
        } else if (s[0] == '0' && (s[1] == 'o' || s[1] == 'O')) {
                base = 8;
                s += 2;
        } else if (s[0] == '0' && (s[1] == 'b' || s[1] == 'B')) {
                base = 2;
                s += 2;
        }

        for (; *s != '\0'; ++s) {
                if (*s == '_') {
                        continue;
                }
                if (n + 1 >= sizeof digits) {
                        return false;
                }
                digits[n++] = *s;
        }

        digits[n] = '\0';

        if (n == 0) {
                return false;
        }

        char *end;
        errno = 0;
        long long v = strtoll(digits, &end, base);

        if (*end != '\0' || errno != 0) {
                return false;
        }

        *out = neg ? -v : v;

        return true;
}

static bool
float_literal(char const *s)
{
        char *end;

        if (*s == '\0') {
                return false;
        }

        (void)strtod(s, &end);

        return *end == '\0';
}

static char *
string_literal(char const *s)
{
        size_t n = strlen(s);
        Buf b = {0};

        if (n < 2 || (s[0] != '\'' && s[0] != '"') || s[n - 1] != s[0]) {
                return NULL;
        }

        bputc(&b, '"');

        for (size_t i = 1; i + 1 < n; ++i) {
                if (s[i] == '\\' && i + 2 < n) {
                        bputc(&b, s[i]);
                        bputc(&b, s[++i]);
                } else if (s[i] == '"') {
                        bputs(&b, "\\\"");
                } else {
                        bputc(&b, s[i]);
                }
        }

        bputc(&b, '"');

        return b.s;
}

static char *
c_default(Builtin const *b, Param const *p, char const *lit)
{
        long long k;
        Buf out = {0};
        char *str;

        bputs(&out, "");

        switch (p->kind) {
        case P_INT:
                if (int_literal(lit, &k)) {
                        bprintf(&out, "%lldLL", k);
                        return out.s;
                }
                break;

        case P_FLOAT:
                if (int_literal(lit, &k)) {
                        bprintf(&out, "%lld.0", k);
                        return out.s;
                }
                if (float_literal(lit)) {
                        bprintf(&out, "%s", lit);
                        return out.s;
                }
                break;

        case P_BOOL:
                if (strcmp(lit, "true") == 0 || strcmp(lit, "false") == 0) {
                        bputs(&out, lit);
                        return out.s;
                }
                break;

        case P_PATH:
        case P_BLOB:
                if (strcmp(lit, "nil") == 0) {
                        bputs(&out, "NULL");
                        return out.s;
                }
                if (p->kind == P_PATH && (str = string_literal(lit)) != NULL) {
                        return str;
                }
                break;

        case P_STRING:
        case P_ANY:
                if (strcmp(lit, "nil") == 0) {
                        bputs(&out, "NIL");
                        return out.s;
                }
                if (strcmp(lit, "true") == 0 || strcmp(lit, "false") == 0) {
                        bprintf(&out, "BOOLEAN(%s)", lit);
                        return out.s;
                }
                if (int_literal(lit, &k)) {
                        bprintf(&out, "INTEGER(%lldLL)", k);
                        return out.s;
                }
                if (float_literal(lit)) {
                        bprintf(&out, "REAL(%s)", lit);
                        return out.s;
                }
                if ((str = string_literal(lit)) != NULL) {
                        bprintf(&out, "vSsz(%s)", str);
                        free(str);
                        return out.s;
                }
                break;
        }

        fail(b, "%s: unsupported default for `%s`: %s", b->cname, p->name, lit);

        return out.s;
}

static int
param_kind(char const *type, bool *nullable)
{
        char *t = xstrdup(type);
        size_t n = strlen(t);
        int kind;

        *nullable = false;

        if (t[0] == '?') {
                *nullable = true;
                memmove(t, t + 1, n);
        } else if (n > 6 && strcmp(t + n - 6, " | nil") == 0) {
                *nullable = true;
                t[n - 6] = '\0';
        }

        if (strcmp(t, "Int") == 0) {
                kind = P_INT;
        } else if (
                (strcmp(t, "Float") == 0)
             || (strcmp(t, "Int | Float") == 0)
             || (strcmp(t, "Float | Int") == 0)
        ) {
                kind = P_FLOAT;
        } else if (strcmp(t, "Bool") == 0) {
                kind = P_BOOL;
        } else if (strcmp(t, "String") == 0) {
                kind = P_STRING;
        } else if (strcmp(t, "Blob") == 0) {
                kind = P_BLOB;
        } else if (strcmp(t, "PathLike") == 0) {
                kind = P_PATH;
        } else {
                kind = P_ANY;
        }

        if (
                *nullable
             && (kind == P_INT || kind == P_FLOAT || kind == P_BOOL || kind == P_STRING)
        ) {
                kind = P_ANY;
        }

        free(t);

        return kind;
}

static Param *
typed_params(Builtin *b, size_t *count)
{
        char const *rest;
        char *module;
        char *name;

        if (b->entries == NULL) {
                return NULL;
        }

        size_t sigs = b->lines.count;
        char const *line = (sigs > 0) ? b->lines.items[0] : NULL;

        if (sigs != 1) {
                fail(b, "%s: TY_BUILTIN needs exactly one signature (use TY_BUILTIN_RAW for overloads)", b->cname);
                return NULL;
        }

        head_split(line, &module, &name, &rest);

        if (*rest == '[') {
                rest = match_close(rest, '[', ']');
                if (rest == NULL) {
                        fail(b, "%s: malformed generics", b->cname);
                        return NULL;
                }
                rest += 1;
        }

        char const *close = (*rest == '(') ? match_close(rest, '(', ')') : NULL;

        if (close == NULL) {
                fail(b, "%s: malformed parameter list", b->cname);
                return NULL;
        }

        StrVec raw = {0};
        split_params(rest + 1, close, &raw);

        Param *ps = xrealloc(NULL, (raw.count + 1) * sizeof *ps);
        size_t paths = 0;

        for (size_t i = 0; i < raw.count; ++i) {
                char const *s = raw.items[i];
                Param *p = &ps[i];

                memset(p, 0, sizeof *p);

                if (*s == '*' || *s == '%') {
                        fail(b, "%s: TY_BUILTIN doesn't support `%s` (use TY_BUILTIN_RAW)", b->cname, s);
                        continue;
                }

                char const *eq = find_default(s);
                char const *end = (eq == NULL) ? s + strlen(s) : eq;
                char const *colon = memchr(s, ':', end - s);

                p->name = trim(s, (colon == NULL) ? end : colon);
                p->cname = param_cname(p->name);

                char *type = (colon == NULL) ? xstrdup("Any") : trim(colon + 1, end);
                p->kind = param_kind(type, &p->nullable);
                free(type);

                if (p->kind == P_PATH) {
                        paths += 1;
                }

                if (eq != NULL) {
                        char *lit = trim(eq + 1, eq + strlen(eq));
                        p->dflt = c_default(b, p, lit);
                        free(lit);
                } else if (p->nullable) {
                        p->dflt = xstrdup(
                                (p->kind == P_PATH || p->kind == P_BLOB) ? "NULL" : "NIL"
                        );
                } else {
                        p->required = true;
                }
        }

        if (paths > 3) {
                fail(b, "%s: TY_BUILTIN supports at most 3 PathLike parameters", b->cname);
        }

        *count = raw.count;

        return ps;
}

static char const *
ctype_of(int kind)
{
        switch (kind) {
        case P_INT:   return "i64";
        case P_FLOAT: return "double";
        case P_BOOL:  return "bool";
        case P_BLOB:  return "Blob *";
        case P_PATH:  return "char const *";
        default:      return "Value";
        }
}

static void
line_out(Buf *out, Buf *line)
{
        size_t width = 80;

        bputs(out, line->s);

        for (size_t i = line->n; i < width; ++i) {
                bputc(out, ' ');
        }

        bputs(out, "\\\n");

        line->n = 0;
        line->s[0] = '\0';
}

static void
emit_typed(Buf *out, Builtin *b)
{
        size_t n = 0;
        Param *ps = typed_params(b, &n);
        Buf l = {0};
        Buf params = {0};
        Buf args = {0};
        size_t paths = 0;
        Entry const *e = &b->entries[0];

        if (ps == NULL) {
                return;
        }

        bputs(&l, "");
        bputs(&params, "");
        bputs(&args, "");

        for (size_t i = 0; i < n; ++i) {
                bprintf(&params, ", %s%s%s", ctype_of(ps[i].kind), (ps[i].kind == P_BLOB || ps[i].kind == P_PATH) ? "" : " ", ps[i].cname);
                bprintf(&args, ", %s", ps[i].cname);
        }

        bprintf(&l, "#define TY_BUILTIN__%s", b->cname);
        line_out(out, &l);

        bprintf(&l, "inline static Value builtin_%s__(Ty *ty, int argc, Value *kwargs, char const *_name__%s);", b->cname, params.s);
        line_out(out, &l);
        bputs(&l, "Value");
        line_out(out, &l);
        bprintf(&l, "builtin_%s(Ty *ty, int argc, Value *kwargs)", b->cname);
        line_out(out, &l);
        bputs(&l, "{");
        line_out(out, &l);
        bprintf(&l, "        char const *_name__ = \"%s%s%s()\";", e->module ? e->module : "", e->module ? "." : "", e->name);
        line_out(out, &l);
        bprintf(&l, "        TyBuiltinArity(ty, _name__, argc, %zu);", n);
        line_out(out, &l);

        for (size_t i = 0; i < n; ++i) {
                bprintf(&l, "        Value _a%zu = TyBuiltinArg(ty, argc, kwargs, %zu, \"%s\");", i, i, ps[i].name);
                line_out(out, &l);
        }

        for (size_t i = 0; i < n; ++i) {
                if (ps[i].kind != P_PATH) {
                        continue;
                }
                if (ps[i].required) {
                        bprintf(&l, "        _a%zu = TyPathValue(ty, _name__, \"%s\", TyBuiltinNeed(ty, _name__, \"%s\", _a%zu));", i, ps[i].name, ps[i].name, i);
                } else {
                        bprintf(&l, "        _a%zu = TyBuiltinAbsent(_a%zu) ? NIL : TyPathValue(ty, _name__, \"%s\", _a%zu);", i, i, ps[i].name, i);
                }
                line_out(out, &l);
                bprintf(&l, "        gP(&_a%zu);", i);
                line_out(out, &l);
                paths += 1;
        }

        size_t buf = 0;

        for (size_t i = 0; i < n; ++i) {
                Param const *p = &ps[i];
                char const *conv;

                switch (p->kind) {
                case P_INT:    conv = "TyBuiltinInt";    break;
                case P_FLOAT:  conv = "TyBuiltinFloat";  break;
                case P_BOOL:   conv = "TyBuiltinBool";   break;
                case P_STRING: conv = "TyBuiltinString"; break;
                case P_BLOB:   conv = "TyBuiltinBlob";   break;
                default:       conv = NULL;              break;
                }

                if (p->kind == P_PATH) {
                        if (p->required) {
                                bprintf(&l, "        char const *%s = TY_PATH_C_STR_i(%zu, _a%zu);", p->cname, buf, i);
                        } else {
                                bprintf(&l, "        char const *%s = IsNil(_a%zu) ? %s : TY_PATH_C_STR_i(%zu, _a%zu);", p->cname, i, p->dflt, buf, i);
                        }
                        buf += 1;
                } else if (conv == NULL) {
                        if (p->required) {
                                bprintf(&l, "        Value %s = TyBuiltinNeed(ty, _name__, \"%s\", _a%zu);", p->cname, p->name, i);
                        } else {
                                bprintf(&l, "        Value %s = TyBuiltinAbsent(_a%zu) ? %s : _a%zu;", p->cname, i, p->dflt, i);
                        }
                } else if (p->required) {
                        bprintf(&l, "        %s%s%s = %s(ty, _name__, \"%s\", TyBuiltinNeed(ty, _name__, \"%s\", _a%zu));", ctype_of(p->kind), (p->kind == P_BLOB) ? "" : " ", p->cname, conv, p->name, p->name, i);
                } else if (p->nullable) {
                        bprintf(&l, "        %s%s%s = (TyBuiltinAbsent(_a%zu) || IsNil(_a%zu)) ? %s : %s(ty, _name__, \"%s\", _a%zu);", ctype_of(p->kind), (p->kind == P_BLOB) ? "" : " ", p->cname, i, i, p->dflt, conv, p->name, i);
                } else {
                        bprintf(&l, "        %s%s%s = TyBuiltinAbsent(_a%zu) ? %s : %s(ty, _name__, \"%s\", _a%zu);", ctype_of(p->kind), (p->kind == P_BLOB) ? "" : " ", p->cname, i, p->dflt, conv, p->name, i);
                }
                line_out(out, &l);
        }

        for (size_t i = 0; i < paths; ++i) {
                bputs(&l, "        gX();");
                line_out(out, &l);
        }

        bprintf(&l, "        return builtin_%s__(ty, argc, kwargs, _name__%s);", b->cname, args.s);
        line_out(out, &l);
        bputs(&l, "}");
        line_out(out, &l);
        bputs(&l, "inline static Value");
        line_out(out, &l);
        bprintf(out, "builtin_%s__(Ty *ty, int argc, Value *kwargs, char const *_name__%s)\n\n", b->cname, params.s);

        free(l.s);
        free(params.s);
        free(args.s);
}

static void
write_if_changed(char const *path, Buf const *b)
{
        FILE *f = fopen(path, "rb");

        if (f != NULL) {
                fclose(f);
                char *old = slurp(path);
                bool same = (strlen(old) == b->n) && (memcmp(old, b->s, b->n) == 0);
                free(old);
                if (same) {
                        return;
                }
        }

        f = fopen(path, "wb");

        if (f == NULL) {
                fprintf(stderr, "tybi: %s: %s\n", path, strerror(errno));
                exit(1);
        }

        fwrite(b->s, 1, b->n, f);
        fclose(f);
}

static void
emit_cond_open(Buf *out, char const *cond)
{
        if (*cond != '\0') {
                bprintf(out, "#if %s\n", cond);
        }
}

static void
emit_cond_close(Buf *out, char const *cond)
{
        if (*cond != '\0') {
                bputs(out, "#endif\n");
        }
}

int
main(int argc, char **argv)
{
        Buf decls = {0};
        Buf table = {0};
        char path[4096];

        if (argc < 3) {
                fprintf(stderr, "usage: tybi <outdir> <source.c>...\n");
                return 1;
        }

        for (int i = 2; i < argc; ++i) {
                scan(argv[i]);
        }

        for (size_t i = 0; i < NBuiltins; ++i) {
                group(&Builtins[i]);
        }

        for (size_t i = 0; i < NBuiltins; ++i) {
                for (size_t j = 0; j < i; ++j) {
                        if (
                                strcmp(Builtins[i].cname, Builtins[j].cname) == 0
                             && strcmp(Builtins[i].cond, Builtins[j].cond) == 0
                        ) {
                                fail(&Builtins[i], "%s is already defined at %s:%d", Builtins[i].cname, Builtins[j].file, Builtins[j].line);
                        }
                }
        }

        bputs(&decls, "#ifndef TY_BUILTIN_DECLS_H_INCLUDED\n#define TY_BUILTIN_DECLS_H_INCLUDED\n\n");

        for (size_t i = 0; i < NBuiltins; ++i) {
                bool seen = false;
                for (size_t j = 0; j < i; ++j) {
                        seen |= (strcmp(Builtins[i].cname, Builtins[j].cname) == 0);
                }
                if (!seen) {
                        bprintf(&decls, "Value builtin_%s(Ty *ty, int argc, Value *kwargs);\n", Builtins[i].cname);
                }
        }

        bputs(&decls, "\n");

        for (size_t i = 0; i < NBuiltins; ++i) {
                if (Builtins[i].typed) {
                        emit_typed(&decls, &Builtins[i]);
                }
        }

        bputs(&decls, "#endif\n");

        for (size_t i = 0; i < NBuiltins; ++i) {
                Builtin const *b = &Builtins[i];
                emit_cond_open(&table, b->cond);
                for (size_t j = 0; j < b->nentries; ++j) {
                        Entry const *e = &b->entries[j];
                        bputs(&table, "  { .module = ");
                        if (e->module == NULL) {
                                bputs(&table, "NULL");
                        } else {
                                c_quote(&table, e->module);
                        }
                        bputs(&table, ", .name = ");
                        c_quote(&table, e->name);
                        bprintf(&table, ", .value = TY_GENERATED_BUILTIN(builtin_%s), .sig = ", b->cname);
                        c_quote(&table, e->sig.s);
                        bputs(&table, ", .doc = ");
                        if (b->doc == NULL) {
                                bputs(&table, "NULL");
                        } else {
                                c_quote(&table, b->doc);
                        }
                        bputs(&table, " },\n");
                }
                emit_cond_close(&table, b->cond);
        }

        if (Errors > 0) {
                return 1;
        }

        snprintf(path, sizeof path, "%s/builtin_decls.h", argv[1]);
        write_if_changed(path, &decls);

        snprintf(path, sizeof path, "%s/builtin_table.h", argv[1]);
        write_if_changed(path, &table);

        return 0;
}
