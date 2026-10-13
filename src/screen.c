#include <string.h>

#include <utf8proc.h>

#include "ty.h"
#include "dict.h"
#include "value.h"
#include "gc.h"
#include "vm.h"
#include "xd.h"
#include "screen.h"

enum {
        GLYPH_INLINE = 12,
        GLYPH_LONG   = 0xff,
        GLYPH_MAX    = 64,
        TAB_MAX      = 4096,
        OP_SLOTS     = 256,
        OP_KEY       = 30,
        TR_SLOTS     = 128,
        TR_MAX       = 94
};

enum {
        OP_FG = 1 << 0,
        OP_BG = 1 << 1,
        OP_UC = 1 << 2,
        OP_UL = 1 << 3
};

typedef struct {
        u32 fg;
        u32 bg;
        u32 uc;
        u16 aset;
        u16 aclr;
        u8  ul;
        u8  mask;
} SgrOp;

typedef struct {
        u8    n;
        u8    key[OP_KEY];
        bool  used;
        SgrOp op;
} OpSlot;

typedef struct {
        Pen  a;
        Pen  b;
        bool used;
        u8   n;
        char sgr[TR_MAX];
} TrSlot;

typedef struct {
        u8  g[GLYPH_INLINE];
        u8  n;
        u8  w;
        u16 ln;
        Pen s;
} Cell;

_Static_assert(sizeof (Cell) == 32, "Cell must have no padding");

typedef struct {
        char *p;
        u32   n;
} ScrStr;

typedef vec(ScrStr) ScrTab;

typedef struct {
        byte_vector src;
        bool        drawn;
} ScrRow;

typedef struct {
        int         cols;
        int         rows;
        Cell       *cur;
        Cell       *prev;
        u8         *dirty;
        ScrRow     *line;
        bool        valid;
        u32         dbg;
        int         crow;
        ScrTab      glyphs;
        ScrTab      links;
        byte_vector buf;
        OpSlot     *ops;
        TrSlot     *trs;
} Scr;

static Cell const VoidCell = {
        .g  = { ' ' },
        .n  = 1,
        .w  = 1,
        .ln = 0,
        .s  = { .fl = PEN_VOID }
};

static Cell const LostCell = {
        .g  = { 0 },
        .n  = 0xfe,
        .w  = 0xfe,
        .ln = 0xffff,
        .s  = { .fl = 0xff }
};

inline static bool
iscont(Cell const *c)
{
        return c->n == 0;
}

inline static bool
isvoid(Cell const *c)
{
        return memcmp(c, &VoidCell, sizeof *c) == 0;
}

static u32
clampu8(i32 v)
{
        if (v < 0) {
                return 0;
        }

        return (v > 255) ? 255 : (u32)v;
}

void
pen_sgr(Pen *p, u8 const *s, isize n)
{
        i32  v[32];
        bool sub[32];
        int  nv  = 0;
        i32  cur = -1;
        bool cs  = false;

        for (isize i = 0; i <= n; ++i) {
                if (i == n || s[i] == ';' || s[i] == ':') {
                        if (nv < 32) {
                                v[nv]   = cur;
                                sub[nv] = cs;
                                nv += 1;
                        }
                        cur = -1;
                        cs  = (i < n && s[i] == ':');
                } else if (xisdigit(s[i])) {
                        cur = (cur < 0) ? 0 : cur;
                        cur = (cur > 99999) ? cur : cur * 10 + (s[i] - '0');
                }
        }

        for (int i = 0; i < nv; ++i) {
                int k = (v[i] < 0) ? 0 : v[i];
                int j = i + 1;

                while (j < nv && sub[j]) {
                        j += 1;
                }

                int ns = j - i - 1;
                u32 *dst = NULL;
                u32 c = 0;
                bool ok = false;

                switch (k) {
                case 0:
                        p->fg = 0;
                        p->bg = 0;
                        p->uc = 0;
                        p->at = 0;
                        p->ul = 0;
                        break;

                case 1:  p->at |= PEN_BOLD;                     break;
                case 2:  p->at |= PEN_DIM;                      break;
                case 3:  p->at |= PEN_ITALIC;                   break;
                case 5:  p->at |= PEN_BLINK;                    break;
                case 6:  p->at |= PEN_BLINK;                    break;
                case 7:  p->at |= PEN_REVERSE;                  break;
                case 8:  p->at |= PEN_HIDDEN;                   break;
                case 9:  p->at |= PEN_STRIKE;                   break;
                case 21: p->ul  = 2;                            break;
                case 22: p->at &= ~(PEN_BOLD | PEN_DIM);        break;
                case 23: p->at &= ~PEN_ITALIC;                  break;
                case 24: p->ul  = 0;                            break;
                case 25: p->at &= ~PEN_BLINK;                   break;
                case 27: p->at &= ~PEN_REVERSE;                 break;
                case 28: p->at &= ~PEN_HIDDEN;                  break;
                case 29: p->at &= ~PEN_STRIKE;                  break;
                case 39: p->fg  = 0;                            break;
                case 49: p->bg  = 0;                            break;
                case 53: p->at |= PEN_OVER;                     break;
                case 55: p->at &= ~PEN_OVER;                    break;
                case 59: p->uc  = 0;                            break;

                case 4:
                        p->ul = (ns > 0) ? (u8)clampu8(max(v[i + 1], 0)) : 1;
                        break;

                case 38:
                case 48:
                case 58:
                        if (k == 38) {
                                dst = &p->fg;
                        } else if (k == 48) {
                                dst = &p->bg;
                        } else {
                                dst = &p->uc;
                        }
                        if (ns > 0) {
                                if (v[i + 1] == 5 && ns >= 2) {
                                        c  = PEN_C256 | clampu8(v[i + 2]);
                                        ok = true;
                                } else if (v[i + 1] == 2 && ns >= 5) {
                                        c  = PEN_RGB
                                           | (clampu8(v[i + 3]) << 16)
                                           | (clampu8(v[i + 4]) << 8)
                                           | clampu8(v[i + 5]);
                                        ok = true;
                                } else if (v[i + 1] == 2 && ns >= 4) {
                                        c  = PEN_RGB
                                           | (clampu8(v[i + 2]) << 16)
                                           | (clampu8(v[i + 3]) << 8)
                                           | clampu8(v[i + 4]);
                                        ok = true;
                                }
                        } else if (i + 2 < nv && v[i + 1] == 5) {
                                c  = PEN_C256 | clampu8(v[i + 2]);
                                ok = true;
                                j  = i + 3;
                        } else if (i + 4 < nv && v[i + 1] == 2) {
                                c  = PEN_RGB
                                   | (clampu8(v[i + 2]) << 16)
                                   | (clampu8(v[i + 3]) << 8)
                                   | clampu8(v[i + 4]);
                                ok = true;
                                j  = i + 5;
                        }
                        if (ok) {
                                *dst = c;
                        }
                        break;

                default:
                        if (k >= 30 && k <= 37) {
                                p->fg = PEN_C16 | (k - 30);
                        } else if (k >= 90 && k <= 97) {
                                p->fg = PEN_C16 | (k - 90 + 8);
                        } else if (k >= 40 && k <= 47) {
                                p->bg = PEN_C16 | (k - 40);
                        } else if (k >= 100 && k <= 107) {
                                p->bg = PEN_C16 | (k - 100 + 8);
                        }
                        break;
                }

                i = j - 1;
        }
}

static char *
putu(char *o, u32 x)
{
        char t[10];
        int n = 0;

        do {
                t[n++] = '0' + x % 10;
                x /= 10;
        } while (x != 0);

        while (n > 0) {
                *o++ = t[--n];
        }

        return o;
}

inline static char *
psep(char *o, char const *start)
{
        if (o != start) {
                *o++ = ';';
        }
        return o;
}

static char *
pcode(char *o, char const *start, u32 code)
{
        return putu(psep(o, start), code);
}

static char *
pcolor(char *o, char const *start, u32 c, u32 base)
{
        u32 idx = c & 0xffffff;

        o = psep(o, start);

        switch (c & 0xff000000) {
        case PEN_C16:
                if (base == 50) {
                        o = putu(o, 58);
                        memcpy(o, ";5;", 3);
                        o = putu(o + 3, idx);
                } else {
                        o = putu(o, ((idx < 8) ? base : base + 60) + (idx & 7));
                }
                break;

        case PEN_C256:
                o = putu(o, base + 8);
                memcpy(o, ";5;", 3);
                o = putu(o + 3, idx);
                break;

        case PEN_RGB:
                o = putu(o, base + 8);
                memcpy(o, ";2;", 3);
                o = putu(o + 3, (idx >> 16) & 0xff);
                *o++ = ';';
                o = putu(o, (idx >> 8) & 0xff);
                *o++ = ';';
                o = putu(o, idx & 0xff);
                break;

        default:
                o = putu(o, base + 9);
                break;
        }

        return o;
}

static char *
pul(char *o, char const *start, u8 ul)
{
        o = psep(o, start);

        switch (ul) {
        case 0:
                return putu(o, 24);

        case 1:
                return putu(o, 4);

        default:
                memcpy(o, "4:", 2);
                return putu(o + 2, ul);
        }
}

static u32 const AttrOn[]  = { 1, 2, 3, 5, 7, 8, 9, 53 };
static u32 const AttrOff[] = { 22, 22, 23, 25, 27, 28, 29, 55 };

static char *
pfull(char *o, Pen const *b)
{
        char *start = o;

        *o++ = '0';

        for (int i = 0; i < countof(AttrOn); ++i) {
                if (b->at & (1 << i)) {
                        o = pcode(o, start, AttrOn[i]);
                }
        }

        if (b->ul != 0) {
                o = pul(o, start, b->ul);
        }
        if (b->fg != 0) {
                o = pcolor(o, start, b->fg, 30);
        }
        if (b->bg != 0) {
                o = pcolor(o, start, b->bg, 40);
        }
        if (b->uc != 0) {
                o = pcolor(o, start, b->uc, 50);
        }

        return o;
}

static char *
pincr(char *o, Pen const *a, Pen const *b)
{
        char *start = o;
        u16 lost = a->at & ~b->at;
        u16 gain = b->at & ~a->at;

        if (lost & (PEN_BOLD | PEN_DIM)) {
                o = pcode(o, start, 22);
                gain |= b->at & (PEN_BOLD | PEN_DIM);
        }

        for (int i = 0; i < countof(AttrOn); ++i) {
                u16 bit = 1 << i;
                if (gain & bit) {
                        o = pcode(o, start, AttrOn[i]);
                } else if ((lost & bit) && i >= 2) {
                        o = pcode(o, start, AttrOff[i]);
                }
        }

        if (a->ul != b->ul) {
                o = pul(o, start, b->ul);
        }
        if (a->fg != b->fg) {
                o = pcolor(o, start, b->fg, 30);
        }
        if (a->bg != b->bg) {
                o = pcolor(o, start, b->bg, 40);
        }
        if (a->uc != b->uc) {
                o = pcolor(o, start, b->uc, 50);
        }

        return o;
}

int
pen_diff(char *o, Pen const *a, Pen const *b, bool known)
{
        char full[PEN_SGR_MAX];
        char incr[PEN_SGR_MAX];
        Pen pa = *a;
        Pen pb = *b;

        pa.fl = 0;
        pb.fl = 0;

        if (known && pen_eq(&pa, &pb)) {
                return 0;
        }

        int nf = (int)(pfull(full, &pb) - full);
        int ni = known ? (int)(pincr(incr, &pa, &pb) - incr) : PEN_SGR_MAX;
        char const *src = (ni < nf) ? incr : full;
        int n = min(ni, nf);

        if (!known && pen_plain(&pb)) {
                n = 0;
        }

        o[0] = '\x1b';
        o[1] = '[';
        memcpy(o + 2, src, n);
        o[n + 2] = 'm';

        return n + 3;
}

bool
pen_osc8(u8 const *s, isize n, isize *off, isize *len)
{
        if (n < 6 || s[1] != ']' || s[2] != '8' || s[3] != ';') {
                return false;
        }

        isize end = n;

        if (s[n - 1] == 0x07) {
                end = n - 1;
        } else if (s[n - 1] == '\\' && s[n - 2] == 0x1b) {
                end = n - 2;
        }

        *off = 4;
        *len = max(end - 4, 0);

        return true;
}

inline static u32
fnv(u8 const *p, isize n)
{
        u32 h = 2166136261u;

        for (isize i = 0; i < n; ++i) {
                h = (h ^ p[i]) * 16777619u;
        }

        return h;
}

static SgrOp
op_compile(u8 const *s, isize n)
{
        Pen lo = { .fg = 0xff000001, .bg = 0xff000001, .uc = 0xff000001, .at = 0,      .ul = 0xfe };
        Pen hi = { .fg = 0xff000002, .bg = 0xff000002, .uc = 0xff000002, .at = 0xffff, .ul = 0xfd };
        SgrOp op = {0};

        pen_sgr(&lo, s, n);
        pen_sgr(&hi, s, n);

        op.aset = lo.at;
        op.aclr = ~hi.at & 0xffff;

        if (lo.fg == hi.fg) {
                op.fg = lo.fg;
                op.mask |= OP_FG;
        }
        if (lo.bg == hi.bg) {
                op.bg = lo.bg;
                op.mask |= OP_BG;
        }
        if (lo.uc == hi.uc) {
                op.uc = lo.uc;
                op.mask |= OP_UC;
        }
        if (lo.ul == hi.ul) {
                op.ul = lo.ul;
                op.mask |= OP_UL;
        }

        return op;
}

inline static void
op_apply(Pen *p, SgrOp const *op)
{
        p->at = (p->at & ~op->aclr) | op->aset;

        if (op->mask & OP_FG) {
                p->fg = op->fg;
        }
        if (op->mask & OP_BG) {
                p->bg = op->bg;
        }
        if (op->mask & OP_UC) {
                p->uc = op->uc;
        }
        if (op->mask & OP_UL) {
                p->ul = op->ul;
        }
}

static void
sgr_cached(OpSlot *ops, Pen *pen, u8 const *s, isize n)
{
        if (n > OP_KEY) {
                pen_sgr(pen, s, n);
                return;
        }

        OpSlot *e = &ops[fnv(s, n) % OP_SLOTS];

        if (!e->used || e->n != n || memcmp(e->key, s, n) != 0) {
                e->used = true;
                e->n    = (u8)n;
                e->op   = op_compile(s, n);
                memcpy(e->key, s, n);
        }

        op_apply(pen, &e->op);
}

static u32
tab_get(ScrTab *t, u8 const *p, isize n)
{
        for (isize i = 0; i < vN(*t); ++i) {
                ScrStr const *e = v_(*t, i);
                if (e->n == n && memcmp(e->p, p, n) == 0) {
                        return (u32)(i + 1);
                }
        }

        if (vN(*t) >= TAB_MAX) {
                return 0;
        }

        char *c = xmA(max(n, 1));
        memcpy(c, p, n);
        xvP(*t, ((ScrStr) { c, (u32)n }));

        return (u32)vN(*t);
}

static void
tab_clear(ScrTab *t)
{
        for (isize i = 0; i < vN(*t); ++i) {
                xmF(v__(*t, i).p);
        }
        v0(*t);
}

static isize
glyph_bytes(Scr const *s, Cell const *c, u8 const **out)
{
        if (c->n != GLYPH_LONG) {
                *out = c->g;
                return c->n;
        }

        u32 id;
        memcpy(&id, c->g, sizeof id);
        ScrStr const *e = v_(s->glyphs, id - 1);
        *out = (u8 const *)e->p;

        return e->n;
}

static void
set_glyph(Scr *s, Cell *c, u8 const *g, isize n)
{
        memset(c->g, 0, sizeof c->g);

        if (n <= GLYPH_INLINE) {
                memcpy(c->g, g, n);
                c->n = (u8)n;
                return;
        }

        u32 id = tab_get(&s->glyphs, g, n);

        if (id == 0) {
                isize keep = 0;
                while (keep < n && keep + u8_rune_sz(g + keep) <= GLYPH_INLINE) {
                        keep += u8_rune_sz(g + keep);
                }
                memcpy(c->g, g, keep);
                c->n = (u8)keep;
                return;
        }

        memcpy(c->g, &id, sizeof id);
        c->n = GLYPH_LONG;
}

static void
attach(Scr *s, Cell *c, u8 const *p, isize m)
{
        u8 buf[GLYPH_MAX];
        u8 const *g;
        isize n = glyph_bytes(s, c, &g);

        if (n + m > GLYPH_MAX) {
                return;
        }

        memcpy(buf, g, n);
        memcpy(buf + n, p, m);
        set_glyph(s, c, buf, n + m);
}

static void
unsplit(Cell *r, int cols, int x, int w)
{
        int end = x + w;

        if (iscont(&r[x]) && x > 0) {
                Pen keep = r[x - 1].s;
                r[x - 1] = VoidCell;
                r[x - 1].s = keep;
        }

        if (r[end - 1].w == 2 && !iscont(&r[end - 1]) && end < cols) {
                Pen keep = r[end].s;
                r[end] = VoidCell;
                r[end].s = keep;
        }
}

static void
put_cell(Scr *s, Cell *r, int x, u8 const *g, isize m, int w, Pen const *pen, u16 ln)
{
        Cell c = {0};

        unsplit(r, s->cols, x, w);

        set_glyph(s, &c, g, m);
        c.w  = (u8)w;
        c.ln = ln;
        c.s  = *pen;
        r[x] = c;

        if (w == 2) {
                Cell d = {0};
                d.ln = ln;
                d.s  = *pen;
                r[x + 1] = d;
        }
}

static void
put_esc(Scr *s, u8 const *p, isize k, Pen *pen, u16 *ln)
{
        isize off;
        isize len;

        if (p[1] == '[' && p[k - 1] == 'm') {
                sgr_cached(s->ops, pen, p + 2, k - 3);
                return;
        }

        if (!pen_osc8(p, k, &off, &len)) {
                return;
        }

        u8 const *semi = memchr(p + off, ';', len);

        if (semi == NULL || semi == p + off + len - 1) {
                *ln = 0;
                return;
        }

        u32 id = tab_get(&s->links, p + off, len);
        *ln = (u16)id;
}

static void
put_line(Scr *s, int y, int x0, u8 const *p, isize n, bool row)
{
        Pen pen = {0};
        u16 ln = 0;
        int x = x0;
        int last = -1;
        bool zwj = false;

        if (y < 0 || y >= s->rows) {
                return;
        }

        Cell *r = s->cur + (isize)y * s->cols;
        ScrRow *src = &s->line[y];

        if (row) {
                if (
                        !src->drawn
                     && (vN(src->src) == n)
                     && (n == 0 || memcmp(vv(src->src), p, n) == 0)
                ) {
                        return;
                }
                v0(src->src);
                xvPn(src->src, (char const *)p, n);
                src->drawn = false;
        } else {
                src->drawn = true;
        }

        s->dirty[y] = 1;

        for (isize i = 0; i < n;) {
                u8 c = p[i];

                if (c >= 0x20 && c < 0x7f && x >= 0 && x < s->cols) {
                        Cell *d = &r[x];
                        if (d->w != 1 || (x + 1 < s->cols && iscont(&d[1]))) {
                                unsplit(r, s->cols, x, 1);
                        }
                        *d = (Cell) { .g = { c }, .n = 1, .w = 1, .ln = ln, .s = pen };
                        last = x;
                        x += 1;
                        i += 1;
                        zwj = false;
                        continue;
                }

                isize k = term_esc_len(p, n, i);

                if (k > 0) {
                        put_esc(s, p + i, k, &pen, &ln);
                        i += k;
                        zwj = false;
                        continue;
                }

                i32 cp;
                isize m = utf8proc_iterate(p + i, n - i, &cp);

                if (m <= 0) {
                        i += 1;
                        continue;
                }

                int w = zwj ? 0 : utf8proc_charwidth(cp);
                zwj = (cp == 0x200d);

                if (cp < 0x20 || (cp >= 0x7f && cp < 0xa0)) {
                        i += m;
                        continue;
                }

                if (w == 0) {
                        if (last >= 0) {
                                attach(s, &r[last], p + i, m);
                        }
                        i += m;
                        continue;
                }

                if (x < 0) {
                        if (x + w > 0) {
                                put_cell(s, r, 0, (u8 const *)" ", 1, 1, &pen, ln);
                        }
                        x += w;
                        i += m;
                        continue;
                }

                if (x + w > s->cols) {
                        if (x < s->cols) {
                                put_cell(s, r, x, (u8 const *)" ", 1, 1, &pen, ln);
                                x += 1;
                        }
                        break;
                }

                put_cell(s, r, x, p + i, m, w, &pen, ln);
                last = x;
                x += w;
                i += m;
        }

        if (row) {
                for (x = max(x, 0); x < s->cols; ++x) {
                        r[x] = VoidCell;
                }
        }
}

static void
fill_void(Cell *c, isize n)
{
        for (isize i = 0; i < n; ++i) {
                c[i] = VoidCell;
        }
}

static bool
row_void(Cell const *r, int cols)
{
        for (int x = 0; x < cols; ++x) {
                if (!isvoid(&r[x])) {
                        return false;
                }
        }

        return true;
}

static void
free_rows(Scr *s)
{
        for (int y = 0; y < s->rows && s->line != NULL; ++y) {
                xvF(s->line[y].src);
        }

        xmF(s->line);
        s->line = NULL;
}

static void
scr_alloc(Scr *s, int cols, int rows)
{
        isize n = (isize)cols * rows;

        xmF(s->cur);
        xmF(s->prev);
        xmF(s->dirty);
        free_rows(s);

        s->cols  = cols;
        s->rows  = rows;
        s->cur   = xtA(Cell, max(n, 1));
        s->prev  = xtA(Cell, max(n, 1));
        s->dirty = xmA(max(rows, 1));
        s->line  = xtA0(ScrRow, max(rows, 1));
        s->valid = false;
        s->crow  = 0;

        fill_void(s->cur, n);
        fill_void(s->prev, n);
        memset(s->dirty, 1, max(rows, 1));

        tab_clear(&s->glyphs);
        tab_clear(&s->links);
}

void
screen_free(Ty *ty, void *p)
{
        Scr *s = p;

        xmF(s->cur);
        xmF(s->prev);
        xmF(s->dirty);
        free_rows(s);
        tab_clear(&s->glyphs);
        tab_clear(&s->links);
        xvF(s->glyphs);
        xvF(s->links);
        xvF(s->buf);
        xmF(s->ops);
        xmF(s->trs);
}

typedef struct {
        Scr         *s;
        byte_vector *o;
        Pen          pen;
        bool         known;
        u16          ln;
        int          cy;
        int          cx;
        bool         rel;
        bool         fill;
} Emit;

inline static void
out(Emit *e, void const *p, isize n)
{
        byte_vector *o = e->o;

        if (n <= 16 && vN(*o) + n <= vC(*o)) {
                char *d = vv(*o) + vN(*o);
                char const *q = p;
                for (isize i = 0; i < n; ++i) {
                        d[i] = q[i];
                }
                vN(*o) += n;
        } else {
                xvPn(*o, (char const *)p, n);
        }
}

#define OUTLIT(e, s) out((e), (s), sizeof (s) - 1)

static void
out_num_seq(Emit *e, u32 a, char fin)
{
        char b[16];
        char *o = b;

        *o++ = '\x1b';
        *o++ = '[';
        o = putu(o, a);
        *o++ = fin;

        out(e, b, o - b);
}

static Pen
eff(Emit const *e, Cell const *c)
{
        Pen p = c->s;

        if (p.bg == 0 && (e->fill || !(p.fl & PEN_VOID))) {
                p.bg = e->s->dbg;
        }

        p.fl = 0;

        return p;
}

inline static u32
pen_hash(Pen const *a, Pen const *b)
{
        u32 h = a->fg * 0x9e3779b1u;

        h ^= a->bg * 0x85ebca77u;
        h ^= a->uc * 0xc2b2ae3du;
        h ^= (a->at | ((u32)a->ul << 16)) * 0x27d4eb2fu;
        h ^= b->fg * 0x165667b1u;
        h ^= b->bg * 0xd3a2646cu;
        h ^= b->uc * 0xfd7046c5u;
        h ^= (b->at | ((u32)b->ul << 16)) * 0xb55a4f09u;

        return h ^ (h >> 15);
}

static void
set_pen(Emit *e, Pen const *p)
{
        char b[PEN_SGR_MAX];

        if (e->known && pen_eq(&e->pen, p)) {
                return;
        }

        if (!e->known) {
                int n = pen_diff(b, &e->pen, p, false);
                out(e, b, n);
                e->pen   = *p;
                e->known = true;
                return;
        }

        TrSlot *t = &e->s->trs[pen_hash(&e->pen, p) % TR_SLOTS];

        if (!t->used || !pen_eq(&t->a, &e->pen) || !pen_eq(&t->b, p)) {
                int n = pen_diff(b, &e->pen, p, true);
                if (n > TR_MAX) {
                        out(e, b, n);
                        e->pen = *p;
                        return;
                }
                t->used = true;
                t->a    = e->pen;
                t->b    = *p;
                t->n    = (u8)n;
                memcpy(t->sgr, b, n);
        }

        out(e, t->sgr, t->n);
        e->pen = *p;
}

static void
set_link(Emit *e, u16 ln)
{
        if (ln == e->ln) {
                return;
        }

        if (ln == 0) {
                OUTLIT(e, "\x1b]8;;\x1b\\");
        } else {
                ScrStr const *l = v_(e->s->links, ln - 1);
                OUTLIT(e, "\x1b]8;");
                out(e, l->p, l->n);
                OUTLIT(e, "\x1b\\");
        }

        e->ln = ln;
}

static bool
reemit(Emit *e, Cell const *r, int from, int to)
{
        int seq = 3 + ((to - from) >= 10) + ((to - from) >= 100);
        int bytes = 0;

        for (int x = from; x < to; ++x) {
                Cell const *c = &r[x];
                if (c->w != 1 || c->n == GLYPH_LONG || c->ln != e->ln) {
                        return false;
                }
                Pen p = eff(e, c);
                if (!pen_eq(&p, &e->pen)) {
                        return false;
                }
                bytes += c->n;
                if (bytes > seq + 1) {
                        return false;
                }
        }

        for (int x = from; x < to; ++x) {
                out(e, r[x].g, r[x].n);
        }

        return true;
}

static void
col_to(Emit *e, Cell const *r, int x)
{
        if (e->cx == x) {
                return;
        }

        if (x == 0) {
                OUTLIT(e, "\r");
        } else if (x < e->cx || e->cx >= e->s->cols) {
                out_num_seq(e, x + 1, 'G');
        } else if (!(e->known && reemit(e, r, e->cx, x))) {
                out_num_seq(e, x - e->cx, 'C');
        }

        e->cx = x;
}

static void
move_to(Emit *e, Cell const *r, int y, int x)
{
        if (e->cy == y && e->cx == x) {
                return;
        }

        if (e->rel) {
                if (y > e->cy) {
                        OUTLIT(e, "\r");
                        for (int i = e->cy; i < y; ++i) {
                                OUTLIT(e, "\n");
                        }
                        e->cx = 0;
                } else if (y < e->cy) {
                        out_num_seq(e, e->cy - y, 'A');
                }
                e->cy = y;
                col_to(e, r, x);
                return;
        }

        if (e->cy == y && x > e->cx && e->cx >= 0 && e->cx < e->s->cols) {
                if (!(e->known && reemit(e, r, e->cx, x))) {
                        out_num_seq(e, x - e->cx, 'C');
                }
        } else if (x == 0 && y == e->cy + 1 && e->cy >= 0) {
                OUTLIT(e, "\r\n");
        } else {
                char b[32];
                char *o = b;
                *o++ = '\x1b';
                *o++ = '[';
                o = putu(o, y + 1);
                *o++ = ';';
                o = putu(o, x + 1);
                *o++ = 'H';
                out(e, b, o - b);
        }

        e->cy = y;
        e->cx = x;
}

static void
flush_row(Emit *e, int y)
{
        Scr *s = e->s;
        int cols = s->cols;
        Cell *c = s->cur + (isize)y * cols;
        Cell *p = s->prev + (isize)y * cols;
        int vend = cols;

        while (vend > 0 && isvoid(&c[vend - 1])) {
                vend -= 1;
        }

        for (int x = 0; x < cols;) {
                Cell const *a = &c[x];

                if (iscont(a)) {
                        x += 1;
                        continue;
                }

                int w = max(a->w, 1);
                bool same = memcmp(a, &p[x], sizeof *a) == 0
                         && (
                                (w < 2)
                             || (x + 1 >= cols)
                             || memcmp(&c[x + 1], &p[x + 1], sizeof *a) == 0
                         );

                if (same) {
                        x += w;
                        continue;
                }

                if (x >= vend && cols - x >= 4) {
                        Pen vp = eff(e, &VoidCell);
                        move_to(e, c, y, x);
                        set_pen(e, &vp);
                        OUTLIT(e, "\x1b[K");
                        break;
                }

                Pen ap = eff(e, a);
                u8 const *g;
                isize gn = glyph_bytes(s, a, &g);

                move_to(e, c, y, x);
                set_pen(e, &ap);
                set_link(e, a->ln);
                out(e, g, gn);

                e->cx += w;
                x += w;
        }
}

static isize
scr_flush(Scr *s, bool rel)
{
        Emit e = {
                .s     = s,
                .o     = &s->buf,
                .pen   = {0},
                .known = s->valid,
                .ln    = 0,
                .cy    = -1,
                .cx    = -1,
                .rel   = rel,
                .fill  = !rel
        };
        isize area = (isize)s->cols * s->rows;

        v0(s->buf);

        if (!s->valid) {
                fill_void(s->prev, area);
                memset(s->dirty, 1, max(s->rows, 1));
                if (rel) {
                        s->crow = 0;
                } else {
                        Pen vp = eff(&e, &VoidCell);
                        set_pen(&e, &vp);
                        OUTLIT(&e, "\x1b[2J");
                }
                s->valid = true;
        }

        if (rel) {
                e.cy = s->crow;
                e.cx = 0;
        }

        for (int y = 0; y < s->rows; ++y) {
                if (!s->dirty[y]) {
                        continue;
                }

                s->dirty[y] = 0;

                Cell *c = s->cur + (isize)y * s->cols;
                Cell *p = s->prev + (isize)y * s->cols;

                if (memcmp(c, p, s->cols * sizeof *c) == 0) {
                        continue;
                }

                flush_row(&e, y);
                memcpy(p, c, s->cols * sizeof *c);
        }

        set_link(&e, 0);

        if (e.known && !pen_plain(&e.pen)) {
                OUTLIT(&e, "\x1b[0m");
        }

        if (rel) {
                if (e.cy < s->rows) {
                        OUTLIT(&e, "\r");
                        for (int i = e.cy; i < s->rows; ++i) {
                                OUTLIT(&e, "\n");
                        }
                } else if (e.cx != 0) {
                        OUTLIT(&e, "\r");
                }
                s->crow = s->rows;
        }

        return vN(s->buf);
}

static Scr *
scr_arg(Ty *ty, char const *_name__, Value v)
{
        if (
                (v.type != VALUE_PTR)
             || (v.gcptr == NULL)
             || (v.ptr != v.gcptr)
             || (ALLOC_OF(v.gcptr)->type != GC_SCREEN)
        ) {
                bP("expected a screen handle but got: %s", VSC(&v));
        }

        return v.ptr;
}

static int
dim_arg(Ty *ty, char const *_name__, char const *what, Value v)
{
        if (v.type != VALUE_INTEGER || v.z < 0 || v.z > 4096) {
                bP("bad %s: %s", what, VSC(&v));
        }

        return (int)v.z;
}

// vt.screen(cols: Int, rows: Int) -> Ptr[Any]
//
// Allocate a cell-grid screen with damage tracking.
TY_BUILTIN_RAW(vt_screen)
{
        ASSERT_ARGC("vt.screen()", 2);

        int cols = dim_arg(ty, _name__, "cols", ARG(0));
        int rows = dim_arg(ty, _name__, "rows", ARG(1));

        Scr *s = mAo0(sizeof *s, GC_SCREEN);
        s->ops = xtA0(OpSlot, OP_SLOTS);
        s->trs = xtA0(TrSlot, TR_SLOTS);
        scr_alloc(s, cols, rows);

        return GCPTR(s, s);
}

// vt.resize(scr: Ptr[Any], cols: Int, rows: Int) -> nil
//
// Resize the grid. Everything is cleared and the next flush repaints fully.
TY_BUILTIN_RAW(vt_resize)
{
        ASSERT_ARGC("vt.resize()", 3);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        int cols = dim_arg(ty, _name__, "cols", ARG(1));
        int rows = dim_arg(ty, _name__, "rows", ARG(2));

        if (cols != s->cols || rows != s->rows) {
                scr_alloc(s, cols, rows);
        }

        return NIL;
}

// vt.background(scr: Ptr[Any], sgr: String) -> nil
//
// Set the color used for cells whose background is the default, given as an
// SGR escape sequence such as "\x1b[48;2;26;26;46m" (or '' for none).
TY_BUILTIN_RAW(vt_background)
{
        ASSERT_ARGC("vt.background()", 2);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        Value sgr = ARGx(1, VALUE_STRING);
        Pen p = {0};
        u8 const *b = ss(sgr);
        isize n = sN(sgr);

        for (isize i = 0; i < n;) {
                isize k = term_esc_len(b, n, i);
                if (k > 0 && b[i + 1] == '[' && b[i + k - 1] == 'm') {
                        pen_sgr(&p, b + i + 2, k - 3);
                }
                i += max(k, 1);
        }

        if (p.bg != s->dbg) {
                s->dbg = p.bg;
                s->valid = false;
        }

        return NIL;
}

// vt.frame(scr: Ptr[Any], lines: Array[String]) -> nil
//
// Replace the whole grid with `lines` (ANSI-styled); rows past the end of a
// line or past the last line become blank.
TY_BUILTIN_RAW(vt_frame)
{
        ASSERT_ARGC("vt.frame()", 2);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        Value lines = ARGx(1, VALUE_ARRAY);
        Array *a = lines.array;
        int n = (int)min(vN(*a), s->rows);

        for (int y = 0; y < n; ++y) {
                Value const *line = v_(*a, y);
                if (line->type != VALUE_STRING) {
                        bP("lines[%d] is not a string: %s", y, VSC(line));
                }
                put_line(s, y, 0, ss(*line), sN(*line), true);
        }

        for (int y = n; y < s->rows; ++y) {
                Cell *r = s->cur + (isize)y * s->cols;
                if (!row_void(r, s->cols)) {
                        fill_void(r, s->cols);
                        s->dirty[y] = 1;
                }
                v0(s->line[y].src);
                s->line[y].drawn = true;
        }

        return NIL;
}

// vt.put(scr: Ptr[Any], y: Int, x: Int, line: String) -> nil
//
// Draw an ANSI-styled line over the grid at row `y`, column `x`.
TY_BUILTIN_RAW(vt_put)
{
        ASSERT_ARGC("vt.put()", 4);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        i64 y = INT_ARG(1);
        i64 x = INT_ARG(2);
        Value line = ARGx(3, VALUE_STRING);

        if (y >= 0 && y < s->rows && x < s->cols && x > -(i64)sN(line) - 1) {
                put_line(s, (int)y, (int)x, ss(line), sN(line), false);
        }

        return NIL;
}

// vt.flush(scr: Ptr[Any], out: Blob, inline: Bool = false) -> Int
//
// Append the escape sequences that bring the terminal from the previously
// flushed grid to the current one, and return the number of bytes appended.
// With `inline`, cursor motion is relative to the top of the region and the
// cursor is left on the line below it.
TY_BUILTIN_RAW(vt_flush)
{
        ASSERT_ARGC("vt.flush()", 2, 3);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        Value blob = ARGx(1, VALUE_BLOB);
        Value *rel = NAMED("inline");
        bool inl = false;

        if (argc == 3) {
                inl = value_truthy(ty, &ARG(2));
        } else if (rel != NULL) {
                inl = value_truthy(ty, rel);
        }

        isize n = scr_flush(s, inl);

        vvPn(*blob.blob, (u8 const *)vv(s->buf), n);

        return INTEGER(n);
}

// vt.invalidate(scr: Ptr[Any]) -> nil
//
// Forget what the terminal shows. The next flush clears the screen (or, when
// inline, assumes a blank region with the cursor at its top) and repaints.
TY_BUILTIN_RAW(vt_invalidate)
{
        ASSERT_ARGC("vt.invalidate()", 1);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        s->valid = false;

        return NIL;
}

// vt.touch(scr: Ptr[Any]) -> nil
//
// Re-send every cell on the next flush without clearing the terminal, e.g.
// after something else has drawn over the screen.
TY_BUILTIN_RAW(vt_touch)
{
        ASSERT_ARGC("vt.touch()", 1);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        isize area = (isize)s->cols * s->rows;

        for (isize i = 0; i < area; ++i) {
                s->prev[i] = LostCell;
        }

        memset(s->dirty, 1, max(s->rows, 1));

        return NIL;
}

// vt.valid(scr: Ptr[Any]) -> Bool
//
// Whether the next flush will be incremental (false after creation, resize,
// a background change, or invalidate()).
TY_BUILTIN_RAW(vt_valid)
{
        ASSERT_ARGC("vt.valid()", 1);

        Scr *s = scr_arg(ty, _name__, ARG(0));

        return BOOLEAN(s->valid);
}

// vt.text(scr: Ptr[Any]) -> Array[String]
//
// The current grid as plain text, one string per row.
TY_BUILTIN_RAW(vt_text)
{
        ASSERT_ARGC("vt.text()", 1);

        Scr *s = scr_arg(ty, _name__, ARG(0));
        Array *a = vA();
        Value av = ARRAY(a);
        byte_vector row = {0};

        gP(&av);

        for (int y = 0; y < s->rows; ++y) {
                Cell const *r = s->cur + (isize)y * s->cols;
                v0(row);
                for (int x = 0; x < s->cols; ++x) {
                        u8 const *g;
                        isize n = glyph_bytes(s, &r[x], &g);
                        xvPn(row, (char const *)g, n);
                }
                vAp(a, vSs(vv(row), vN(row)));
        }

        gX();
        xvF(row);

        return ARRAY(a);
}

/* vim: set sw=8 sts=8 expandtab: */
