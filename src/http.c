#include <pthread.h>
#include <string.h>

#if defined(__linux__) || defined(__FreeBSD__)
#include <sys/random.h>
#else
#include <unistd.h>
#endif

#include <nghttp2/nghttp2.h>

#include "ty.h"
#include "value.h"
#include "dict.h"
#include "vm.h"
#include "class.h"
#include "functions.h"
#include "blob.h"

enum {
        C_TCHAR = 1,
        C_VCHAR = 2,
        C_FIELD = 4,
        C_DIGIT = 8,
        C_HEX   = 16,
        C_UPPER = 32
};

enum {
        F_CHUNKED    = 1,
        F_CLOSE      = 2,
        F_KEEP_ALIVE = 4,
        F_CONTINUE   = 8,
        F_HOST       = 16,
        F_UPGRADE    = 32,
        F_CODED      = 64
};

enum {
        M_OFF = 0,
        M_LEN = 1,
        T_OFF = 2,
        T_LEN = 3,
        MINOR = 4,
        NHEAD = 5,
        CLEN  = 6,
        FLAGS = 7,
        CTYPE = 8,
        HEAD  = 9
};

enum {
        E_REQUEST_LINE = -1,
        E_VERSION      = -2,
        E_HEADER       = -3,
        E_TOO_MANY     = -4,
        E_LENGTH       = -5,
        E_FRAMING      = -6
};

enum {
        D_STATE,
        D_LEFT,
        D_SIZE,
        D_DIGITS,
        D_LINE,
        D_DONE,
        D_N
};

static u8 const CharClass[256] = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x04, 0x07, 0x06, 0x07, 0x07, 0x07, 0x07, 0x07, 0x06, 0x06, 0x07, 0x07, 0x06, 0x07, 0x07, 0x06,
        0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x1f, 0x06, 0x06, 0x06, 0x06, 0x06, 0x06,
        0x06, 0x37, 0x37, 0x37, 0x37, 0x37, 0x37, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27,
        0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x27, 0x06, 0x06, 0x06, 0x07, 0x07,
        0x07, 0x17, 0x17, 0x17, 0x17, 0x17, 0x17, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07,
        0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x07, 0x06, 0x07, 0x06, 0x07, 0x00,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
        0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04, 0x04,
};

#define IS(c, k) ((CharClass[(c)] & C_##k) != 0)

typedef struct {
        u8 const *b;
        Value    *out;
        isize     nout;
} Scan;

inline static bool
lower_eq(u8 const *p, isize n, char const *w, isize wn)
{
        if (n != wn) {
                return false;
        }

        for (isize k = 0; k < n; ++k) {
                if ((p[k] | (CharClass[p[k]] & C_UPPER)) != (u8)w[k]) {
                        return false;
                }
        }

        return true;
}

#define LEQ(p, n, w) lower_eq((p), (n), (w), sizeof (w) - 1)

inline static bool
ascii_ieq(u8 const *p, u8 const *q, isize n)
{
        for (isize k = 0; k < n; ++k) {
                if ((p[k] | (CharClass[p[k]] & C_UPPER)) != (q[k] | (CharClass[q[k]] & C_UPPER))) {
                        return false;
                }
        }

        return true;
}

inline static i64
decimal(u8 const *p, isize n)
{
        i64 x = 0;

        if (n == 0 || n > 15) {
                return -1;
        }

        for (isize k = 0; k < n; ++k) {
                if (!IS(p[k], DIGIT)) {
                        return -1;
                }
                x = 10 * x + (p[k] - '0');
        }

        return x;
}

inline static void
put(Scan *sc, isize i, i64 x)
{
        sc->out[i] = INTEGER(x);
}

static isize
scan_fields(Scan *sc, isize start, isize i, isize end, bool resp)
{
        u8 const *b = sc->b;
        i64 length = -1;
        i64 n      = 0;
        i64 fl     = 0;
        i64 ctype  = -1;

        for (;;) {
                if (end - i < 2) {
                        return 0;
                }

                if (b[i] == '\r') {
                        if (b[i + 1] != '\n') {
                                return E_HEADER;
                        }
                        if ((fl & F_CHUNKED) && length >= 0) {
                                if (!resp) {
                                        return E_LENGTH;
                                }
                                length = -1;
                                fl |= F_CLOSE;
                        }
                        put(sc, NHEAD, n);
                        put(sc, CLEN,  length);
                        put(sc, FLAGS, fl);
                        put(sc, CTYPE, ctype);
                        return i + 2 - start;
                }

                isize k = i;
                while (i < end && IS(b[i], TCHAR)) {
                        i += 1;
                }
                if (i == end) {
                        return 0;
                }
                if (i == k || b[i] != ':') {
                        return E_HEADER;
                }
                isize klen = i - k;
                i += 1;

                while (i < end && (b[i] == ' ' || b[i] == '\t')) {
                        i += 1;
                }
                isize v = i;
                isize e = i;
                while (i < end && IS(b[i], FIELD)) {
                        if (b[i] != ' ' && b[i] != '\t') {
                                e = i + 1;
                        }
                        i += 1;
                }
                if (end - i < 2) {
                        return 0;
                }
                if (b[i] != '\r' || b[i + 1] != '\n') {
                        return E_HEADER;
                }
                i += 2;

                isize o = HEAD + 4 * n;
                if (o + 4 > sc->nout) {
                        return E_TOO_MANY;
                }
                put(sc, o,     k);
                put(sc, o + 1, klen);
                put(sc, o + 2, v);
                put(sc, o + 3, e - v);

                u8 const *key = b + k;
                u8 const *val = b + v;
                isize    vlen = e - v;

                switch (klen) {
                case 14:
                        if (LEQ(key, klen, "content-length")) {
                                i64 x = decimal(val, vlen);
                                if (x < 0 || (length >= 0 && x != length)) {
                                        return E_LENGTH;
                                }
                                length = x;
                        }
                        break;

                case 17:
                        if (!LEQ(key, klen, "transfer-encoding")) {
                                break;
                        }
                        if (LEQ(val, vlen, "chunked") && !(fl & F_CHUNKED)) {
                                fl |= F_CHUNKED;
                        } else if (!resp) {
                                return E_FRAMING;
                        } else if (
                                (vlen > 7)
                             && LEQ(b + e - 7, 7, "chunked")
                             && (b[e - 8] == ',' || b[e - 8] == ' ')
                        ) {
                                fl |= F_CHUNKED | F_CODED;
                        } else {
                                fl = (fl & ~F_CHUNKED) | F_CODED | F_CLOSE;
                        }
                        break;

                case 10:
                        if (!LEQ(key, klen, "connection")) {
                                break;
                        }
                        if (LEQ(val, vlen, "close")) {
                                fl |= F_CLOSE;
                        } else if (LEQ(val, vlen, "keep-alive")) {
                                fl |= F_KEEP_ALIVE;
                        }
                        break;

                case 4:
                        if (LEQ(key, klen, "host")) {
                                fl |= F_HOST;
                        }
                        break;

                case 7:
                        if (LEQ(key, klen, "upgrade")) {
                                fl |= F_UPGRADE;
                        }
                        break;

                case 6:
                        if (LEQ(key, klen, "expect") && LEQ(val, vlen, "100-continue")) {
                                fl |= F_CONTINUE;
                        }
                        break;

                case 12:
                        if (LEQ(key, klen, "content-type")) {
                                ctype = n;
                        }
                        break;
                }

                n += 1;
        }
}

inline static bool
version_ok(u8 const *b)
{
        return memcmp(b, "HTTP/", 5) == 0
            && IS(b[5], DIGIT)
            && (b[6] == '.')
            && IS(b[7], DIGIT);
}

static isize
scan_head(Scan *sc, isize start, isize end)
{
        u8 const *b = sc->b;
        isize i = start;

        while (i < end && (b[i] == '\r' || b[i] == '\n')) {
                i += 1;
        }

        isize m = i;
        while (i < end && IS(b[i], TCHAR)) {
                i += 1;
        }
        if (i == end) {
                return 0;
        }
        if (i == m || b[i] != ' ') {
                return E_REQUEST_LINE;
        }
        put(sc, M_OFF, m);
        put(sc, M_LEN, i - m);
        i += 1;

        isize t = i;
        while (i < end && IS(b[i], VCHAR)) {
                i += 1;
        }
        if (i == end) {
                return 0;
        }
        if (i == t || b[i] != ' ') {
                return E_REQUEST_LINE;
        }
        put(sc, T_OFF, t);
        put(sc, T_LEN, i - t);
        i += 1;

        if (end - i < 10) {
                return 0;
        }
        if (!version_ok(b + i) || b[i + 8] != '\r' || b[i + 9] != '\n') {
                return E_REQUEST_LINE;
        }
        if (b[i + 5] != '1') {
                return E_VERSION;
        }
        put(sc, MINOR, b[i + 7] - '0');
        i += 10;

        return scan_fields(sc, start, i, end, false);
}

static isize
scan_status(Scan *sc, isize start, isize end)
{
        u8 const *b = sc->b;
        isize i = start;

        if (end - i < 12) {
                for (isize k = 0; k < 5 && k < end - i; ++k) {
                        if (b[i + k] != "HTTP/"[k]) {
                                return E_REQUEST_LINE;
                        }
                }
                return 0;
        }
        if (!version_ok(b + i) || b[i + 8] != ' ') {
                return E_REQUEST_LINE;
        }
        if (b[i + 5] != '1') {
                return E_VERSION;
        }
        put(sc, MINOR, b[i + 7] - '0');
        i += 9;

        i64 code = 0;
        for (isize k = 0; k < 3; ++k) {
                if (!IS(b[i + k], DIGIT)) {
                        return E_REQUEST_LINE;
                }
                code = 10 * code + (b[i + k] - '0');
        }
        i += 3;
        put(sc, M_OFF, code);
        put(sc, M_LEN, 0);

        if (i < end && b[i] == ' ') {
                i += 1;
        }
        isize r = i;
        while (i < end && b[i] != '\r') {
                if (!IS(b[i], FIELD)) {
                        return E_REQUEST_LINE;
                }
                i += 1;
        }
        if (end - i < 2) {
                return 0;
        }
        if (b[i + 1] != '\n') {
                return E_REQUEST_LINE;
        }
        put(sc, T_OFF, r);
        put(sc, T_LEN, i - r);
        i += 2;

        return scan_fields(sc, start, i, end, true);
}

inline static int
hexval(u8 c)
{
        return IS(c, DIGIT) ? (c - '0') : ((c | 0x20) - 'a' + 10);
}

static isize
dechunk(u8 const *b, isize start, isize end, u8 *dst, isize *olen)
{
        isize i = start;
        isize o = 0;

        for (;;) {
                i64 size   = 0;
                int digits = 0;
                while (i < end && IS(b[i], HEX)) {
                        size = 16 * size + hexval(b[i]);
                        if (++digits > 15) {
                                return -1;
                        }
                        i += 1;
                }
                if (i == end) {
                        return 0;
                }
                if (digits == 0) {
                        return -1;
                }
                while (i < end && b[i] != '\r') {
                        if (!IS(b[i], FIELD)) {
                                return -1;
                        }
                        i += 1;
                }
                if (end - i < 2) {
                        return 0;
                }
                if (b[i + 1] != '\n') {
                        return -1;
                }
                i += 2;

                if (size == 0) {
                        for (;;) {
                                if (end - i < 2) {
                                        return 0;
                                }
                                if (b[i] == '\r' && b[i + 1] == '\n') {
                                        *olen = o;
                                        return i + 2 - start;
                                }
                                while (i < end && b[i] != '\r') {
                                        i += 1;
                                }
                                if (end - i < 2) {
                                        return 0;
                                }
                                if (b[i + 1] != '\n') {
                                        return -1;
                                }
                                i += 2;
                        }
                }

                if (end - i < size + 2) {
                        return 0;
                }
                memcpy(dst + o, b + i, size);
                o += size;
                i += size;
                if (b[i] != '\r' || b[i + 1] != '\n') {
                        return -1;
                }
                i += 2;
        }
}

static Value *
ints(Ty *ty, char const *ctx, char const *name, Value v, isize min, isize *n)
{
        if (v.type != VALUE_ARRAY || vN(*v.array) < min) {
                TyBuiltinBadArg(ty, ctx, name, "Array[Int]", &v);
        }

        *n = vN(*v.array);

        return vv(*v.array);
}

static void
span(Ty *ty, char const *ctx, Blob const *b, i64 start, i64 end)
{
        if (start < 0 || end < start || end > vN(*b)) {
                zP("%s: bad range [%"PRIi64", %"PRIi64") of %zu bytes", ctx, start, end, vN(*b));
        }
}

// _http.scan-head(b: Blob, start: Int, end: Int, out: Array[Int]) -> Int
TY_BUILTIN(http_scan_head)
{
        Scan sc = { .b = vv(*b) };

        span(ty, _name__, b, start, end);
        sc.out = ints(ty, _name__, "out", out, HEAD, &sc.nout);

        return INTEGER(scan_head(&sc, start, end));
}

// _http.scan-status(b: Blob, start: Int, end: Int, out: Array[Int]) -> Int
TY_BUILTIN(http_scan_status)
{
        Scan sc = { .b = vv(*b) };

        span(ty, _name__, b, start, end);
        sc.out = ints(ty, _name__, "out", out, HEAD, &sc.nout);

        return INTEGER(scan_status(&sc, start, end));
}

// _http.dechunk(b: Blob, start: Int, end: Int) -> (Int, String) | Int
TY_BUILTIN(http_dechunk)
{
        isize olen = 0;

        span(ty, _name__, b, start, end);

        u8 *dst = xmA(max(end - start, 1));
        isize r = dechunk(vv(*b), start, end, dst, &olen);

        if (r <= 0) {
                xmF(dst);
                return INTEGER(r);
        }

        Value pair = vT(2);
        gP(&pair);
        pair.items[0] = INTEGER(r);
        pair.items[1] = vSs((char const *)dst, olen);
        gX();

        xmF(dst);

        return pair;
}

// _http.pack-head(buf: Blob, start: Int, hlen: Int, marks: Array[Int], k: Int, base: Int) -> String
TY_BUILTIN(http_pack_head)
{
        isize n;

        span(ty, _name__, buf, start, start + hlen);

        Value const *m = ints(ty, _name__, "marks", marks, k, &n);

        if (hlen > 4 * base) {
                bP("base is too small");
        }

        isize size = 4 * (base + k);
        char *head = value_string_alloc(ty, size);

        memset(head + hlen, 0, 4 * base - hlen);
        memcpy(head, vv(*buf) + start, hlen);

        i32 *out = (i32 *)head + base;

        for (isize i = 0; i < k; ++i) {
                bool off = (i < HEAD) ? (i == M_OFF || i == T_OFF)
                         :              (((i - HEAD) & 1) == 0);
                out[i] = off ? (m[i].z - start) : m[i].z;
        }

        return STRING(head, size);
}

// _http.mark(head: String, i: Int) -> Int
TY_BUILTIN(http_mark)
{
        if (i < 0 || 4 * (i + 1) > sN(head)) {
                bP("index out of range: %"PRIi64, i);
        }

        i32 x;
        memcpy(&x, ss(head) + 4 * i, sizeof x);

        return INTEGER(x);
}

// _http.header(head: String, base: Int, name: String) -> String | nil
TY_BUILTIN(http_header)
{
        isize n = sN(head) / 4;

        if (base < 0 || base + HEAD > n) {
                bP("bad base: %"PRIi64, base);
        }

        i32 const *m = (i32 const *)ss(head) + base;
        u8 const *b  = (u8 const *)ss(head);
        u8 const *w  = (u8 const *)ss(name);
        isize wn     = sN(name);
        isize total  = 0;
        int hits     = 0;

        if (base + HEAD + 4 * m[NHEAD] > n) {
                bP("bad marks");
        }

/* ========================================================================= */
#define FOR_MATCH(go)                                                            \
        for (int i = 0; i < m[NHEAD]; ++i) {                                     \
                i32 const *f = m + HEAD + 4 * i;                                 \
                if (f[1] != wn || !ascii_ieq(b + f[0], w, wn)) {                 \
                        continue;                                                \
                }                                                                \
                go;                                                              \
        }
/* ------------------------------------------------------------------------- */
        FOR_MATCH(total += f[3] + 2 * (hits++ > 0));

        if (hits == 0) {
                return NIL;
        }

        char *s = value_string_alloc(ty, total);
        isize at = 0;

        FOR_MATCH(
                if (at > 0) {
                        memcpy(s + at, ", ", 2);
                        at += 2;
                }
                memcpy(s + at, b + f[2], f[3]);
                at += f[3]
        );
/* ------------------------------------------------------------------------- */
#undef FOR_MATCH
/* ========================================================================= */

        return STRING(s, total);
}

// _http.dechunk-feed(st: Array[Int], buf: Blob, start: Int, end: Int, out: Blob) -> Int
TY_BUILTIN(http_dechunk_feed)
{
        isize n;
        i64 s[D_N];

        span(ty, _name__, buf, start, end);

        Value *sv = ints(ty, _name__, "st", st, D_N, &n);

        for (int k = 0; k < D_N; ++k) {
                s[k] = sv[k].z;
        }

        u8 const *b = vv(*buf);
        isize i = start;
        isize r;

        while (i < end && !s[D_DONE]) {
                u8 c = b[i];
                switch (s[D_STATE]) {
                case 0:
                        if (IS(c, HEX) && s[D_LINE] == 0) {
                                s[D_SIZE] = 16 * s[D_SIZE] + hexval(c);
                                if (++s[D_DIGITS] > 15) {
                                        r = -1;
                                        goto End;
                                }
                        } else if (c == '\r') {
                                s[D_STATE] = 1;
                        } else if (s[D_DIGITS] == 0 || !IS(c, FIELD)) {
                                r = -1;
                                goto End;
                        } else {
                                s[D_LINE] = 1;
                        }
                        i += 1;
                        break;

                case 1:
                        if (c != '\n') {
                                r = -1;
                                goto End;
                        }
                        i += 1;
                        s[D_LINE]   = 0;
                        s[D_DIGITS] = 0;
                        if (s[D_SIZE] == 0) {
                                s[D_STATE] = 4;
                        } else {
                                s[D_LEFT]  = s[D_SIZE];
                                s[D_SIZE]  = 0;
                                s[D_STATE] = 2;
                        }
                        break;

                case 2:
                {
                        isize k = min(s[D_LEFT], end - i);
                        vvPn(*out, b + i, k);
                        b = vv(*buf);
                        s[D_LEFT] -= k;
                        i += k;
                        if (s[D_LEFT] == 0) {
                                s[D_STATE] = 3;
                        }
                        break;
                }

                case 3:
                        if (c != (s[D_LINE] ? '\n' : '\r')) {
                                r = -1;
                                goto End;
                        }
                        s[D_LINE]  = !s[D_LINE];
                        s[D_STATE] = s[D_LINE] ? 3 : 0;
                        i += 1;
                        break;

                case 4:
                        s[D_LINE]  = (c != '\r');
                        s[D_STATE] = (c == '\r') ? 5 : 6;
                        i += 1;
                        break;

                case 5:
                        if (c != '\n') {
                                r = -1;
                                goto End;
                        }
                        i += 1;
                        s[D_DONE] = 1;
                        break;

                case 6:
                        if (c == '\n') {
                                s[D_STATE] = 4;
                        }
                        i += 1;
                        break;

                default:
                        r = -1;
                        goto End;
                }
        }

        r = i - start;

End:
        for (int k = 0; k < D_N; ++k) {
                sv[k] = INTEGER(s[k]);
        }

        return INTEGER(r);
}

enum {
        PCT_UNRESERVED,
        PCT_PATH,
        PCT_QUERY,
        PCT_USERINFO,
        PCT_KINDS
};

static u8 PctSafe[256];

static void
pct_init(void)
{
        static char const *const extra[PCT_KINDS] = {
                [PCT_UNRESERVED] = "",
                [PCT_PATH]       = "!$&'()*+,;=:@/",
                [PCT_QUERY]      = "!$&'()*+,;=:@/?",
                [PCT_USERINFO]   = "!$&'()*+,;=%"
        };

        for (int k = 0; k < PCT_KINDS; ++k) {
                for (int c = 0; c < 128; ++c) {
                        bool safe = (CharClass[c] & (C_DIGIT | C_UPPER)) != 0
                                 || (c >= 'a' && c <= 'z')
                                 || (c != 0 && strchr("-._~", c) != NULL)
                                 || (c != 0 && strchr(extra[k], c) != NULL);
                        PctSafe[c] |= safe << k;
                }
        }
}

inline static bool
pct_escape(u8 const *s, isize i, isize n, int kind)
{
        if (PctSafe[s[i]] & (1 << kind)) {
                return false;
        }

        return (s[i] != '%')
            || (kind == PCT_UNRESERVED)
            || (i + 2 >= n)
            || !IS(s[i + 1], HEX)
            || !IS(s[i + 2], HEX);
}

static void
pct_once(void)
{
        static pthread_once_t once = PTHREAD_ONCE_INIT;
        pthread_once(&once, pct_init);
}

static void
pct_encode_into(Ty *ty, byte_vector *out, u8 const *p, isize n, int kind)
{
        static char const hex[] = "0123456789ABCDEF";

        for (isize i = 0; i < n; ++i) {
                if (pct_escape(p, i, n, kind)) {
                        xvP(*out, '%');
                        xvP(*out, hex[p[i] >> 4]);
                        xvP(*out, hex[p[i] & 15]);
                } else {
                        xvP(*out, p[i]);
                }
        }
}

static isize
pct_decode_into(u8 *dst, u8 const *p, isize n, bool plus, bool form)
{
        isize j = 0;

        for (isize i = 0; i < n; ++i) {
                u8 c = p[i];
                if (c == '%' && i + 2 < n && IS(p[i + 1], HEX) && IS(p[i + 2], HEX)) {
                        c = (hexval(p[i + 1]) << 4) | hexval(p[i + 2]);
                        i += 2;
                } else if (plus && c == '+') {
                        c = ' ';
                }
                if (form && c == '\n' && j > 0 && dst[j - 1] == '\r') {
                        dst[j - 1] = '\n';
                        continue;
                }
                dst[j++] = c;
        }

        if (form) {
                for (isize k = 0; k < j; ++k) {
                        if (dst[k] == '\r') {
                                dst[k] = '\n';
                        }
                }
        }

        return j;
}

static Value
pct_decode(Ty *ty, u8 const *p, isize n, bool plus, bool form)
{
        u8 *buf = xmA(max(n, 1));
        isize j = pct_decode_into(buf, p, n, plus, form);
        Value result = LossyString(ty, buf, j);

        xmF(buf);

        return result;
}

// _http.percent-encode(s: String, kind: Int = 0) -> String
TY_BUILTIN(http_percent_encode)
{
        pct_once();

        if (kind < 0 || kind >= PCT_KINDS) {
                bP("bad kind: %"PRIi64, kind);
        }

        u8 const *p = (u8 const *)ss(s);
        isize n = sN(s);
        isize i = 0;

        while (i < n && !pct_escape(p, i, n, kind)) {
                i += 1;
        }

        if (i == n) {
                return s;
        }

        byte_vector out = {0};
        xvPn(out, p, i);
        pct_encode_into(ty, &out, p + i, n - i, kind);

        Value result = vSs(vv(out), vN(out));
        xvF(out);

        return result;
}

// _http.percent-decode(s: String, plus: Bool = false, form: Bool = false) -> String
TY_BUILTIN(http_percent_decode)
{
        u8 const *p = (u8 const *)ss(s);
        isize n = sN(s);

        if (
                (memchr(p, '%', n) == NULL)
             && !(plus && memchr(p, '+', n) != NULL)
             && !(form && memchr(p, '\r', n) != NULL)
        ) {
                return s;
        }

        return pct_decode(ty, p, n, plus, form);
}

// _http.decode-query(query: String) -> Dict[String, String | Array[String | nil] | nil]
TY_BUILTIN(http_decode_query)
{
        Value d = DICT(dict_new(ty));
        u8 const *p = (u8 const *)ss(query);
        isize n = sN(query);
        isize i = 0;

        gP(&d);

        for (;;) {
                u8 const *amp = memchr(p + i, '&', n - i);
                isize end = (amp == NULL) ? n : (amp - p);
                u8 const *eq = memchr(p + i, '=', end - i);

                isize klen = (eq == NULL) ? (end - i) : (eq - (p + i));
                Value key = pct_decode(ty, p + i, klen, true, true);
                Value val = NIL;

                gP(&key);
                if (eq != NULL) {
                        isize at = eq + 1 - p;
                        val = pct_decode(ty, p + at, end - at, true, true);
                }
                gP(&val);

                Value *slot = dict_get_value(ty, d.dict, &key);

                if (slot == NULL || slot->type == VALUE_NIL) {
                        dict_put_value(ty, d.dict, key, val);
                } else if (slot->type == VALUE_STRING) {
                        Value one = *slot;
                        Value both = ARRAY(vA());
                        gP(&both);
                        vAp(both.array, one);
                        vAp(both.array, val);
                        dict_put_value(ty, d.dict, key, both);
                        gX();
                } else {
                        vAp(slot->array, val);
                }

                gX();
                gX();

                if (amp == NULL) {
                        break;
                }

                i = end + 1;
        }

        gX();

        return d;
}

static void
query_pair(Ty *ty, byte_vector *out, Value const *k, Value const *v, bool blank)
{
        Value ks = (k->type == VALUE_STRING) ? *k : value_vshow(ty, k, 0);

        if (vN(*out) > 0) {
                xvP(*out, '&');
        }

        pct_encode_into(ty, out, (u8 const *)ss(ks), sN(ks), PCT_UNRESERVED);

        if (v->type == VALUE_NIL) {
                if (blank) {
                        xvP(*out, '=');
                }
                return;
        }

        Value vs = (v->type == VALUE_STRING) ? *v : value_vshow(ty, v, 0);

        xvP(*out, '=');
        pct_encode_into(ty, out, (u8 const *)ss(vs), sN(vs), PCT_UNRESERVED);
}

static void
query_entry(Ty *ty, byte_vector *out, Value const *k, Value const *v, bool blank)
{
        if (v->type != VALUE_ARRAY) {
                query_pair(ty, out, k, v, blank);
                return;
        }

        vfor(*v->array, query_pair(ty, out, k, it, blank));
}

// _http.encode-query(params: Dict[_, _] | Array[(_, _)], blank: Bool = false) -> String
TY_BUILTIN(http_encode_query)
{
        byte_vector out = {0};

        pct_once();

        switch (params.type) {
        case VALUE_DICT:
                dfor(params.dict, query_entry(ty, &out, key, val, blank));
                break;

        case VALUE_ARRAY:
                vfor(*params.array, {
                        if (it->type != VALUE_TUPLE || it->count != 2) {
                                xvF(out);
                                bP("expected (key, value) pairs but got: %s", VSC(it));
                        }
                        query_entry(ty, &out, &it->items[0], &it->items[1], blank);
                });
                break;

        default:
                xvF(out);
                TyBuiltinBadArg(ty, _name__, "params", "Dict | Array[(_, _)]", &params);
        }

        Value result = vSs(vv(out), vN(out));
        xvF(out);

        return result;
}

enum {
        WS_OP_TEXT   = 0x1,
        WS_OP_BINARY = 0x2
};

enum {
        WS_RESERVED     = -1,
        WS_MASK         = -2,
        WS_LENGTH       = -3,
        WS_CONTROL      = -4,
        WS_TOO_BIG      = -5
};

enum {
        WS_OUT_OP,
        WS_OUT_FIN,
        WS_OUT_RSV1,
        WS_OUT_TOTAL,
        WS_OUT_LEN,
        WS_OUT_N
};

static void
ws_key(u8 key[4])
{
#if defined(__linux__) || defined(__FreeBSD__)
        while (getrandom(key, 4, 0) != 4) {
                continue;
        }
#else
        (void)getentropy(key, 4);
#endif
}

inline static void
ws_xor(u8 *dst, u8 const *src, isize n, u8 const key[4])
{
        for (isize i = 0; i < n; ++i) {
                dst[i] = src[i] ^ key[i & 3];
        }
}

static isize
ws_header(Ty *ty, char const *ctx, u8 hdr[14], int op, isize n, bool fin, Value mask, bool rsv1)
{
        isize nh = 2;

        hdr[0] = (fin ? 0x80 : 0) | (rsv1 ? 0x40 : 0) | (op & 0x0F);

        if (n < 126) {
                hdr[1] = n;
        } else if (n < 65536) {
                hdr[1] = 126;
                hdr[2] = n >> 8;
                hdr[3] = n;
                nh = 4;
        } else {
                hdr[1] = 127;
                for (int i = 0; i < 8; ++i) {
                        hdr[2 + i] = (u64)n >> (56 - 8 * i);
                }
                nh = 10;
        }

        switch (mask.type) {
        case VALUE_BLOB:
                if (vN(*mask.blob) != 4) {
                        zP("%s: mask must be 4 bytes", ctx);
                }
                memcpy(hdr + nh, vv(*mask.blob), 4);
                break;

        case VALUE_BOOLEAN:
                if (!mask.boolean) {
                        return nh;
                }
                ws_key(hdr + nh);
                break;

        case VALUE_NIL:
                return nh;

        default:
                TyBuiltinBadArg(ty, ctx, "mask", "Blob | Bool | nil", &mask);
        }

        hdr[1] |= 0x80;

        return nh + 4;
}

static void
ws_body(u8 *dst, u8 const hdr[14], isize nh, u8 const *p, isize n)
{
        memcpy(dst, hdr, nh);

        if (hdr[1] & 0x80) {
                ws_xor(dst + nh, p, n, hdr + nh - 4);
        } else {
                memcpy(dst + nh, p, n);
        }
}

static void
bytes_of(Ty *ty, char const *ctx, char const *name, Value v, u8 const **p, isize *n)
{
        switch (v.type) {
        case VALUE_STRING: *p = (u8 const *)ss(v); *n = sN(v);         break;
        case VALUE_BLOB:   *p = vv(*v.blob);       *n = vN(*v.blob);   break;
        default:           TyBuiltinBadArg(ty, ctx, name, "String | Blob", &v);
        }
}

// _http.ws-frame(op: Int, payload: String | Blob, fin: Bool = true, mask: Blob | Bool | nil = nil, rsv1: Bool = false) -> String
TY_BUILTIN(http_ws_frame)
{
        u8 const *p;
        isize n;
        u8 hdr[14];

        bytes_of(ty, _name__, "payload", payload, &p, &n);

        isize nh = ws_header(ty, _name__, hdr, op, n, fin, mask, rsv1);
        u8 *out  = (u8 *)value_string_alloc(ty, nh + n);

        bytes_of(ty, _name__, "payload", payload, &p, &n);
        ws_body(out, hdr, nh, p, n);

        return STRING((char *)out, nh + n);
}

// _http.ws-frame-into(out: Blob, op: Int, payload: String | Blob, fin: Bool = true, mask: Blob | Bool | nil = nil, rsv1: Bool = false) -> Blob
TY_BUILTIN(http_ws_frame_into)
{
        u8 const *p;
        isize n;
        u8 hdr[14];

        bytes_of(ty, _name__, "payload", payload, &p, &n);

        isize nh = ws_header(ty, _name__, hdr, op, n, fin, mask, rsv1);

        vvR(*out, vN(*out) + nh + n);
        bytes_of(ty, _name__, "payload", payload, &p, &n);
        ws_body(vZ(*out), hdr, nh, p, n);
        vN(*out) += nh + n;

        return BLOB(out);
}

// _http.ws-close-payload(code: Int, reason: String = '') -> String
TY_BUILTIN(http_ws_close_payload)
{
        isize n = min(sN(reason), 123);
        u8 *out = (u8 *)value_string_alloc(ty, 2 + n);

        out[0] = (code >> 8) & 0xFF;
        out[1] = code & 0xFF;
        memcpy(out + 2, ss(reason), n);

        return STRING((char *)out, 2 + n);
}

// _http.ws-next(b: Blob, at: Int, end: Int, masked: Bool, rsv1: Bool, limit: Int, out: Array[Int]) -> String | Blob | Int
TY_BUILTIN(http_ws_next)
{
        isize no;

        span(ty, _name__, b, at, end);

        Value *o = ints(ty, _name__, "out", out, WS_OUT_N, &no);
        u8 const *s = vv(*b) + at;
        isize avail = end - at;

        o[WS_OUT_TOTAL] = INTEGER(0);

        if (avail < 2) {
                return INTEGER(0);
        }

        int  op  = s[0] & 0x0F;
        bool fin = (s[0] & 0x80) != 0;
        bool r1  = (s[0] & 0x40) != 0;

        if (
                ((s[0] & 0x30) != 0)
             || (r1 && !(rsv1 && (op == WS_OP_TEXT || op == WS_OP_BINARY)))
        ) {
                return INTEGER(WS_RESERVED);
        }

        if (((s[1] & 0x80) != 0) != masked) {
                return INTEGER(WS_MASK);
        }

        u64 len = s[1] & 0x7F;
        isize hdr = 2;

        if (len == 126) {
                if (avail < 4) {
                        return INTEGER(0);
                }
                len = (s[2] << 8) | s[3];
                hdr = 4;
        } else if (len == 127) {
                if (avail < 10) {
                        return INTEGER(0);
                }
                if ((s[2] & 0x80) != 0) {
                        return INTEGER(WS_LENGTH);
                }
                len = 0;
                for (int i = 0; i < 8; ++i) {
                        len = (len << 8) | s[2 + i];
                }
                hdr = 10;
        }

        o[WS_OUT_OP]   = INTEGER(op);
        o[WS_OUT_FIN]  = INTEGER(fin);
        o[WS_OUT_RSV1] = INTEGER(r1);
        o[WS_OUT_LEN]  = INTEGER(len);

        if (op >= 0x8 && (len > 125 || !fin)) {
                return INTEGER(WS_CONTROL);
        }

        if (len > (u64)limit) {
                return INTEGER(WS_TOO_BIG);
        }

        isize key   = masked ? hdr : -1;
        isize total = hdr + 4 * masked + len;

        o[WS_OUT_TOTAL] = INTEGER(total);

        if (avail < total) {
                return INTEGER(0);
        }

        u8 *dst;
        Value result;

        if (op == WS_OP_BINARY) {
                Blob *blob = value_blob_new(ty);
                result = BLOB(blob);
                gP(&result);
                vvR(*blob, max(len, 1));
                gX();
                vN(*blob) = len;
                dst = vv(*blob);
        } else {
                dst = (u8 *)value_string_alloc(ty, len);
                result = STRING((char *)dst, len);
        }

        s = vv(*b) + at;

        if (masked) {
                ws_xor(dst, s + key + 4, len, s + key);
        } else {
                memcpy(dst, s + hdr, len);
        }

        return result;
}

#undef LEQ
#undef IS

typedef struct {
        nghttp2_session *s;
        Ty              *ty;
        Value const     *h;
        Value            exc;
        bool             failed;
        bool             dead;
} H2;

enum {
        CB_BEGIN,
        CB_HEADER,
        CB_FRAME,
        CB_CHUNK,
        CB_CLOSE,
        CB_READ,
        CB_N
};

static char const *CbNames[CB_N] = {
        [CB_BEGIN]  = "cbBegin",
        [CB_HEADER] = "cbHeader",
        [CB_FRAME]  = "cbFrame",
        [CB_CHUNK]  = "cbChunk",
        [CB_CLOSE]  = "cbClose",
        [CB_READ]   = "cbRead"
};

static int CbIds[CB_N];

static nghttp2_session_callbacks *Callbacks;

static Value
dispatch(H2 *h2, int cb, int argc, Value *ok)
{
        Ty *ty = h2->ty;
        Value r = NIL;

        if (h2->failed || h2->h == NULL) {
                *ok = BOOLEAN(false);
                while (argc --> 0) {
                        vmX();
                }
                return NIL;
        }

        if (TY_CATCH_ERROR()) {
                h2->exc    = TY_CATCH();
                h2->failed = true;
                *ok        = BOOLEAN(false);
                return NIL;
        }

        Value *f = (h2->h->type == VALUE_OBJECT)
                 ? class_lookup_method_i(ty, h2->h->class, CbIds[cb])
                 : NULL;

        if (f == NULL) {
                zP("http: HTTP/2 handler %s has no method %s", VSC(h2->h), CbNames[cb]);
        }

        r = vm_call_method(ty, h2->h, f, argc);

        TY_CATCH_END();

        *ok = BOOLEAN(true);

        return r;
}

inline static int
rc(H2 *h2, Value r, Value ok)
{
        return !ok.boolean          ? NGHTTP2_ERR_CALLBACK_FAILURE
             : (r.type == VALUE_INTEGER) ? (int)r.z
             :                        0;
}

/* ========================================================================= */
#define TyOf(user) Ty *ty = ((H2 *)(user))->ty
#define CALL(cb, n) dispatch((H2 *)user, (cb), (n), &ok)
/* ------------------------------------------------------------------------- */
static int
on_begin(nghttp2_session *s, nghttp2_frame const *frame, void *user)
{
        TyOf(user);
        Value ok;

        if (frame->hd.type != NGHTTP2_HEADERS) {
                return 0;
        }

        vmP(&INTEGER(frame->hd.stream_id));
        vmP(&INTEGER(frame->headers.cat));

        return rc(user, CALL(CB_BEGIN, 2), ok);
}

static int
on_header(
        nghttp2_session *s,
        nghttp2_frame const *frame,
        u8 const *name,
        size_t namelen,
        u8 const *value,
        size_t valuelen,
        u8 flags,
        void *user
)
{
        TyOf(user);
        Value ok;

        vmP(&INTEGER(frame->hd.stream_id));
        Value k = vSs((char const *)name, namelen);
        vmP(&k);
        Value v = vSs((char const *)value, valuelen);
        vmP(&v);

        return rc(user, CALL(CB_HEADER, 3), ok);
}

static int
on_frame(nghttp2_session *s, nghttp2_frame const *frame, void *user)
{
        TyOf(user);
        Value ok;

        i64 aux = (frame->hd.type == NGHTTP2_GOAWAY)     ? frame->goaway.last_stream_id
                : (frame->hd.type == NGHTTP2_RST_STREAM) ? frame->rst_stream.error_code
                :                                          0;

        vmP(&INTEGER(frame->hd.stream_id));
        vmP(&INTEGER(frame->hd.type));
        vmP(&INTEGER(frame->hd.flags));
        vmP(&INTEGER(aux));

        return rc(user, CALL(CB_FRAME, 4), ok);
}

static int
on_chunk(nghttp2_session *s, u8 flags, i32 id, u8 const *data, size_t len, void *user)
{
        TyOf(user);
        Value ok;

        vmP(&INTEGER(id));
        vmP(&PTR((void *)data));
        vmP(&INTEGER(len));

        return rc(user, CALL(CB_CHUNK, 3), ok);
}

static int
on_close(nghttp2_session *s, i32 id, u32 code, void *user)
{
        TyOf(user);
        Value ok;

        vmP(&INTEGER(id));
        vmP(&INTEGER(code));

        return rc(user, CALL(CB_CLOSE, 2), ok);
}

static nghttp2_ssize
on_read(
        nghttp2_session *s,
        i32 id,
        u8 *buf,
        size_t length,
        u32 *flags,
        nghttp2_data_source *source,
        void *user
)
{
        TyOf(user);
        Value ok;

        vmP(&INTEGER(id));
        vmP(&INTEGER(length));

        Value r = CALL(CB_READ, 2);

        if (!ok.boolean) {
                return NGHTTP2_ERR_CALLBACK_FAILURE;
        }

        if (r.type == VALUE_INTEGER) {
                return r.z;
        }

        if (
                (r.type != VALUE_TUPLE)
             || (r.count != 4)
             || (r.items[0].type != VALUE_BLOB)
             || (r.items[1].type != VALUE_INTEGER)
             || (r.items[2].type != VALUE_INTEGER)
        ) {
                return NGHTTP2_ERR_CALLBACK_FAILURE;
        }

        Blob const *b = r.items[0].blob;
        i64 off = r.items[1].z;
        i64 n   = r.items[2].z;

        if (off < 0 || n < 0 || n > length || off + n > vN(*b)) {
                return NGHTTP2_ERR_CALLBACK_FAILURE;
        }

        memcpy(buf, vv(*b) + off, n);

        if (value_truthy(ty, &r.items[3])) {
                *flags |= NGHTTP2_DATA_FLAG_EOF;
        }

        return n;
}
/* ------------------------------------------------------------------------- */
#undef CALL
#undef TyOf
/* ========================================================================= */

static void
h2_init(void)
{
        nghttp2_session_callbacks_new(&Callbacks);
        nghttp2_session_callbacks_set_on_begin_headers_callback(Callbacks, on_begin);
        nghttp2_session_callbacks_set_on_header_callback(Callbacks, on_header);
        nghttp2_session_callbacks_set_on_frame_recv_callback(Callbacks, on_frame);
        nghttp2_session_callbacks_set_on_data_chunk_recv_callback(Callbacks, on_chunk);
        nghttp2_session_callbacks_set_on_stream_close_callback(Callbacks, on_close);

        for (int i = 0; i < CB_N; ++i) {
                CbIds[i] = M_ID(CbNames[i]);
        }
}

static H2 *
h2_arg(Ty *ty, char const *ctx, Value v)
{
        if (v.type != VALUE_PTR || v.ptr == NULL) {
                TyBuiltinBadArg(ty, ctx, "s", "Ptr", &v);
        }

        H2 *h2 = v.ptr;

        if (h2->dead) {
                zP("%s: the HTTP/2 session was deleted", ctx);
        }

        return h2;
}

inline static void
h2_enter(Ty *ty, H2 *h2, Value const *h, H2 *saved)
{
        *saved     = *h2;
        h2->ty     = ty;
        h2->h      = h;
        h2->failed = false;
}

static void
h2_free(H2 *h2)
{
        nghttp2_session_del(h2->s);
        xmF(h2);
}

static void
h2_leave(Ty *ty, H2 *h2, H2 const *saved)
{
        bool  failed = h2->failed;
        Value exc    = h2->exc;

        h2->ty     = saved->ty;
        h2->h      = saved->h;
        h2->exc    = saved->exc;
        h2->failed = saved->failed;

        if (h2->dead && h2->h == NULL) {
                h2_free(h2);
        }

        if (failed) {
                vmE(&exc);
        }
}

static void
nv_pack(Ty *ty, char const *ctx, Value headers, nghttp2_nv **nva, isize *n)
{
        if (headers.type != VALUE_ARRAY) {
                TyBuiltinBadArg(ty, ctx, "headers", "Array[(String, String)]", &headers);
        }

        *n   = vN(*headers.array);
        *nva = smA(max(*n, 1) * sizeof (nghttp2_nv));

        for (isize i = 0; i < *n; ++i) {
                Value const *p = v_(*headers.array, i);
                if (
                        (p->type != VALUE_TUPLE)
                     || (p->count != 2)
                     || (p->items[0].type != VALUE_STRING)
                     || (p->items[1].type != VALUE_STRING)
                ) {
                        zP("%s: bad header: %s", ctx, VSC(p));
                }
                (*nva)[i] = (nghttp2_nv) {
                        .name     = (u8 *)ss(p->items[0]),
                        .value    = (u8 *)ss(p->items[1]),
                        .namelen  = sN(p->items[0]),
                        .valuelen = sN(p->items[1]),
                        .flags    = NGHTTP2_NV_FLAG_NONE
                };
        }
}

// _http.h2-new(server: Bool, maxSettings: Int = 64, noAutoWindow: Bool = false, peerMaxStreams: Int = 0) -> Ptr
TY_BUILTIN(http_h2_new)
{
        static pthread_once_t once = PTHREAD_ONCE_INIT;
        nghttp2_option *opt;

        pthread_once(&once, h2_init);

        H2 *h2 = xmA(sizeof *h2);
        *h2 = (H2) { .exc = NIL };

        nghttp2_option_new(&opt);
        nghttp2_option_set_max_settings(opt, maxSettings);
        nghttp2_option_set_no_auto_window_update(opt, noAutoWindow);
        if (peerMaxStreams > 0) {
                nghttp2_option_set_peer_max_concurrent_streams(opt, peerMaxStreams);
        }

        int err = server ? nghttp2_session_server_new2(&h2->s, Callbacks, h2, opt)
                :          nghttp2_session_client_new2(&h2->s, Callbacks, h2, opt);

        nghttp2_option_del(opt);

        if (err != 0) {
                xmF(h2);
                bP("%s", nghttp2_strerror(err));
        }

        return PTR(h2);
}

// _http.h2-del(s: Ptr) -> nil
TY_BUILTIN(http_h2_del)
{
        H2 *h2 = h2_arg(ty, _name__, s);

        h2->dead = true;

        if (h2->h == NULL) {
                h2_free(h2);
        }

        return NIL;
}

// _http.h2-recv(s: Ptr, h: Any, buf: Blob, off: Int, n: Int) -> Int
TY_BUILTIN(http_h2_recv)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        H2 saved;

        span(ty, _name__, buf, off, off + n);

        h2_enter(ty, h2, &h, &saved);
        nghttp2_ssize r = nghttp2_session_mem_recv2(h2->s, vv(*buf) + off, n);
        h2_leave(ty, h2, &saved);

        return INTEGER(r);
}

// _http.h2-send(s: Ptr, h: Any, out: Blob, max: Int) -> Int
TY_BUILTIN(http_h2_send)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        H2 saved;
        isize total = 0;
        nghttp2_ssize r = 0;

        h2_enter(ty, h2, &h, &saved);

        while (total < max) {
                u8 const *data;
                r = nghttp2_session_mem_send2(h2->s, &data);
                if (r <= 0) {
                        break;
                }
                vvPn(*out, data, r);
                total += r;
        }

        h2_leave(ty, h2, &saved);

        return INTEGER((r < 0) ? r : total);
}

// _http.h2-settings(s: Ptr, iv: Array[Int]) -> Int
TY_BUILTIN(http_h2_settings)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        isize n;

        Value const *xs = ints(ty, _name__, "iv", iv, 0, &n);
        nghttp2_settings_entry es[16];

        if (n / 2 > countof(es)) {
                bP("too many settings");
        }

        for (isize i = 0; i + 1 < n; i += 2) {
                es[i / 2] = (nghttp2_settings_entry) {
                        .settings_id = xs[i].z,
                        .value       = xs[i + 1].z
                };
        }

        return INTEGER(nghttp2_submit_settings(h2->s, NGHTTP2_FLAG_NONE, es, n / 2));
}

// _http.h2-response(s: Ptr, id: Int, headers: Array[(String, String)], body: Bool) -> Int
TY_BUILTIN(http_h2_response)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        nghttp2_nv *nva;
        isize n;
        nghttp2_data_provider2 prd = { .read_callback = on_read };

        SCRATCH_SAVE();
        nv_pack(ty, _name__, headers, &nva, &n);
        int r = nghttp2_submit_response2(h2->s, id, nva, n, body ? &prd : NULL);
        SCRATCH_RESTORE();

        return INTEGER(r);
}

// _http.h2-request(s: Ptr, headers: Array[(String, String)], body: Bool) -> Int
TY_BUILTIN(http_h2_request)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        nghttp2_nv *nva;
        isize n;
        nghttp2_data_provider2 prd = { .read_callback = on_read };

        SCRATCH_SAVE();
        nv_pack(ty, _name__, headers, &nva, &n);
        i32 r = nghttp2_submit_request2(h2->s, NULL, nva, n, body ? &prd : NULL, NULL);
        SCRATCH_RESTORE();

        return INTEGER(r);
}

// _http.h2-rst(s: Ptr, id: Int, code: Int) -> Int
TY_BUILTIN(http_h2_rst)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return INTEGER(nghttp2_submit_rst_stream(h2->s, NGHTTP2_FLAG_NONE, id, code));
}

// _http.h2-goaway(s: Ptr, code: Int) -> Int
TY_BUILTIN(http_h2_goaway)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        i32 last = nghttp2_session_get_last_proc_stream_id(h2->s);
        return INTEGER(nghttp2_submit_goaway(h2->s, NGHTTP2_FLAG_NONE, last, code, NULL, 0));
}

// _http.h2-resume(s: Ptr, id: Int) -> Int
TY_BUILTIN(http_h2_resume)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return INTEGER(nghttp2_session_resume_data(h2->s, id));
}

// _http.h2-consume(s: Ptr, id: Int, n: Int) -> Int
TY_BUILTIN(http_h2_consume)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return INTEGER(
                (id == 0) ? nghttp2_session_consume_connection(h2->s, n)
                :           nghttp2_session_consume(h2->s, id, n)
        );
}

// _http.h2-want-read(s: Ptr) -> Bool
TY_BUILTIN(http_h2_want_read)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return BOOLEAN(nghttp2_session_want_read(h2->s));
}

// _http.h2-want-write(s: Ptr) -> Bool
TY_BUILTIN(http_h2_want_write)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return BOOLEAN(nghttp2_session_want_write(h2->s));
}

// _http.h2-remote-setting(s: Ptr, id: Int) -> Int
TY_BUILTIN(http_h2_remote_setting)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return INTEGER(nghttp2_session_get_remote_settings(h2->s, id));
}

// _http.h2-local-window(s: Ptr, size: Int) -> Int
TY_BUILTIN(http_h2_local_window)
{
        H2 *h2 = h2_arg(ty, _name__, s);
        return INTEGER(nghttp2_session_set_local_window_size(h2->s, NGHTTP2_FLAG_NONE, 0, size));
}

// _http.h2-strerror(code: Int) -> String
TY_BUILTIN(http_h2_strerror)
{
        return vSsz(nghttp2_strerror(code));
}

// _http.h2-error-name(code: Int) -> String
TY_BUILTIN(http_h2_error_name)
{
        return vSsz(nghttp2_http2_strerror(code));
}

/* vim: set sts=8 sw=8 expandtab: */
