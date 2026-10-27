#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <sha1.h>
#include <utf8proc.h>

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"
#include "class.h"
#include "blob.h"

enum {
        C_TCHAR = 1,
        C_VCHAR = 2,
        C_FIELD = 4,
        C_DIGIT = 8,
        C_HEX   = 16,
        C_UPPER = 32
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

#define IS(c, k) ((CharClass[(u8)(c)] & C_##k) != 0)

inline static u8
lower(u8 c)
{
        return c | (CharClass[c] & C_UPPER);
}

static struct {
        int  request;
        int  headers;
        int  response;
        int  event;
        int  url;
        u16  ur[8];
        u16  ev[4];
        u16  rq[10];
        u16  hd;
        u16  rs[4];
        Value v10;
        Value v11;
        Value v20;
        bool ready;
} K;

enum {
        RQ_METHOD,
        RQ_TARGET,
        RQ_URL,
        RQ_QUERY,
        RQ_HEADERS,
        RQ_BODY,
        RQ_VERSION,
        RQ_SCHEME,
        RQ_REMOTE,
        RQ_ID
};

enum {
        RS_STATUS,
        RS_REASON,
        RS_VERSION,
        RS_HEADERS
};

static char const *const Reasons[] = {
        [100] = "Continue",
        [101] = "Switching Protocols",
        [102] = "Processing",
        [103] = "Early Hints",
        [200] = "OK",
        [201] = "Created",
        [202] = "Accepted",
        [203] = "Non-Authoritative Information",
        [204] = "No Content",
        [205] = "Reset Content",
        [206] = "Partial Content",
        [207] = "Multi-Status",
        [208] = "Already Reported",
        [226] = "IM Used",
        [300] = "Multiple Choices",
        [301] = "Moved Permanently",
        [302] = "Found",
        [303] = "See Other",
        [304] = "Not Modified",
        [305] = "Use Proxy",
        [307] = "Temporary Redirect",
        [308] = "Permanent Redirect",
        [400] = "Bad Request",
        [401] = "Unauthorized",
        [402] = "Payment Required",
        [403] = "Forbidden",
        [404] = "Not Found",
        [405] = "Method Not Allowed",
        [406] = "Not Acceptable",
        [407] = "Proxy Authentication Required",
        [408] = "Request Timeout",
        [409] = "Conflict",
        [410] = "Gone",
        [411] = "Length Required",
        [412] = "Precondition Failed",
        [413] = "Content Too Large",
        [414] = "URI Too Long",
        [415] = "Unsupported Media Type",
        [416] = "Range Not Satisfiable",
        [417] = "Expectation Failed",
        [418] = "I'm a teapot",
        [421] = "Misdirected Request",
        [422] = "Unprocessable Content",
        [423] = "Locked",
        [424] = "Failed Dependency",
        [425] = "Too Early",
        [426] = "Upgrade Required",
        [428] = "Precondition Required",
        [429] = "Too Many Requests",
        [431] = "Request Header Fields Too Large",
        [451] = "Unavailable For Legal Reasons",
        [500] = "Internal Server Error",
        [501] = "Not Implemented",
        [502] = "Bad Gateway",
        [503] = "Service Unavailable",
        [504] = "Gateway Timeout",
        [505] = "HTTP Version Not Supported",
        [506] = "Variant Also Negotiates",
        [507] = "Insufficient Storage",
        [508] = "Loop Detected",
        [510] = "Not Extended",
        [511] = "Network Authentication Required"
};

char const *
MsgReason(int status)
{
        return (status >= 0 && status < countof(Reasons) && Reasons[status] != NULL) ? Reasons[status] : "Unknown";
}

usize
MsgStatusLine(char *out, int status)
{
        return ty_snprintf(out, 64, "HTTP/1.1 %d %s\r\n", status, MsgReason(status));
}

bool
MsgIeq(void const *p, usize n, char const *b)
{
        u8 const *a = p;

        for (usize i = 0; i < n; ++i) {
                if (b[i] == '\0' || lower(a[i]) != (u8)b[i]) {
                        return false;
                }
        }

        return b[n] == '\0';
}

bool
MsgReserved(void const *p, usize n)
{
        switch (n) {
        case 4:  return MsgIeq(p, n, "date");
        case 10: return MsgIeq(p, n, "connection") || MsgIeq(p, n, "keep-alive");
        case 12: return MsgIeq(p, n, "content-type");
        case 14: return MsgIeq(p, n, "content-length");
        case 17: return MsgIeq(p, n, "transfer-encoding");
        }

        return false;
}

static void
put_name(Buf *b, void const *name, usize n)
{
        u8 const *p = name;
        char *dst   = BufRoom(b, n);
        bool up = true;

        for (usize i = 0; i < n; ++i) {
                u8 c = p[i];
                dst[i] = (up && c >= 'a' && c <= 'z') ? (c - 32) : c;
                up = (c == '-');
        }

        b->count += n;
}

static bool
safe_value(void const *s, usize n)
{
        char const *p = s;

        for (usize i = 0; i < n; ++i) {
                if (p[i] == '\r' || p[i] == '\n' || p[i] == '\0') {
                        return false;
                }
        }

        return true;
}

static void
put_field(Ty *ty, Buf *b, Value const *k, Value const *v, bool lowercase)
{
        Value s = (v->type == VALUE_STRING) ? *v : value_vshow(ty, v, 0);

        if (!safe_value(ss(s), sN(s))) {
                zP("http: invalid character in header %.*s", (int)sN(*k), ss(*k));
        }

        if (lowercase) {
                BufStr(b, *k);
        } else {
                put_name(b, ss(*k), sN(*k));
        }

        BufLit(b, ": ");
        BufStr(b, s);
        BufLit(b, "\r\n");
}

void
MsgHeaders(Ty *ty, Buf *out, Value headers, bool lowercase, bool server)
{
        if (headers.type != VALUE_DICT) {
                return;
        }

        dfor(headers.dict, {
                if (key->type != VALUE_STRING || (server && MsgReserved(ss(*key), sN(*key)))) {
                        continue;
                }
                if (val->type == VALUE_ARRAY) {
                        vfor(*val->array, put_field(ty, out, key, it, lowercase));
                } else if (val->type != VALUE_NIL) {
                        put_field(ty, out, key, val, lowercase);
                }
        });
}

static u16
field_slot(Ty *ty, Class *c, char const *name)
{
        i32 id = M_ID(name);

        for (u32 i = 0; i < vN(c->fields.ids); ++i) {
                if (v__(c->fields.ids, i) == id) {
                        return i;
                }
        }

        zP("http: class %s has no field %s", c->name, name);
}

void
MsgSetup(Ty *ty, Value request, Value headers, Value v10, Value v11, Value v20)
{
        static char const *const rq[] = { "method", "target", "url", "query", "headers", "body", "version", "scheme", "remote", "id" };

        class_ctor(ty, request.class);
        class_ctor(ty, headers.class);

        Class *crq = class_get(ty, request.class);
        Class *chd = class_get(ty, headers.class);

        for (int i = 0; i < countof(rq); ++i) {
                K.rq[i] = field_slot(ty, crq, rq[i]);
        }

        K.hd      = field_slot(ty, chd, "table");
        K.request = request.class;
        K.headers = headers.class;
        K.v10     = v10;
        K.v11     = v11;
        K.v20     = v20;

        gc_immortalize(ty, &v10);
        gc_immortalize(ty, &v11);
        gc_immortalize(ty, &v20);

        K.ready = true;
}

void
MsgSetupClient(Ty *ty, Value response, Value event)
{
        static char const *const rs[] = { "statusCode", "reason", "httpVersion", "headers" };
        static char const *const ev[] = { "event", "data", "id", "retry" };

        class_ctor(ty, response.class);
        class_ctor(ty, event.class);

        Class *crs = class_get(ty, response.class);
        Class *cev = class_get(ty, event.class);

        for (int i = 0; i < countof(rs); ++i) {
                K.rs[i] = field_slot(ty, crs, rs[i]);
        }

        for (int i = 0; i < countof(ev); ++i) {
                K.ev[i] = field_slot(ty, cev, ev[i]);
        }

        K.response = response.class;
        K.event    = event.class;
}

Value
MsgEvent(Ty *ty, Value event, Value data, Value id, Value retry)
{
        TyObject *o = class_new_instance(ty, K.event);

        o->slots[K.ev[0]] = event;
        o->slots[K.ev[1]] = data;
        o->slots[K.ev[2]] = id;
        o->slots[K.ev[3]] = retry;

        return OBJECT(o, K.event);
}

Value
MsgVersion(int v)
{
        return (v == 10) ? K.v10
             : (v == 20) ? K.v20
             :             K.v11;
}

Value
MsgHeadersObject(Ty *ty, Dict *d)
{
        TyObject *o = class_new_instance(ty, K.headers);
        o->slots[K.hd] = DICT(d);
        return OBJECT(o, K.headers);
}

Value
MsgHeadString(Loop *L, Xch *x, char const *p, usize n)
{
        Ty *ty   = L->ty;
        Conn *c  = x->c;
        u32 peer = (c != NULL) ? c->npeer : 0;
        usize total = n + peer + sizeof x->rid;
        char *s  = value_string_alloc(ty, total);

        memcpy(s, p, n);

        for (usize i = 0; i < vN(x->hs); i += 2) {
                Span k = v__(x->hs, i);
                for (u32 j = 0; j < k.len; ++j) {
                        s[k.off + j] = lower(s[k.off + j]);
                }
        }

        if (peer > 0) {
                memcpy(s + n, c->peer, peer);
        }

        return STRING(s, total);
}

static bool
valid_rid(char const *p, usize n)
{
        if (n == 0 || n > 128) {
                return false;
        }

        for (usize i = 0; i < n; ++i) {
                u8 c = p[i];
                if (!(IS(c, DIGIT) || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '.' || c == '_' || c == ':' || c == '-')) {
                        return false;
                }
        }

        return true;
}

inline static Value
view(Value head, Span s)
{
        return STRING_VIEW(head, s.off, s.len);
}

void
MsgFields(Ty *ty, Dict *d, Value head, Span const *hs, usize n)
{
        for (usize i = 0; i < n; ++i) {
                Value k = view(head, hs[2 * i]);
                Value v = view(head, hs[2 * i + 1]);
                Value *slot = dict_put_key_if_not_exists(ty, d, k);
                if (slot->type == VALUE_NIL || slot->type == VALUE_ZERO || slot->type == VALUE_NONE) {
                        *slot = v;
                } else if (slot->type == VALUE_STRING) {
                        Array *both = vAn(2);
                        uvP(*both, *slot);
                        uvP(*both, v);
                        *slot = ARRAY(both);
                } else {
                        vAp(slot->array, v);
                }
        }
}

Value
MsgRequest(Loop *L, Xch *x, Value head, Value body)
{
        Ty *ty   = L->ty;
        Conn *c  = x->c;
        Group *g = L->g;
        usize nh = vN(x->hs) / 2;

        GC_STOP();

        Dict *d = dict_new_sized(ty, nh + 1);
        Span rid = {0};

        MsgFields(ty, d, head, vv(x->hs), nh);

        Value const *xr = dict_get_member(ty, d, "x-request-id");
        if (xr != NULL && xr->type == VALUE_STRING) {
                rid = (Span) { .off = ss(*xr) - ss(head), .len = sN(*xr) };
        }

        if (x->authority.len > 0) {
                Value *slot = dict_put_member_if_not_exists(ty, d, "host");
                if (slot->type == VALUE_NIL || slot->type == VALUE_ZERO || slot->type == VALUE_NONE) {
                        *slot = view(head, x->authority);
                }
        }

        u32 peer = (c != NULL) ? c->npeer : 0;
        char *s  = (char *)ss(head);
        usize at = sN(head) - sizeof x->rid;

        if (g->cfg.trust_rid && valid_rid(s + rid.off, rid.len)) {
                memcpy(x->rid, s + rid.off, rid.len);
                x->nrid = rid.len;
        } else {
                L->seq += 1;
                x->nrid = ty_snprintf(x->rid, sizeof x->rid, "%s-%x-%"PRIx64, g->rid, L->index, L->seq);
                memcpy(s + at, x->rid, x->nrid);
                rid = (Span) { .off = at, .len = x->nrid };
        }

        Value hobj = MsgHeadersObject(ty, d);

        TyObject *o = class_new_instance(ty, K.request);
        Value req   = OBJECT(o, K.request);

        Span t = x->target;
        char const *q = memchr(s + t.off, '?', t.len);

        o->slots[K.rq[RQ_METHOD]]  = view(head, x->method);
        o->slots[K.rq[RQ_TARGET]]  = view(head, t);
        o->slots[K.rq[RQ_HEADERS]] = hobj;
        o->slots[K.rq[RQ_BODY]]    = body;
        o->slots[K.rq[RQ_VERSION]] = MsgVersion(x->v);
        o->slots[K.rq[RQ_ID]]      = view(head, rid);
        o->slots[K.rq[RQ_REMOTE]]  = (peer > 0) ? STRING_VIEW(head, sN(head) - sizeof x->rid - peer, peer) : NIL;

        if (q == NULL) {
                o->slots[K.rq[RQ_URL]]   = view(head, t);
                o->slots[K.rq[RQ_QUERY]] = NIL;
        } else {
                u32 n = q - (s + t.off);
                o->slots[K.rq[RQ_URL]]   = STRING_VIEW(head, t.off, n);
                o->slots[K.rq[RQ_QUERY]] = STRING_VIEW(head, t.off + n + 1, t.len - n - 1);
        }

        if (x->scheme.len > 0) {
                o->slots[K.rq[RQ_SCHEME]] = view(head, x->scheme);
        } else {
                o->slots[K.rq[RQ_SCHEME]] = (c != NULL && c->tls != NULL) ? xSz("https") : xSz("http");
        }

        GC_RESUME();

        return req;
}

Value
MsgClientResponse(Ty *ty, int status, Value reason, int version, Dict *headers)
{
        GC_STOP();

        Value h     = MsgHeadersObject(ty, headers);
        TyObject *o = class_new_instance(ty, K.response);

        o->slots[K.rs[RS_STATUS]]  = INTEGER(status);
        o->slots[K.rs[RS_REASON]]  = reason;
        o->slots[K.rs[RS_VERSION]] = (version == 20) ? xSz("HTTP/2")
                                   : (version == 10) ? xSz("HTTP/1.0")
                                   :                   xSz("HTTP/1.1");
        o->slots[K.rs[RS_HEADERS]] = h;

        GC_RESUME();

        return OBJECT(o, K.response);
}

void
Sha1(void const *p, usize n, u8 out[20])
{
        SHA1_CTX ctx;

        SHA1Init(&ctx);
        SHA1Update(&ctx, p, n);
        SHA1Final(out, &ctx);
}

usize
Base64(u8 const *p, usize n, char *out)
{
        static char const tab[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
        usize j = 0;

        for (usize i = 0; i < n; i += 3) {
                u32 v = (u32)p[i] << 16;
                if (i + 1 < n) { v |= (u32)p[i + 1] << 8; }
                if (i + 2 < n) { v |= p[i + 2];           }
                out[j++] = tab[(v >> 18) & 63];
                out[j++] = tab[(v >> 12) & 63];
                out[j++] = (i + 1 < n) ? tab[(v >> 6) & 63] : '=';
                out[j++] = (i + 2 < n) ? tab[v & 63]        : '=';
        }

        return j;
}

inline static int
hexval(u8 c)
{
        return IS(c, DIGIT) ? (c - '0') : ((c | 0x20) - 'a' + 10);
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

static void
pct_once(void)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, pct_init);
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
pct_encode_into(Buf *out, u8 const *p, isize n, int kind)
{
        static char const hex[] = "0123456789ABCDEF";

        for (isize i = 0; i < n; ++i) {
                if (pct_escape(p, i, n, kind)) {
                        char e[3] = { '%', hex[p[i] >> 4], hex[p[i] & 15] };
                        BufPut(out, e, 3);
                } else {
                        BufPutc(out, p[i]);
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
        if (
                (memchr(p, '%', n) == NULL)
             && !(plus && memchr(p, '+', n) != NULL)
             && !(form && memchr(p, '\r', n) != NULL)
        ) {
                return vSs(p, n);
        }

        u8 *buf = xmA(max(n, 1));
        isize j = pct_decode_into(buf, p, n, plus, form);
        Value result = LossyString(ty, buf, j);

        xmF(buf);

        return result;
}

static Value
buf_string(Ty *ty, Buf *b)
{
        Value s = vSs(BufHead(b), BufLen(b));
        BufFree(b);
        return s;
}

// _http.setup-server(request: Class, headers: Class, v10: _, v11: _, v20: _) -> nil
TY_BUILTIN(http_setup_server)
{
        if (request.type != VALUE_CLASS || headers.type != VALUE_CLASS) {
                bP("expected classes");
        }

        MsgSetup(ty, request, headers, v10, v11, v20);

        return NIL;
}

// _http.setup-client(response: Class, event: Class) -> nil
TY_BUILTIN(http_setup_client)
{
        if (response.type != VALUE_CLASS || event.type != VALUE_CLASS) {
                bP("expected classes");
        }

        MsgSetupClient(ty, response, event);

        return NIL;
}

// _http.reason(code: Int) -> String
TY_BUILTIN(http_reason)
{
        return xSz(MsgReason(code));
}

// _http.header(table: Dict[String, _], name: String) -> String | nil
TY_BUILTIN(http_header)
{
        char tmp[128];
        usize n = sN(name);

        if (table.type != VALUE_DICT) {
                TyBuiltinBadArg(ty, _name__, "table", "Dict", &table);
        }

        Value key = name;

        if (n <= sizeof tmp) {
                bool changed = false;
                for (usize i = 0; i < n; ++i) {
                        tmp[i] = lower(ss(name)[i]);
                        changed |= (tmp[i] != ss(name)[i]);
                }
                if (changed) {
                        key = xSs(tmp, n);
                }
        }

        Value *v = dict_get_value(ty, table.dict, &key);

        if (v == NULL || v->type == VALUE_NIL) {
                return NIL;
        }

        if (v->type != VALUE_ARRAY) {
                return *v;
        }

        Buf out = {0};

        vfor(*v->array, {
                if (BufLen(&out) > 0) {
                        BufLit(&out, ", ");
                }
                if (it->type == VALUE_STRING) {
                        BufStr(&out, *it);
                }
        });

        return buf_string(ty, &out);
}

// _http.copy-headers[h](headers: h) -> h
TY_BUILTIN(http_copy_headers)
{
        if (headers.type != VALUE_OBJECT || headers.class != K.headers) {
                bP("expected Headers");
        }

        GC_STOP();

        Dict *d = DictClone(ty, headers.object->slots[K.hd].dict);

        dfor(d, {
                if (val->type == VALUE_ARRAY) {
                        *val = ARRAY(ArrayClone(ty, val->array));
                }
        });

        Value h = MsgHeadersObject(ty, d);

        GC_RESUME();

        return h;
}

// _http.canonical(name: String) -> String
TY_BUILTIN(http_canonical)
{
        Buf out = {0};
        put_name(&out, ss(name), sN(name));
        return buf_string(ty, &out);
}

// _http.lower(s: String) -> String
TY_BUILTIN(http_lower)
{
        usize n = sN(s);
        usize i = 0;

        while (i < n && lower(ss(s)[i]) == (u8)ss(s)[i]) {
                i += 1;
        }

        if (i == n) {
                return s;
        }

        char *out = value_string_alloc(ty, n);

        for (usize j = 0; j < n; ++j) {
                out[j] = lower(ss(s)[j]);
        }

        return STRING(out, n);
}

// _http.valid-header?(s: String) -> Bool
TY_BUILTIN(http_valid_header)
{
        return BOOLEAN(safe_value(ss(s), sN(s)));
}

static Value
pct_part(Ty *ty, Value s, isize off, isize n, int kind)
{
        u8 const *p = (u8 const *)ss(s) + off;
        isize i = 0;

        while (i < n && !pct_escape(p, i, n, kind)) {
                i += 1;
        }

        if (i == n) {
                return STRING_VIEW(s, off, n);
        }

        Buf out = {0};
        BufPut(&out, p, i);
        pct_encode_into(&out, p + i, n - i, kind);

        return buf_string(ty, &out);
}

// _http.percent-encode(s: String, kind: Int = 0) -> String
TY_BUILTIN(http_percent_encode)
{
        pct_once();

        if (kind < 0 || kind >= PCT_KINDS) {
                bP("bad kind: %"PRIi64, kind);
        }

        return pct_part(ty, s, 0, sN(s), kind);
}

static Value
lower_part(Ty *ty, Value s, isize off, isize n)
{
        u8 const *p = (u8 const *)ss(s) + off;
        isize i = 0;

        while (i < n && !IS(p[i], UPPER)) {
                i += 1;
        }

        if (i == n) {
                return STRING_VIEW(s, off, n);
        }

        char *out = value_string_alloc(ty, n);

        for (isize j = 0; j < n; ++j) {
                out[j] = lower(p[j]);
        }

        return STRING(out, n);
}

inline static char
puny_digit(u32 d)
{
        return (d < 26) ? 'a' + d : '0' + d - 26;
}

static u32
puny_adapt(u32 delta, u32 points, bool first)
{
        u32 k = 0;

        delta  = first ? delta / 700 : delta / 2;
        delta += delta / points;

        while (delta > 455) {
                delta /= 35;
                k     += 36;
        }

        return k + (36 * delta) / (delta + 38);
}

static bool
punycode(Buf *out, i32 const *cp, u32 n)
{
        u32 code  = 128;
        u32 delta = 0;
        u32 bias  = 72;
        u32 b     = 0;

        for (u32 i = 0; i < n; ++i) {
                if (cp[i] < 128) {
                        BufPutc(out, cp[i]);
                        b += 1;
                }
        }

        if (b > 0) {
                BufPutc(out, '-');
        }

        for (u32 h = b; h < n; ++delta, ++code) {
                u32 m = UINT32_MAX;
                for (u32 i = 0; i < n; ++i) {
                        if ((u32)cp[i] >= code && (u32)cp[i] < m) {
                                m = cp[i];
                        }
                }
                if ((m - code) > (UINT32_MAX - delta) / (h + 1)) {
                        return false;
                }
                delta += (m - code) * (h + 1);
                code   = m;
                for (u32 i = 0; i < n; ++i) {
                        if ((u32)cp[i] < code) {
                                delta += 1;
                        }
                        if ((u32)cp[i] != code) {
                                continue;
                        }
                        u32 q = delta;
                        for (u32 k = 36;; k += 36) {
                                u32 t = (k <= bias)      ? 1
                                      : (k >= bias + 26) ? 26
                                      :                    k - bias;
                                if (q < t) {
                                        break;
                                }
                                BufPutc(out, puny_digit(t + (q - t) % (36 - t)));
                                q = (q - t) / (36 - t);
                        }
                        BufPutc(out, puny_digit(q));
                        bias   = puny_adapt(delta, h + 1, h == b);
                        delta  = 0;
                        h     += 1;
                }
        }

        return true;
}

static Value
idna(Ty *ty, Value s)
{
        u8 const *p = (u8 const *)ss(s);
        isize n = sN(s);
        isize i = 0;

        while (i < n && p[i] < 128) {
                i += 1;
        }

        if (i == n) {
                return lower_part(ty, s, 0, n);
        }

        Buf out = {0};
        vec(i32) cps = {0};

        for (isize at = 0; at <= n;) {
                u8 const *dot = memchr(p + at, '.', n - at);
                isize end = (dot == NULL) ? n : (dot - p);
                bool ascii = true;
                v0(cps);
                for (isize j = at; j < end;) {
                        i32 cp;
                        isize k = utf8proc_iterate(p + j, end - j, &cp);
                        if (k <= 0) {
                                cp = 0xFFFD;
                                k  = 1;
                        }
                        cp     = utf8proc_tolower(cp);
                        ascii &= (cp < 128);
                        xvP(cps, cp);
                        j += k;
                }
                if (ascii) {
                        vfor(cps, BufPutc(&out, *it));
                } else {
                        BufLit(&out, "xn--");
                        punycode(&out, vv(cps), vN(cps));
                }
                if (dot == NULL) {
                        break;
                }
                BufPutc(&out, '.');
                at = end + 1;
        }

        xvF(cps);

        return buf_string(ty, &out);
}

// _http.idna(host: String) -> String
TY_BUILTIN(http_idna)
{
        return idna(ty, host);
}

static bool
bad_host(Value h)
{
        u8 const *p = (u8 const *)ss(h);

        for (isize i = 0; i < sN(h); ++i) {
                if (p[i] <= 0x20 || strchr("#/<>?@[\\]^|", p[i]) != NULL) {
                        return true;
                }
        }

        return false;
}

enum {
        UR_SCHEME,
        UR_USERNAME,
        UR_PASSWORD,
        UR_HOST,
        UR_PORT,
        UR_PATH,
        UR_QUERY,
        UR_FRAGMENT
};

static void
url_slots(Ty *ty, int class, u16 *out)
{
        static char const *const ur[] = { "scheme", "username", "password", "host", "port", "path", "query", "fragment" };

        Class *c = class_get(ty, class);

        for (int i = 0; i < countof(ur); ++i) {
                out[i] = field_slot(ty, c, ur[i]);
        }
}

// _http.setup-url(url: Class) -> nil
TY_BUILTIN(http_setup_url)
{
        if (url.type != VALUE_CLASS) {
                bP("expected a class");
        }

        class_ctor(ty, url.class);
        url_slots(ty, url.class, K.ur);
        K.url = url.class;

        return NIL;
}

inline static bool
scheme_char(u8 c)
{
        return IS(c, DIGIT) || ((c | 0x20) >= 'a' && (c | 0x20) <= 'z') || c == '+' || c == '-' || c == '.';
}

inline static isize
span_until(u8 const *p, isize i, isize n, char const *stop)
{
        while (i < n && strchr(stop, p[i]) == NULL) {
                i += 1;
        }

        return i;
}

static bool
parse_url(Ty *ty, Value *slot, u16 const *ur, Value s)
{
        u8 const *p = (u8 const *)ss(s);
        isize n = sN(s);
        isize i = 0;

        while (i < n && strchr(" \t\r\n\f\v", p[i]) != NULL && p[i] != 0) {
                i += 1;
        }
        while (n > i && strchr(" \t\r\n\f\v", p[n - 1]) != NULL && p[n - 1] != 0) {
                n -= 1;
        }

        for (int k = 0; k < 8; ++k) {
                slot[ur[k]] = NIL;
        }

        isize j = i;

        if (j < n && ((p[j] | 0x20) >= 'a' && (p[j] | 0x20) <= 'z')) {
                while (j < n && scheme_char(p[j])) {
                        j += 1;
                }
                if (j < n && p[j] == ':') {
                        slot[ur[UR_SCHEME]] = lower_part(ty, s, i, j - i);
                        i = j + 1;
                }
        }

        isize a0 = -1;
        isize a1 = -1;

        if (i + 1 < n && p[i] == '/' && p[i + 1] == '/') {
                a0 = i + 2;
                a1 = span_until(p, a0, n, "/?#");
                i  = a1;
        }

        isize pe = span_until(p, i, n, "?#");
        slot[ur[UR_PATH]] = pct_part(ty, s, i, pe - i, PCT_PATH);
        i = pe;

        if (i < n && p[i] == '?') {
                isize qe = span_until(p, i + 1, n, "#");
                slot[ur[UR_QUERY]] = pct_part(ty, s, i + 1, qe - i - 1, PCT_QUERY);
                i = qe;
        }

        if (i < n && p[i] == '#') {
                slot[ur[UR_FRAGMENT]] = pct_part(ty, s, i + 1, n - i - 1, PCT_QUERY);
        }

        if (a0 < 0) {
                return true;
        }

        isize h0 = a0;

        for (isize k = a1 - 1; k >= a0; --k) {
                if (p[k] == '@') {
                        u8 const *colon = memchr(p + a0, ':', k - a0);
                        isize ue = (colon == NULL) ? k : (colon - p);
                        slot[ur[UR_USERNAME]] = pct_part(ty, s, a0, ue - a0, PCT_USERINFO);
                        if (colon != NULL) {
                                slot[ur[UR_PASSWORD]] = pct_part(ty, s, ue + 1, k - ue - 1, PCT_USERINFO);
                        }
                        h0 = k + 1;
                        break;
                }
        }

        isize he;
        isize pt;
        Value host;

        if (h0 < a1 && p[h0] == '[') {
                u8 const *rb = memchr(p + h0, ']', a1 - h0);
                if (rb == NULL) {
                        return false;
                }
                he = rb - p;
                pt = he + 1;
                if (pt < a1 && (p[pt] != ':' || memchr(p + pt + 1, ':', a1 - pt - 1) != NULL)) {
                        return false;
                }
                host = lower_part(ty, s, h0 + 1, he - h0 - 1);
        } else {
                he = a1;
                for (isize k = a1 - 1; k >= h0; --k) {
                        if (p[k] == ':') {
                                he = k;
                                break;
                        }
                }
                pt   = he;
                host = idna(ty, pct_decode(ty, p + h0, he - h0, false, false));
        }

        slot[ur[UR_HOST]] = host;

        if (bad_host(host)) {
                return false;
        }

        if (pt + 1 < a1) {
                i64 port = 0;
                for (isize k = pt + 1; k < a1; ++k) {
                        if (!IS(p[k], DIGIT)) {
                                return false;
                        }
                        port = 10 * port + (p[k] - '0');
                        if (port > 65535) {
                                return false;
                        }
                }
                slot[ur[UR_PORT]] = INTEGER(port);
        }

        return true;
}

// _http.parse-url(url: Object, s: String) -> Bool
TY_BUILTIN(http_parse_url)
{
        if (url.type != VALUE_OBJECT) {
                bP("expected a URL object");
        }

        u16 local[8];
        u16 *ur = K.ur;

        if (url.class != K.url) {
                url_slots(ty, url.class, local);
                ur = local;
        }

        pct_once();

        GC_STOP();
        bool ok = parse_url(ty, url.object->slots, ur, s);
        GC_RESUME();

        return BOOLEAN(ok);
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
        u8 const *p = (u8 const *)ss(query);
        isize n = sN(query);
        isize i = 0;

        GC_STOP();

        Value d = DICT(dict_new(ty));

        while (i <= n) {
                u8 const *amp = memchr(p + i, '&', n - i);
                isize end = (amp == NULL) ? n : (amp - p);

                if (end == i) {
                        if (amp == NULL) {
                                break;
                        }
                        i = end + 1;
                        continue;
                }

                u8 const *eq = memchr(p + i, '=', end - i);
                isize klen = (eq == NULL) ? (end - i) : (eq - (p + i));
                Value key = pct_decode(ty, p + i, klen, true, true);
                Value val = NIL;

                if (eq != NULL) {
                        isize at = eq + 1 - p;
                        val = pct_decode(ty, p + at, end - at, true, true);
                }

                Value *slot = dict_get_value(ty, d.dict, &key);

                if (slot == NULL) {
                        dict_put_value(ty, d.dict, key, val);
                } else if (slot->type == VALUE_ARRAY) {
                        vAp(slot->array, val);
                } else {
                        Array *both = vAn(2);
                        uvP(*both, *slot);
                        uvP(*both, val);
                        *slot = ARRAY(both);
                }

                if (amp == NULL) {
                        break;
                }

                i = end + 1;
        }

        GC_RESUME();

        return d;
}

static void
query_pair(Ty *ty, Buf *out, Value const *k, Value const *v, bool blank)
{
        Value ks = (k->type == VALUE_STRING) ? *k : value_vshow(ty, k, 0);

        if (BufLen(out) > 0) {
                BufPutc(out, '&');
        }

        pct_encode_into(out, (u8 const *)ss(ks), sN(ks), PCT_UNRESERVED);

        if (v->type == VALUE_NIL) {
                if (blank) {
                        BufPutc(out, '=');
                }
                return;
        }

        Value vs = (v->type == VALUE_STRING) ? *v : value_vshow(ty, v, 0);

        BufPutc(out, '=');
        pct_encode_into(out, (u8 const *)ss(vs), sN(vs), PCT_UNRESERVED);
}

static void
query_entry(Ty *ty, Buf *out, Value const *k, Value const *v, bool blank)
{
        if (v->type != VALUE_ARRAY) {
                query_pair(ty, out, k, v, blank);
                return;
        }

        vfor(*v->array, query_pair(ty, out, k, it, blank));
}

// _http.encode-query(params: Dict[_, _] | Array[(_, _)] | Tuple, blank: Bool = false) -> String
TY_BUILTIN(http_encode_query)
{
        Buf out = {0};

        pct_once();

        switch (params.type) {
        case VALUE_DICT:
                dfor(params.dict, query_entry(ty, &out, key, val, blank));
                break;

        case VALUE_ARRAY:
                vfor(*params.array, {
                        if (it->type != VALUE_TUPLE || it->count != 2) {
                                BufFree(&out);
                                bP("expected (key, value) pairs but got: %s", VSC(it));
                        }
                        query_entry(ty, &out, &it->items[0], &it->items[1], blank);
                });
                break;

        case VALUE_TUPLE:
                for (int i = 0; i < params.count; ++i) {
                        if (params.ids == NULL || params.ids[i] < 0) {
                                continue;
                        }
                        Value k = vSsz(M_NAME(params.ids[i]));
                        query_entry(ty, &out, &k, &params.items[i], blank);
                }
                break;

        default:
                BufFree(&out);
                TyBuiltinBadArg(ty, _name__, "params", "Dict | Array[(_, _)]", &params);
        }

        return buf_string(ty, &out);
}

// _http.cookies(header: String | nil) -> Dict[String, String]
TY_BUILTIN(http_cookies)
{
        if (header.type != VALUE_STRING) {
                return DICT(dict_new(ty));
        }

        GC_STOP();

        Value d = DICT(dict_new(ty));

        char const *p = (char const *)ss(header);
        usize n = sN(header);
        usize i = 0;

        while (i < n) {
                char const *semi = memchr(p + i, ';', n - i);
                usize end = (semi == NULL) ? n : (usize)(semi - p);
                char const *eq = memchr(p + i, '=', end - i);

                if (eq != NULL) {
                        usize ks = i;
                        usize ke = eq - p;
                        usize vs = ke + 1;
                        usize ve = end;
                        TrimSpan(p, &ks, &ke, " \t");
                        TrimSpan(p, &vs, &ve, " \t");
                        if (ve - vs >= 2 && p[vs] == '"' && p[ve - 1] == '"') {
                                vs += 1;
                                ve -= 1;
                        }
                        if (ke > ks) {
                                Value k = STRING_VIEW(header, ks, ke - ks);
                                if (dict_get_value(ty, d.dict, &k) == NULL) {
                                        dict_put_value(ty, d.dict, k, STRING_VIEW(header, vs, ve - vs));
                                }
                        }
                }

                i = end + 1;
        }

        GC_RESUME();

        return d;
}

// _http.sse(data: String | nil, event: String | nil = nil, id: String | nil = nil, retry: Int | nil = nil) -> String
TY_BUILTIN(http_sse)
{
        Buf out = {0};

/* ========================================================================= */
#define FIELD(name, v) do {                                                   \
        BufLit(&out, name ": ");                                              \
        for (usize _i = 0; _i < sN(v); ++_i) {                                \
                char _c = ss(v)[_i];                                          \
                BufPutc(&out, (_c == '\r' || _c == '\n') ? ' ' : _c);         \
        }                                                                     \
        BufPutc(&out, '\n');                                                  \
} while (0)
/* ------------------------------------------------------------------------- */
        if (event.type == VALUE_STRING) { FIELD("event", event); }
        if (id.type    == VALUE_STRING) { FIELD("id",    id);    }

        if (retry.type == VALUE_INTEGER) {
                BufLit(&out, "retry: ");
                BufInt(&out, retry.z);
                BufPutc(&out, '\n');
        }
/* ------------------------------------------------------------------------- */
#undef FIELD
/* ========================================================================= */

        if (data.type == VALUE_STRING) {
                char const *p = (char const *)ss(data);
                usize n = sN(data);
                usize i = 0;
                for (;;) {
                        usize j = i;
                        while (j < n && p[j] != '\r' && p[j] != '\n') {
                                j += 1;
                        }
                        BufLit(&out, "data: ");
                        BufPut(&out, p + i, j - i);
                        BufPutc(&out, '\n');
                        if (j >= n) {
                                break;
                        }
                        i = j + ((p[j] == '\r' && j + 1 < n && p[j + 1] == '\n') ? 2 : 1);
                }
        }

        BufPutc(&out, '\n');

        return buf_string(ty, &out);
}

// _http.date(t: Int) -> String
TY_BUILTIN(http_date)
{
        static char const *const days[]   = { "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat" };
        static char const *const months[] = { "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec" };
        time_t tt = t;
        struct tm tm;
        char buf[40];

        gmtime_r(&tt, &tm);

        int n = ty_snprintf(
                buf,
                sizeof buf,
                "%s, %02d %s %04d %02d:%02d:%02d GMT",
                days[tm.tm_wday],
                tm.tm_mday,
                months[tm.tm_mon],
                tm.tm_year + 1900,
                tm.tm_hour,
                tm.tm_min,
                tm.tm_sec
        );

        return vSs(buf, n);
}

static u8 const *
find(u8 const *p, usize n, u8 const *w, usize wn)
{
        return memmem(p, n, w, wn);
}

static bool
part_headers(u8 const *p, usize n, Span *name, Span *file, Span *ctype)
{
        usize i = 0;

        *name  = (Span) { .len = UINT32_MAX };
        *file  = (Span) { .len = UINT32_MAX };
        *ctype = (Span) { .len = UINT32_MAX };

        while (i < n) {
                u8 const *eol = find(p + i, n - i, (u8 const *)"\r\n", 2);
                usize end = (eol == NULL) ? n : (usize)(eol - p);
                u8 const *colon = memchr(p + i, ':', end - i);

                if (colon == NULL) {
                        return false;
                }

                usize k  = colon - p;
                usize vs = k + 1;

                while (vs < end && (p[vs] == ' ' || p[vs] == '\t')) {
                        vs += 1;
                }

                if (MsgIeq((char const *)p + i, k - i, "content-disposition")) {
/* ========================================================================= */
#define PARAM(key, out) do {                                                                   \
        u8 const *_q = find(p + vs, end - vs, (u8 const *)(key "=\""), sizeof (key "=\"") - 1); \
        if (_q != NULL && (_q == p + vs || _q[-1] == ' ' || _q[-1] == ';')) {                 \
                usize _s = _q - p + sizeof (key "=\"") - 1;                                    \
                u8 const *_e = memchr(p + _s, '"', end - _s);                                 \
                if (_e != NULL) {                                                              \
                        (out)->off = _s;                                                       \
                        (out)->len = _e - (p + _s);                                            \
                }                                                                              \
        }                                                                                      \
} while (0)
/* ------------------------------------------------------------------------- */
                        PARAM("name",     name);
                        PARAM("filename", file);
/* ------------------------------------------------------------------------- */
#undef PARAM
/* ========================================================================= */
                } else if (MsgIeq((char const *)p + i, k - i, "content-type")) {
                        ctype->off = vs;
                        ctype->len = end - vs;
                } else {
                        return false;
                }

                i = end + 2;
        }

        return name->len != UINT32_MAX;
}

// _http.multipart(body: String, boundary: String, dir: String) -> (Dict[String, String], Dict[String, {name: String, type: String | nil, path: String}]) | nil
TY_BUILTIN(http_multipart)
{
        u8 const *p = (u8 const *)ss(body);
        usize n = sN(body);
        Buf sep = {0};

        BufLit(&sep, "\r\n--");
        BufStr(&sep, boundary);

        u8 const *w = (u8 const *)BufHead(&sep);
        usize wn    = BufLen(&sep);

        GC_STOP();

        Value fields = DICT(dict_new(ty));
        Value files  = DICT(dict_new(ty));
        Value result = NIL;

        u8 const *at = (n >= wn - 2 && memcmp(p, w + 2, wn - 2) == 0) ? p + wn - 2 : NULL;

        if (at == NULL) {
                u8 const *first = find(p, n, w, wn);
                at = (first == NULL) ? NULL : first + wn;
        }

        while (at != NULL) {
                usize left = p + n - at;

                if (left >= 2 && at[0] == '-' && at[1] == '-') {
                        result = vT(2);
                        result.items[0] = fields;
                        result.items[1] = files;
                        break;
                }

                if (left < 2 || at[0] != '\r' || at[1] != '\n') {
                        break;
                }

                at += 2;
                left -= 2;

                u8 const *hend = find(at, left, (u8 const *)"\r\n\r\n", 4);
                u8 const *head = at;
                usize hn;

                if (hend == NULL) {
                        if (left >= 2 && at[0] == '\r' && at[1] == '\n') {
                                hend = at - 2;
                                hn = 0;
                        } else {
                                break;
                        }
                } else {
                        hn = hend - at;
                }

                Span name, file, ctype;

                if (!part_headers(head, hn, &name, &file, &ctype)) {
                        break;
                }

                u8 const *data = hend + 4;
                u8 const *next = find(data, p + n - data, w, wn);

                if (next == NULL) {
                        break;
                }

                Value k = vSs(head + name.off, name.len);

                if (file.len != UINT32_MAX) {
                        char path[4096];
                        ty_snprintf(path, sizeof path, "%.*s/upload-XXXXXX", (int)sN(dir), ss(dir));
                        int fd = mkstemp(path);
                        if (fd < 0) {
                                break;
                        }
                        usize len = next - data;
                        usize off = 0;
                        while (off < len) {
                                isize k2 = write(fd, data + off, len - off);
                                if (k2 <= 0) {
                                        break;
                                }
                                off += k2;
                        }
                        close(fd);
                        Value fname = vSs(head + file.off, file.len);
                        Value ftype = (ctype.len == UINT32_MAX) ? NIL : vSs(head + ctype.off, ctype.len);
                        Value fpath = vSsz(path);
                        dict_put_value(ty, files.dict, k, vTn("name", fname, "type", ftype, "path", fpath));
                } else {
                        dict_put_value(ty, fields.dict, k, vSs(data, next - data));
                }

                at = next + wn;
        }

        GC_RESUME();
        BufFree(&sep);

        return result;
}

/* vim: set sts=8 sw=8 expandtab: */
