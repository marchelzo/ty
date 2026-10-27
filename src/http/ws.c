#include <string.h>

#if defined(__linux__) || defined(__FreeBSD__)
#include <sys/random.h>
#else
#include <stdlib.h>
#endif

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"
#include "blob.h"

enum {
        OP_CONT   = 0x0,
        OP_TEXT   = 0x1,
        OP_BINARY = 0x2,
        OP_CLOSE  = 0x8,
        OP_PING   = 0x9,
        OP_PONG   = 0xA
};

enum {
        CLOSE_NORMAL    = 1000,
        CLOSE_AWAY      = 1001,
        CLOSE_PROTOCOL  = 1002,
        CLOSE_NO_STATUS = 1005,
        CLOSE_ABNORMAL  = 1006,
        CLOSE_INVALID   = 1007,
        CLOSE_TOO_BIG   = 1009,
        CLOSE_INTERNAL  = 1011
};

enum {
        CLOSE_GRACE = 5000
};

struct ws {
        Xch    *x;
        Buf     msg;
        Buf     tmp;
        int     op;
        int     code;
        bool    frag;
        bool    fragz;
        bool    z;
        bool    sent;
        bool    got;
        bool    told;
        Codec  *inf;
        Codec  *def;
        u8      nreason;
        char    reason[123];
};

static char const Guid[] = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";
static char const Tail[] = { 0x00, 0x00, (char)0xFF, (char)0xFF };

bool
WsUtf8(void const *p, usize n)
{
        u8 const *s = p;
        usize i = 0;

        while (i < n) {
                if (i + 8 <= n) {
                        u64 w;
                        memcpy(&w, s + i, 8);
                        if ((w & 0x8080808080808080ULL) == 0) {
                                i += 8;
                                continue;
                        }
                }

                u8 c = s[i];

                if (c < 0x80) {
                        i += 1;
                        continue;
                }

                usize k;
                u32 cp;

                if (c >= 0xC2 && c <= 0xDF) {
                        k  = 1;
                        cp = c & 0x1F;
                } else if (c >= 0xE0 && c <= 0xEF) {
                        k  = 2;
                        cp = c & 0x0F;
                } else if (c >= 0xF0 && c <= 0xF4) {
                        k  = 3;
                        cp = c & 0x07;
                } else {
                        return false;
                }

                if (i + k >= n) {
                        return false;
                }

                for (usize j = 1; j <= k; ++j) {
                        if ((s[i + j] & 0xC0) != 0x80) {
                                return false;
                        }
                        cp = (cp << 6) | (s[i + j] & 0x3F);
                }

                if (
                        (k == 2 && cp < 0x800)
                     || (k == 3 && (cp < 0x10000 || cp > 0x10FFFF))
                     || (cp >= 0xD800 && cp <= 0xDFFF)
                ) {
                        return false;
                }

                i += k + 1;
        }

        return true;
}

static bool
valid_code(int code)
{
        return (code >= 1000 && code <= 1003)
            || (code >= 1007 && code <= 1011)
            || (code >= 3000 && code <= 4999);
}

static void
mask_key(u8 key[4])
{
#if defined(__linux__) || defined(__FreeBSD__)
        while (getrandom(key, 4, 0) != 4) {
                continue;
        }
#else
        arc4random_buf(key, 4);
#endif
}

static void
xor(u8 *p, usize n, u8 const key[4], usize phase)
{
        for (usize i = 0; i < n; ++i) {
                p[i] ^= key[(i + phase) & 3];
        }
}

usize
WsHeader(u8 hdr[14], int op, usize n, bool fin, bool rsv1, u8 const *mask)
{
        usize nh = 2;

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

        if (mask != NULL) {
                hdr[1] |= 0x80;
                memcpy(hdr + nh, mask, 4);
                nh += 4;
        }

        return nh;
}

void
WsFrameInto(Buf *out, int op, void const *p, usize n, bool fin, bool rsv1, bool masked)
{
        u8 hdr[14];
        u8 key[4];

        if (masked) {
                mask_key(key);
        }

        usize nh = WsHeader(hdr, op, n, fin, rsv1, masked ? key : NULL);

        BufPut(out, hdr, nh);

        char *dst = BufRoom(out, n);
        memcpy(dst, p, n);

        if (masked) {
                xor((u8 *)dst, n, key, 0);
        }

        out->count += n;
}

bool
WsDeflate(Ty *ty, Codec **z, void const *p, usize n, Buf *out)
{
        char const *err;

        if (*z == NULL) {
                *z = CodecNew("raw-deflate", 11, true, 6, &err);
                if (*z == NULL) {
                        return false;
                }
        } else {
                CodecReset(*z);
        }

        usize start = out->count;

        if (CodecRun(ty, *z, p, n, CODEC_FLUSH, (CodecBytes *)out, false, -1) != CODEC_OK) {
                return false;
        }

        if (out->count - start >= 4 && memcmp(out->items + out->count - 4, Tail, 4) == 0) {
                out->count -= 4;
        }

        return true;
}

int
WsInflate(Ty *ty, Codec **z, void const *p, usize n, Buf *out, i64 limit)
{
        char const *err;

        if (*z == NULL) {
                *z = CodecNew("raw-deflate", 11, false, 0, &err);
                if (*z == NULL) {
                        return CODEC_ERROR;
                }
        } else {
                CodecReset(*z);
        }

        int rc = CodecRun(ty, *z, p, n, CODEC_PROCESS, (CodecBytes *)out, false, limit);

        if (rc == CODEC_OK) {
                rc = CodecRun(ty, *z, Tail, sizeof Tail, CODEC_PROCESS, (CodecBytes *)out, false, limit);
        }

        if (rc != CODEC_OK) {
                CodecFree(*z);
                *z = NULL;
        }

        return rc;
}

static void
put_frame(Conn *c, int op, void const *p, usize n, bool rsv1)
{
        u8 hdr[14];
        usize nh = WsHeader(hdr, op, n, true, rsv1, NULL);

        ConnWrite(c, hdr, nh);
        ConnWrite(c, p, n);
}

static void
announce(Conn *c, Ws *ws)
{
        Loop *L = c->L;
        Ty *ty  = L->ty;

        if (ws->told) {
                return;
        }

        ws->told = true;

        Value reason = vSs(ws->reason, ws->nreason);
        Emit(L, EV_CLOSE, XchHandle(ws->x), INTEGER(ws->code ? ws->code : CLOSE_ABNORMAL), reason);
}

static void
send_close(Conn *c, Ws *ws, int code, char const *reason, usize n)
{
        u8 body[125];

        if (ws->sent) {
                return;
        }

        ws->sent = true;

        if (code == CLOSE_NO_STATUS || code == 0) {
                put_frame(c, OP_CLOSE, NULL, 0, false);
                return;
        }

        n = min(n, 123);
        body[0] = code >> 8;
        body[1] = code;
        memcpy(body + 2, reason, n);

        put_frame(c, OP_CLOSE, body, n + 2, false);
}

static void
fail(Conn *c, Ws *ws, int code, char const *reason)
{
        if (ws->code == 0) {
                ws->code = code;
        }

        send_close(c, ws, code, reason, strlen(reason));
        announce(c, ws);
        ConnFinish(c);
}

static bool
deliver(Conn *c, Ws *ws, int op, u8 const *p, usize n, bool compressed)
{
        Loop *L = c->L;
        Ty *ty  = L->ty;
        i64 max = L->g->cfg.ws_max;

        if (compressed) {
                if (!ws->z) {
                        fail(c, ws, CLOSE_PROTOCOL, "unexpected compressed frame");
                        return false;
                }
                BufClear(&ws->tmp);
                int rc = WsInflate(ty, &ws->inf, p, n, &ws->tmp, max);
                if (rc == CODEC_TOO_BIG) {
                        fail(c, ws, CLOSE_TOO_BIG, "message too big");
                        return false;
                }
                if (rc != CODEC_OK) {
                        fail(c, ws, CLOSE_INVALID, "bad compressed data");
                        return false;
                }
                p = (u8 const *)BufHead(&ws->tmp);
                n = BufLen(&ws->tmp);
        }

        Value msg;

        if (op == OP_TEXT) {
                if (!WsUtf8(p, n)) {
                        fail(c, ws, CLOSE_INVALID, "invalid UTF-8");
                        return false;
                }
                msg = vSs(p, n);
        } else {
                msg = BlobOf(ty, p, n);
        }

        Emit(L, EV_MESSAGE, XchHandle(ws->x), msg, NIL);

        return true;
}

static bool
control(Conn *c, Ws *ws, int op, u8 const *p, usize n)
{
        switch (op) {
        case OP_PING:
                if (!ws->sent) {
                        put_frame(c, OP_PONG, p, n, false);
                }
                return true;

        case OP_PONG:
                return true;

        case OP_CLOSE:
                break;

        default:
                fail(c, ws, CLOSE_PROTOCOL, "unknown opcode");
                return false;
        }

        int code = CLOSE_NO_STATUS;

        if (n == 1) {
                fail(c, ws, CLOSE_PROTOCOL, "");
                return false;
        }

        if (n >= 2) {
                code = (p[0] << 8) | p[1];
                if (!valid_code(code)) {
                        fail(c, ws, CLOSE_PROTOCOL, "invalid close code");
                        return false;
                }
                if (!WsUtf8(p + 2, n - 2)) {
                        fail(c, ws, CLOSE_INVALID, "invalid UTF-8");
                        return false;
                }
                ws->nreason = min(n - 2, sizeof ws->reason);
                memcpy(ws->reason, p + 2, ws->nreason);
        }

        ws->got = true;

        if (ws->code == 0) {
                ws->code = code;
        }

        send_close(c, ws, code, NULL, 0);
        announce(c, ws);
        ConnFinish(c);

        return false;
}

void
WsData(Conn *c)
{
        Loop *L = c->L;
        Ws *ws  = c->ws;
        i64 max = L->g->cfg.ws_max;

        while (!c->closing && !c->finishing && BufLen(&c->in) >= 2) {
                u8 *s = (u8 *)BufHead(&c->in);
                usize avail = BufLen(&c->in);

                bool fin  = (s[0] & 0x80) != 0;
                bool rsv1 = (s[0] & 0x40) != 0;
                int op    = s[0] & 0x0F;

                if ((s[0] & 0x30) != 0 || (rsv1 && (!ws->z || op >= 0x8 || op == OP_CONT))) {
                        fail(c, ws, CLOSE_PROTOCOL, "reserved bits set");
                        return;
                }

                if ((s[1] & 0x80) == 0) {
                        fail(c, ws, CLOSE_PROTOCOL, "unmasked client frame");
                        return;
                }

                u64 len = s[1] & 0x7F;
                usize hdr = 2;

                if (len == 126) {
                        if (avail < 4) {
                                break;
                        }
                        len = ((u64)s[2] << 8) | s[3];
                        hdr = 4;
                } else if (len == 127) {
                        if (avail < 10) {
                                break;
                        }
                        if (s[2] & 0x80) {
                                fail(c, ws, CLOSE_PROTOCOL, "invalid length");
                                return;
                        }
                        len = 0;
                        for (int i = 0; i < 8; ++i) {
                                len = (len << 8) | s[2 + i];
                        }
                        hdr = 10;
                }

                if (op >= 0x8 && (len > 125 || !fin)) {
                        fail(c, ws, CLOSE_PROTOCOL, "invalid control frame");
                        return;
                }

                if ((op > OP_BINARY && op < OP_CLOSE) || op > OP_PONG) {
                        fail(c, ws, CLOSE_PROTOCOL, "unknown opcode");
                        return;
                }

                if ((i64)len > max || (ws->frag && (i64)(BufLen(&ws->msg) + len) > max)) {
                        fail(c, ws, CLOSE_TOO_BIG, "message too big");
                        return;
                }

                usize total = hdr + 4 + len;

                if (avail < total) {
                        BufRoom(&c->in, total - avail);
                        break;
                }

                u8 *key = s + hdr;
                u8 *p   = s + hdr + 4;

                xor(p, len, key, 0);

                c->rk = RT_WS;
                ConnTimer(c, TM_READ, ws->sent ? CLOSE_GRACE : L->g->cfg.t_ws_idle);

                if (ws->sent && op != OP_CLOSE) {
                        BufEat(&c->in, total);
                        continue;
                }

                bool ok = true;

                switch (op) {
                case OP_CONT:
                        if (!ws->frag) {
                                fail(c, ws, CLOSE_PROTOCOL, "unexpected continuation");
                                return;
                        }
                        BufPut(&ws->msg, p, len);
                        if (fin) {
                                ws->frag = false;
                                ok = deliver(c, ws, ws->op, (u8 const *)BufHead(&ws->msg), BufLen(&ws->msg), ws->fragz);
                                BufClear(&ws->msg);
                                BufShrink(&ws->msg, 1 << 16);
                        }
                        break;

                case OP_TEXT:
                case OP_BINARY:
                        if (ws->frag) {
                                fail(c, ws, CLOSE_PROTOCOL, "expected continuation");
                                return;
                        }
                        if (fin) {
                                ok = deliver(c, ws, op, p, len, rsv1);
                        } else {
                                ws->frag  = true;
                                ws->op    = op;
                                ws->fragz = rsv1;
                                BufClear(&ws->msg);
                                BufPut(&ws->msg, p, len);
                        }
                        break;

                default:
                        ok = control(c, ws, op, p, len);
                        break;
                }

                if (!ok) {
                        return;
                }

                BufEat(&c->in, total);
        }

        if (!c->closing && !c->finishing) {
                ConnRead(c);
        }
}

void
WsTimeout(Conn *c, int kind)
{
        Ws *ws = c->ws;

        if (ws->code == 0) {
                ws->code = CLOSE_ABNORMAL;
        }

        ConnClose(c);
}

void
WsPing(Conn *c)
{
        Ws *ws = c->ws;
        i64 t  = c->L->g->cfg.t_ws_ping;

        if (ws->sent || t <= 0) {
                return;
        }

        put_frame(c, OP_PING, NULL, 0, false);
        ConnTimer(c, TM_AUX, t);
}

void
WsShutdown(Conn *c)
{
        static char const why[] = "server shutting down";
        Ws *ws = c->ws;

        if (ws->code == 0) {
                ws->code = CLOSE_AWAY;
        }

        send_close(c, ws, CLOSE_AWAY, why, sizeof why - 1);
        announce(c, ws);

        c->rk = RT_CLOSING;
        ConnTimer(c, TM_READ, CLOSE_GRACE);
}

void
WsClosed(Conn *c)
{
        Ws *ws = c->ws;
        Xch *x = ws->x;
        Loop *L = c->L;

        if (ws->code == 0) {
                ws->code = CLOSE_ABNORMAL;
        }

        announce(c, ws);
        Count(L, S_WS, -1);

        x->flags |= X_ENDED;
        x->flags &= ~X_NOTIFY;
        c->x = NULL;

        XchClosed(L, x);
}

void
WsFree(Ws *ws)
{
        CodecFree(ws->inf);
        CodecFree(ws->def);
        BufFree(&ws->msg);
        BufFree(&ws->tmp);
        xmF(ws);
}

static bool
negotiate(Value offer)
{
        if (offer.type != VALUE_STRING) {
                return false;
        }

        char const *p = (char const *)ss(offer);
        usize n = sN(offer);
        usize i = 0;

        while (i < n) {
                char const *comma = memchr(p + i, ',', n - i);
                usize end = (comma == NULL) ? n : (usize)(comma - p);
                usize j = i;
                bool first = true;
                bool ok = true;

                while (j < end) {
                        char const *semi = memchr(p + j, ';', end - j);
                        usize e = (semi == NULL) ? end : (usize)(semi - p);
                        usize a = j;
                        usize b = e;
                        TrimSpan(p, &a, &b, " \t");
                        char const *eq = memchr(p + a, '=', b - a);
                        usize ka = a;
                        usize kb = (eq == NULL) ? b : (usize)(eq - p);
                        TrimSpan(p, &ka, &kb, " \t");
                        usize kn = kb - ka;
                        if (first) {
                                ok = MsgIeq(p + a, kn, "permessage-deflate");
                                first = false;
                        } else if (
                                MsgIeq(p + a, kn, "server_no_context_takeover")
                             || MsgIeq(p + a, kn, "client_no_context_takeover")
                             || MsgIeq(p + a, kn, "client_max_window_bits")
                        ) {
                        } else if (MsgIeq(p + a, kn, "server_max_window_bits") && eq != NULL) {
                                usize va = eq + 1 - p;
                                usize vb = b;
                                TrimSpan(p, &va, &vb, " \t\"");
                                ok = ok && vb - va == 2 && memcmp(p + va, "15", 2) == 0;
                        } else {
                                ok = false;
                        }
                        j = e + 1;
                }

                if (ok && !first) {
                        return true;
                }

                i = end + 1;
        }

        return false;
}

bool
WsAccept(Xch *x, Value key, Value protocol, Value offer)
{
        Conn *c = x->c;
        Loop *L = x->L;
        Buf *b  = &L->tmp;
        u8 digest[20];
        char accept[32];

        BufClear(b);
        BufStr(b, key);
        BufPut(b, Guid, sizeof Guid - 1);
        Sha1(BufHead(b), BufLen(b), digest);
        usize na = Base64(digest, 20, accept);

        bool z = L->g->cfg.ws_z && negotiate(offer);

        BufClear(b);
        BufLit(b, "HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ");
        BufPut(b, accept, na);
        BufLit(b, "\r\n");

        if (protocol.type == VALUE_STRING) {
                BufLit(b, "Sec-WebSocket-Protocol: ");
                BufStr(b, protocol);
                BufLit(b, "\r\n");
        }

        if (z) {
                BufLit(b, "Sec-WebSocket-Extensions: permessage-deflate; server_no_context_takeover; client_no_context_takeover\r\n");
        }

        BufLit(b, "\r\n");
        ConnWrite(c, BufHead(b), BufLen(b));

        Ws *ws = xmA(sizeof *ws);
        *ws = (Ws) { .x = x, .z = z };

        c->ws    = ws;
        c->proto = P_WS;
        c->rk    = RT_WS;
        c->hstate = HS_DONE;
        c->paused = false;

        x->flags |= X_WS | X_STARTED | X_UPGRADED;
        x->status = 101;

        Count(L, S_WS,       1);
        Count(L, S_WS_TOTAL, 1);

        ConnTimer(c, TM_READ, L->g->cfg.t_ws_idle);

        if (L->g->cfg.t_ws_ping > 0) {
                ConnTimer(c, TM_AUX, L->g->cfg.t_ws_ping);
        }

        if (BufLen(&c->in) > 0) {
                WsData(c);
        } else {
                ConnRead(c);
        }

        return true;
}

isize
WsSend(Xch *x, void const *p, usize n, int op)
{
        Conn *c = x->c;
        Loop *L = x->L;
        Ws *ws;

        if (c == NULL || c->closing || (ws = c->ws) == NULL || ws->sent) {
                return -1;
        }

        if (ws->z && (i64)n >= L->g->cfg.ws_zmin && (op == OP_TEXT || op == OP_BINARY)) {
                BufClear(&ws->tmp);
                if (WsDeflate(L->ty, &ws->def, p, n, &ws->tmp)) {
                        put_frame(c, op, BufHead(&ws->tmp), BufLen(&ws->tmp), true);
                        return ConnBuffered(c);
                }
        }

        put_frame(c, op, p, (op >= OP_CLOSE) ? min(n, 125) : n, false);

        return ConnBuffered(c);
}

void
WsClose(Xch *x, int code, Value reason)
{
        Conn *c = x->c;
        Ws *ws;

        if (c == NULL || c->closing || (ws = c->ws) == NULL || ws->sent) {
                return;
        }

        if (ws->code == 0) {
                ws->code = code;
        }

        send_close(c, ws, code, (reason.type == VALUE_STRING) ? (char const *)ss(reason) : "", (reason.type == VALUE_STRING) ? sN(reason) : 0);

        announce(c, ws);

        c->rk = RT_CLOSING;
        ConnTimer(c, TM_READ, CLOSE_GRACE);
}

// _http.ws-accept(loop: Ptr, id: Int, key: String, protocol: String | nil = nil, offer: String | nil = nil) -> Bool
TY_BUILTIN(http_ws_accept)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (x == NULL || x->c == NULL || x->c->closing || x->sid > 0 || (x->flags & X_STARTED)) {
                return BOOLEAN(false);
        }

        return BOOLEAN(WsAccept(x, key, protocol, offer));
}

// _http.ws-send(loop: Ptr, id: Int, data: String | Blob, op: Int = 1) -> Int
TY_BUILTIN(http_ws_send)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);
        u8 const *p;
        usize n;

        p = BytesOf(ty, _name__, data, &n);

        return INTEGER((x == NULL) ? -1 : WsSend(x, p, n, op));
}

// _http.ws-close(loop: Ptr, id: Int, code: Int = 1000, reason: String | nil = nil) -> nil
TY_BUILTIN(http_ws_close)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (x != NULL) {
                WsClose(x, code, reason);
        }

        return NIL;
}

// _http.pause(loop: Ptr, id: Int, on: Bool) -> nil
TY_BUILTIN(http_pause)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);
        Conn *c = (x != NULL) ? x->c : NULL;

        if (c == NULL || c->closing) {
                return NIL;
        }

        if (on) {
                c->paused = true;
        } else if (c->paused) {
                c->paused = false;
                if (c->proto == P_WS && BufLen(&c->in) > 0) {
                        WsData(c);
                } else {
                        ConnRead(c);
                }
        }

        return NIL;
}

// _http.ws-frame(op: Int, payload: String | Blob, fin: Bool = true, mask: Blob | Bool | nil = nil, rsv1: Bool = false) -> Blob
TY_BUILTIN(http_ws_frame)
{
        u8 const *p;
        usize n;
        u8 hdr[14];
        u8 key[4];
        u8 const *m = NULL;

        p = BytesOf(ty, _name__, payload, &n);

        if (mask.type == VALUE_BLOB && vN(*mask.blob) == 4) {
                memcpy(key, vv(*mask.blob), 4);
                m = key;
        } else if (mask.type == VALUE_BOOLEAN && mask.boolean) {
                mask_key(key);
                m = key;
        }

        usize nh = WsHeader(hdr, op, n, fin, rsv1, m);
        Blob *b = value_blob_new(ty);

        uvR(*b, nh + n);

        p = BytesOf(ty, _name__, payload, &n);

        memcpy(vv(*b), hdr, nh);
        memcpy(vv(*b) + nh, p, n);

        if (m != NULL) {
                xor(vv(*b) + nh, n, m, 0);
        }

        vN(*b) = nh + n;

        return BLOB(b);
}

// _http.ws-accept-key(key: String) -> String
TY_BUILTIN(http_ws_accept_key)
{
        char buf[256];
        u8 digest[20];
        char out[32];
        usize n = min(sN(key), sizeof buf - sizeof Guid);

        memcpy(buf, ss(key), n);
        memcpy(buf + n, Guid, sizeof Guid - 1);
        Sha1(buf, n + sizeof Guid - 1, digest);

        return vSs(out, Base64(digest, 20, out));
}

// _http.ws-deflate(data: String | Blob) -> Blob
TY_BUILTIN(http_ws_deflate)
{
        u8 const *p;
        usize n;
        Codec *z = NULL;
        Buf out = {0};

        p = BytesOf(ty, _name__, data, &n);

        bool ok = WsDeflate(ty, &z, p, n, &out);
        CodecFree(z);

        if (!ok) {
                BufFree(&out);
                bP("deflate failed");
        }

        Value v = BlobOf(ty, BufHead(&out), BufLen(&out));

        BufFree(&out);

        return v;
}

// _http.ws-inflate(data: String | Blob, limit: Int = -1) -> Blob | nil
TY_BUILTIN(http_ws_inflate)
{
        u8 const *p;
        usize n;
        Codec *z = NULL;
        Buf out = {0};

        p = BytesOf(ty, _name__, data, &n);

        int rc = WsInflate(ty, &z, p, n, &out, limit);
        CodecFree(z);

        if (rc != CODEC_OK) {
                BufFree(&out);
                return NIL;
        }

        Value v = BlobOf(ty, BufHead(&out), BufLen(&out));

        BufFree(&out);

        return v;
}

/* vim: set sts=8 sw=8 expandtab: */
