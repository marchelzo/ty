#include <errno.h>
#include <fcntl.h>
#include <time.h>
#include <poll.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"
#include "blob.h"

enum {
        WANT_READ  = -1,
        WANT_WRITE = -2,
        E_CLOSED   = -3,
        E_TLS      = -4,
        E_PROTO    = -5,
        E_IO       = -6,
        E_DECODE   = -7,
        E_TOO_BIG  = -8,
        E_CERT     = -9
};

enum {
        OP_CONT   = 0x0,
        OP_TEXT   = 0x1,
        OP_BINARY = 0x2,
        OP_CLOSE  = 0x8,
        OP_PING   = 0x9,
        OP_PONG   = 0xA
};

typedef struct wire Wire;

struct wire {
        int    fd;
        Tls   *tls;
        Wire  *lower;
        Buf    tin;
        Buf    tout;
        bool   eof;
        bool   owned;
        char   err[256];
};

typedef struct {
        Wire      w;
        Buf       in;
        llhttp_t  p;
        bool      head_req;
        bool      got_head;
        bool      done;
        bool      interim;
        bool      eof;
        u8        span;
        int       status;
        Span      reason;
        vec(Span) hs;
        Buf       raw;
        Buf       out;
        Buf       msg;
        int       mop;
        bool      frag;
        bool      closed;
        int       code;
        u8        nreason;
        char      creason[123];
        u32       fed;
        u32       hend;
} CConn;

static llhttp_settings_t Settings;

static void
wire_fail(Wire *w, char const *fmt, ...)
{
        va_list ap;

        va_start(ap, fmt);
        ty_vsnprintf(w->err, sizeof w->err, fmt, ap);
        va_end(ap);
}

static isize
raw_recv(Wire *w, Buf *out);

static int
wire_flush(Wire *w);

static int
tls_pump_out(Wire *w)
{
        usize n;

        while ((n = TlsPending(w->tls)) > 0) {
                char *p = BufRoom(&w->tout, n);
                isize k = TlsDrain(w->tls, p, n);
                if (k <= 0) {
                        break;
                }
                w->tout.count += k;
        }

        if (w->lower != NULL && BufLen(&w->tout) > 0) {
                isize k = TlsWrite(w->lower->tls, BufHead(&w->tout), BufLen(&w->tout));
                if (k < 0) {
                        wire_fail(w, "TLS error on the tunnel");
                        return E_TLS;
                }
                BufEat(&w->tout, k);
                return tls_pump_out(w->lower);
        }

        return 0;
}

static int
wire_flush(Wire *w)
{
        if (w->tls != NULL) {
                int rc = tls_pump_out(w);
                if (rc < 0) {
                        return rc;
                }
        }

        if (w->lower != NULL) {
                return wire_flush(w->lower);
        }

        while (BufLen(&w->tout) > 0) {
                isize k = send(w->fd, BufHead(&w->tout), BufLen(&w->tout), HTTP_SEND_FLAGS);
                if (k > 0) {
                        BufEat(&w->tout, k);
                        continue;
                }
                if (k < 0 && errno == EINTR) {
                        continue;
                }
                if (k < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
                        return WANT_WRITE;
                }
                wire_fail(w, "%s", strerror(errno));
                return E_IO;
        }

        return 0;
}

static isize
raw_recv(Wire *w, Buf *out)
{
        if (w->lower != NULL) {
                Wire *l = w->lower;
                for (;;) {
                        char *p = BufRoom(out, 65536);
                        isize k = TlsRead(l->tls, p, out->capacity - out->count);
                        if (k > 0) {
                                out->count += k;
                                return k;
                        }
                        if (k < 0) {
                                return (k == -1) ? -1 : E_TLS;
                        }
                        isize r = raw_recv(l, &l->tin);
                        if (r <= 0) {
                                return r;
                        }
                        TlsFeed(l->tls, BufHead(&l->tin), BufLen(&l->tin));
                        BufClear(&l->tin);
                        tls_pump_out(l);
                }
        }

        if (w->eof) {
                return -1;
        }

        for (;;) {
                char *p = BufRoom(out, 65536);
                isize k = recv(w->fd, p, out->capacity - out->count, 0);
                if (k > 0) {
                        out->count += k;
                        return k;
                }
                if (k == 0) {
                        w->eof = true;
                        return -1;
                }
                if (errno == EINTR) {
                        continue;
                }
                if (errno == EAGAIN || errno == EWOULDBLOCK) {
                        return 0;
                }
                if (errno == ECONNRESET) {
                        w->eof = true;
                        wire_fail(w, "connection reset by peer");
                        return E_IO;
                }
                wire_fail(w, "%s", strerror(errno));
                return E_IO;
        }
}

static isize
wire_recv(Wire *w, Buf *out)
{
        if (w->tls == NULL) {
                return raw_recv(w, out);
        }

        for (;;) {
                char *p = BufRoom(out, 65536);
                isize k = TlsRead(w->tls, p, out->capacity - out->count);

                if (k > 0) {
                        out->count += k;
                        tls_pump_out(w);
                        return k;
                }

                if (k == -1) {
                        return -1;
                }

                if (k < -1) {
                        TlsErrors(w->err, sizeof w->err);
                        return E_TLS;
                }

                isize r = raw_recv(w, &w->tin);

                if (r == -1) {
                        TlsFeedEof(w->tls);
                        k = TlsRead(w->tls, BufRoom(out, 65536), out->capacity - out->count);
                        if (k > 0) {
                                out->count += k;
                                return k;
                        }
                        return -1;
                }

                if (r <= 0) {
                        return r;
                }

                TlsFeed(w->tls, BufHead(&w->tin), BufLen(&w->tin));
                BufClear(&w->tin);
        }
}

inline static int
queued(int rc)
{
        return (rc == WANT_WRITE) ? 0 : rc;
}

static int
wire_send(Wire *w, void const *p, usize n)
{
        if (w->tls == NULL) {
                if (w->lower != NULL) {
                        isize k = TlsWrite(w->lower->tls, p, n);
                        if (k < 0) {
                                wire_fail(w, "TLS error on the tunnel");
                                return E_TLS;
                        }
                        return queued(wire_flush(w->lower));
                }
                BufPut(&w->tout, p, n);
                return queued(wire_flush(w));
        }

        isize k = TlsWrite(w->tls, p, n);

        if (k < 0 || (usize)k != n) {
                TlsErrors(w->err, sizeof w->err);
                return E_TLS;
        }

        return queued(wire_flush(w));
}

static int
wire_handshake(Ty *ty, Wire *w)
{
        for (;;) {
                int rc = TlsHandshake(ty, w->tls, NULL);
                int f  = tls_pump_out(w);

                if (f < 0) {
                        return f;
                }

                f = wire_flush(w);

                if (rc == 1) {
                        return (f == WANT_WRITE) ? WANT_WRITE : 0;
                }

                if (rc < 0) {
                        long v = TlsVerifyResult(w->tls);
                        if (v != 0) {
                                ty_snprintf(w->err, sizeof w->err, "certificate verification failed: %s", TlsVerifyError(v));
                                return E_CERT;
                        }
                        TlsErrors(w->err, sizeof w->err);
                        if (w->err[0] == '\0') {
                                ty_snprintf(w->err, sizeof w->err, "handshake failed");
                        }
                        return E_TLS;
                }

                if (f == WANT_WRITE) {
                        return WANT_WRITE;
                }

                isize r = raw_recv(w, &w->tin);

                if (r == 0) {
                        return WANT_READ;
                }

                if (r < 0) {
                        if (w->err[0] == '\0') {
                                ty_snprintf(w->err, sizeof w->err, "connection closed during the TLS handshake");
                        }
                        return E_CLOSED;
                }

                TlsFeed(w->tls, BufHead(&w->tin), BufLen(&w->tin));
                BufClear(&w->tin);
        }
}

static void
wire_free(Wire *w)
{
        if (w->tls != NULL) {
                TlsShutdown(w->tls);
                tls_pump_out(w);
                wire_flush(w);
                TlsFree(w->tls);
                w->tls = NULL;
        }

        if (w->lower == NULL && w->fd >= 0 && w->owned) {
                close(w->fd);
        }

        w->fd = -1;

        BufFree(&w->tin);
        BufFree(&w->tout);
}

inline static CConn *
CC(llhttp_t const *p)
{
        return p->data;
}

static int
on_begin(llhttp_t *p)
{
        CConn *c = CC(p);

        v0(c->hs);
        c->reason  = (Span) {0};
        c->span    = 0;
        c->interim = false;

        return HPE_OK;
}

static int
on_status(llhttp_t *p, char const *at, size_t n)
{
        CConn *c = CC(p);
        u32 off  = at - BufHead(&c->in);

        if (c->reason.len == 0) {
                c->reason.off = off;
        }

        c->reason.len += n;

        return HPE_OK;
}

static int
on_field(llhttp_t *p, char const *at, size_t n)
{
        CConn *c = CC(p);
        u32 off  = at - BufHead(&c->in);

        if (!(c->span & 1)) {
                xvP(c->hs, ((Span) { .off = off }));
                xvP(c->hs, ((Span) { .off = off + n }));
                c->span |= 1;
        }

        v__(c->hs, vN(c->hs) - 2).len += n;
        v_L(c->hs).off += n;

        return HPE_OK;
}

static int
on_field_done(llhttp_t *p)
{
        CC(p)->span &= ~1;
        return HPE_OK;
}

static int
on_value(llhttp_t *p, char const *at, size_t n)
{
        CConn *c = CC(p);
        u32 off  = at - BufHead(&c->in);
        Span *v  = &v_L(c->hs);

        if (!(c->span & 2)) {
                v->off = off;
                v->len = 0;
                c->span |= 2;
        }

        v->len += n;

        return HPE_OK;
}

static int
on_value_done(llhttp_t *p)
{
        CConn *c = CC(p);
        Span *v  = &v_L(c->hs);
        char const *b = BufHead(&c->in);

        c->span &= ~2;

        while (v->len > 0 && (b[v->off + v->len - 1] == ' ' || b[v->off + v->len - 1] == '\t')) {
                v->len -= 1;
        }

        c->hend = max(c->hend, v->off + v->len);

        return HPE_OK;
}

static int
on_headers(llhttp_t *p)
{
        CConn *c = CC(p);

        if (p->status_code >= 100 && p->status_code < 200 && p->status_code != 101) {
                c->interim = true;
                return HPE_OK;
        }

        c->got_head = true;
        c->status   = p->status_code;
        c->hend     = max(c->hend, c->reason.off + c->reason.len);

        return (c->head_req || c->status == 204 || c->status == 304) ? 1 : HPE_OK;
}

static int
on_body(llhttp_t *p, char const *at, size_t n)
{
        BufPut(&CC(p)->raw, at, n);
        return HPE_OK;
}

static int
on_complete(llhttp_t *p)
{
        CConn *c = CC(p);

        if (c->interim) {
                c->interim = false;
                return HPE_OK;
        }

        c->done = true;

        return HPE_PAUSED;
}

static void
init_settings(void)
{
        llhttp_settings_init(&Settings);

        Settings.on_message_begin         = on_begin;
        Settings.on_status                = on_status;
        Settings.on_header_field          = on_field;
        Settings.on_header_field_complete = on_field_done;
        Settings.on_header_value          = on_value;
        Settings.on_header_value_complete = on_value_done;
        Settings.on_headers_complete      = on_headers;
        Settings.on_body                  = on_body;
        Settings.on_message_complete      = on_complete;
}

static void
conn_free(void *p)
{
        CConn *c = p;

        wire_free(&c->w);

        if (c->w.lower != NULL) {
                Wire *l = c->w.lower;
                wire_free(l);
                xmF(l);
        }

        BufFree(&c->in);
        BufFree(&c->raw);
        BufFree(&c->out);
        BufFree(&c->msg);
        xvF(c->hs);
        xmF(c);
}

static Value
autoptr(Ty *ty, void *p, void (*dtor)(void *))
{
        Value *d = mAo(sizeof (Value [2]), GC_FFI_AUTO);

        d[0] = PTR((void *)dtor);
        d[1] = PTR(p);

        return GCPTR(p, d);
}

static void
reset_parser(CConn *c)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, init_settings);

        llhttp_init(&c->p, HTTP_RESPONSE, &Settings);
        c->p.data = c;

        c->got_head = false;
        c->done     = false;
        c->interim  = false;
        c->span     = 0;
        c->status   = 0;
        c->hend     = 0;
        c->fed      = 0;

        v0(c->hs);
        BufClear(&c->raw);
}

static void
adopt(CConn *c, CConn *outer)
{
        Buf rest = outer->in;

        outer->in = (Buf) {0};

        if (outer->w.tls != NULL) {
                Wire *l = xmA(sizeof *l);
                *l = outer->w;
                c->w.lower = l;
                c->w.fd    = l->fd;
        } else {
                c->w.fd    = outer->w.fd;
                c->w.owned = outer->w.owned;
                BufPut(&c->w.tout, BufHead(&outer->w.tout), BufLen(&outer->w.tout));
                BufFree(&outer->w.tin);
                BufFree(&outer->w.tout);
        }

        outer->w = (Wire) { .fd = -1 };

        if (c->w.tls != NULL) {
                TlsFeed(c->w.tls, BufHead(&rest), BufLen(&rest));
        } else {
                BufPut(&c->in, BufHead(&rest), BufLen(&rest));
        }

        BufFree(&rest);
}

// _http.client(fd: Int, tls: Ptr | nil = nil, host: String | nil = nil, over: Ptr | nil = nil) -> Ptr
TY_BUILTIN(http_client)
{
        CConn *c = xmA(sizeof *c);

        *c = (CConn) { .w = { .fd = fd, .owned = true } };

        reset_parser(c);

        if (tls.type == VALUE_PTR && tls.ptr != NULL) {
                SCRATCH_SAVE();
                char *h = NULL;
                if (host.type == VALUE_STRING) {
                        h = smA(sN(host) + 1);
                        memcpy(h, ss(host), sN(host));
                        h[sN(host)] = '\0';
                }
                c->w.tls = TlsNew(tls.ptr, false, h);
                SCRATCH_RESTORE();
                if (c->w.tls == NULL) {
                        conn_free(c);
                        bP("cannot create a TLS session");
                }
        }

        if (over.type == VALUE_PTR && over.ptr != NULL) {
                adopt(c, over.ptr);
        }

        return autoptr(ty, c, conn_free);
}

// _http.handshake(conn: Ptr) -> Int
TY_BUILTIN(http_handshake)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        return INTEGER((c->w.tls == NULL) ? 0 : wire_handshake(ty, &c->w));
}

// _http.alpn(conn: Ptr) -> String | nil
TY_BUILTIN(http_alpn)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        char const *p;
        unsigned n;

        if (c->w.tls == NULL || !TlsAlpn(c->w.tls, &p, &n)) {
                return NIL;
        }

        return vSs(p, n);
}

// _http.error(conn: Ptr) -> String
TY_BUILTIN(http_error)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        return vSsz((c->w.err[0] != '\0') ? c->w.err : (c->w.lower != NULL ? c->w.lower->err : ""));
}

// _http.fd(conn: Ptr) -> Int
TY_BUILTIN(http_fd)
{
        return INTEGER(((CConn *)PtrArg(ty, _name__, "conn", conn))->w.fd);
}

// _http.close(conn: Ptr) -> nil
TY_BUILTIN(http_close)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);

        wire_free(&c->w);

        if (c->w.lower != NULL) {
                wire_free(c->w.lower);
        }

        return NIL;
}

// _http.send(conn: Ptr, data: String | Blob) -> Int
TY_BUILTIN(http_send)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        char const *p;
        usize n;

        p = BytesOf(ty, _name__, data, &n);

        return INTEGER(wire_send(&c->w, p, n));
}

// _http.flush(conn: Ptr) -> Int
TY_BUILTIN(http_flush_conn)
{
        return INTEGER(wire_flush(&((CConn *)PtrArg(ty, _name__, "conn", conn))->w));
}

// _http.recv(conn: Ptr, limit: Int = 65536) -> Blob | Int | nil
TY_BUILTIN(http_recv)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);

        if (BufLen(&c->in) == 0) {
                isize r = wire_recv(&c->w, &c->in);
                if (r == 0) {
                        return INTEGER(WANT_READ);
                }
                if (r == -1) {
                        return NIL;
                }
                if (r < 0) {
                        return INTEGER(r);
                }
        }

        usize k = min(BufLen(&c->in), (usize)max(limit, 1));
        Value out = BlobOf(ty, BufHead(&c->in), k);
        BufEat(&c->in, k);

        return out;
}

// _http.request(conn: Ptr, method: String, target: String, host: String | nil, headers: Dict[String, _], length: Int = -2, body: String | Blob | nil = nil) -> Int
TY_BUILTIN(http_request)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        Buf *b   = &c->out;
        char const *p;
        usize n;

        p = BytesOf(ty, _name__, body, &n);

        BufClear(b);
        BufStr(b, method);
        BufPutc(b, ' ');
        BufStr(b, target);
        BufLit(b, " HTTP/1.1\r\n");

        Dict *d = (headers.type == VALUE_DICT) ? headers.dict : NULL;

        if (host.type == VALUE_STRING && (d == NULL || dict_get_member(ty, d, "host") == NULL)) {
                BufLit(b, "Host: ");
                BufStr(b, host);
                BufLit(b, "\r\n");
        }

        MsgHeaders(ty, b, headers, false, false);

        bool cl = d != NULL && dict_get_member(ty, d, "content-length") != NULL;

        if (length == -1) {
                BufLit(b, "Transfer-Encoding: chunked\r\n");
        } else if (length >= 0 && !cl) {
                BufLit(b, "Content-Length: ");
                BufInt(b, length);
                BufLit(b, "\r\n");
        }

        BufLit(b, "\r\n");
        BufPut(b, p, n);

        c->head_req = sN(method) == 4 && memcmp(ss(method), "HEAD", 4) == 0;

        reset_parser(c);

        int rc = wire_send(&c->w, BufHead(b), BufLen(b));

        BufClear(b);

        return INTEGER(rc);
}

// _http.chunk(conn: Ptr, data: String | Blob | nil) -> Int
TY_BUILTIN(http_chunk)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        Buf *b   = &c->out;
        char const *p;
        usize n;

        p = BytesOf(ty, _name__, data, &n);

        BufClear(b);

        if (data.type == VALUE_NIL) {
                BufLit(b, "0\r\n\r\n");
        } else if (n > 0) {
                BufHex(b, n);
                BufLit(b, "\r\n");
                BufPut(b, p, n);
                BufLit(b, "\r\n");
        }

        int rc = (BufLen(b) == 0) ? wire_flush(&c->w) : wire_send(&c->w, BufHead(b), BufLen(b));

        BufClear(b);

        return INTEGER(rc);
}

static int
parse(CConn *c)
{
        if (c->done) {
                return 0;
        }

        usize avail = BufLen(&c->in) - c->fed;

        if (avail == 0 && !c->eof) {
                return 0;
        }

        char const *start = BufHead(&c->in) + c->fed;
        llhttp_errno_t rc = (avail == 0) ? llhttp_finish(&c->p) : llhttp_execute(&c->p, start, avail);
        char const *pos   = llhttp_get_error_pos(&c->p);
        usize used        = (rc == HPE_OK || pos == NULL) ? avail : (usize)(pos - start);

        switch (rc) {
        case HPE_OK:
        case HPE_PAUSED:
        case HPE_PAUSED_UPGRADE:
                c->fed += used;
                if (rc == HPE_PAUSED_UPGRADE) {
                        c->done = true;
                }
                return 0;

        case HPE_INVALID_EOF_STATE:
                ty_snprintf(c->w.err, sizeof c->w.err, "the server closed the connection before the response was complete");
                return E_CLOSED;

        default:
                ty_snprintf(c->w.err, sizeof c->w.err, "malformed response (%s)", llhttp_errno_name(rc));
                return E_PROTO;
        }
}

static void
settle(CConn *c)
{
        if (c->got_head || c->done) {
                BufEat(&c->in, c->fed);
                c->fed = 0;
        }
}

static Value
build_head(Ty *ty, CConn *c)
{
        u32 n = max(c->hend, c->reason.off + c->reason.len);
        char *s = value_string_alloc(ty, max(n, 1));
        Value head = STRING(s, n);

        memcpy(s, BufHead(&c->in), n);

        for (usize i = 0; i < vN(c->hs); i += 2) {
                Span k = v__(c->hs, i);
                for (u32 j = 0; j < k.len; ++j) {
                        u8 ch = s[k.off + j];
                        s[k.off + j] = (ch >= 'A' && ch <= 'Z') ? (ch | 0x20) : ch;
                }
        }

        GC_STOP();

        Dict *d = dict_new_sized(ty, vN(c->hs) / 2 + 1);

        MsgFields(ty, d, head, vv(c->hs), vN(c->hs) / 2);

        Value reason = STRING_VIEW(head, c->reason.off, c->reason.len);
        int version  = c->p.http_major * 10 + c->p.http_minor;
        Value rsp    = MsgClientResponse(ty, c->status, reason, version, d);

        GC_RESUME();

        return rsp;
}

// _http.head(conn: Ptr) -> _
TY_BUILTIN(http_head)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);

        for (;;) {
                int rc = parse(c);

                if (rc < 0) {
                        return INTEGER(rc);
                }

                if (c->got_head) {
                        Value rsp = build_head(ty, c);
                        settle(c);
                        return rsp;
                }

                if (c->eof) {
                        ty_snprintf(c->w.err, sizeof c->w.err, "the server closed the connection without a response");
                        return INTEGER(E_CLOSED);
                }

                isize r = wire_recv(&c->w, &c->in);

                if (r == 0) {
                        return INTEGER(WANT_READ);
                }

                if (r == -1) {
                        c->eof = true;
                        if (BufLen(&c->in) == 0) {
                                ty_snprintf(c->w.err, sizeof c->w.err, "the server closed the connection without a response");
                                return INTEGER(E_CLOSED);
                        }
                        continue;
                }

                if (r < 0) {
                        return INTEGER(r);
                }
        }
}

static isize
body_fill(CConn *c)
{
        for (;;) {
                if (BufLen(&c->raw) > 0 || c->done) {
                        return 0;
                }

                int rc = parse(c);

                if (rc < 0) {
                        return rc;
                }

                settle(c);

                if (BufLen(&c->raw) > 0 || c->done) {
                        continue;
                }

                if (c->eof) {
                        ty_snprintf(c->w.err, sizeof c->w.err, "the server closed the connection before the response body was complete");
                        return E_CLOSED;
                }

                isize r = wire_recv(&c->w, &c->in);

                if (r == 0) {
                        return WANT_READ;
                }

                if (r == -1) {
                        c->eof = true;
                } else if (r < 0) {
                        return r;
                }
        }
}

// _http.body(conn: Ptr, limit: Int = 65536) -> Blob | Int | nil
TY_BUILTIN(http_body)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        isize rc = body_fill(c);

        if (rc < 0) {
                return INTEGER(rc);
        }

        if (BufLen(&c->raw) == 0) {
                return NIL;
        }

        usize k = min(BufLen(&c->raw), (usize)max(limit, 1));
        Value out = BlobOf(ty, BufHead(&c->raw), k);
        BufEat(&c->raw, k);

        return out;
}

// _http.body-into(conn: Ptr, out: Blob, limit: Int) -> Int
TY_BUILTIN(http_body_into)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        i64 got  = 0;

        while (got < limit) {
                isize rc = body_fill(c);
                if (rc < 0) {
                        return INTEGER((got > 0) ? got : rc);
                }
                if (BufLen(&c->raw) == 0) {
                        break;
                }
                usize k = min(BufLen(&c->raw), (usize)(limit - got));
                vvPn(*out, BufHead(&c->raw), k);
                BufEat(&c->raw, k);
                got += k;
        }

        return INTEGER(got);
}

// _http.reusable?(conn: Ptr) -> Bool
TY_BUILTIN(http_reusable)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);

        return BOOLEAN(
                c->done
             && !c->eof
             && !c->w.eof
             && BufLen(&c->in) == 0
             && BufLen(&c->raw) == 0
             && c->status != 101
             && llhttp_should_keep_alive(&c->p)
             && (c->w.tls == NULL || TlsBuffered(c->w.tls) == 0)
        );
}

// _http.stale?(conn: Ptr) -> Bool
TY_BUILTIN(http_stale)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        struct pollfd p = { .fd = c->w.fd, .events = POLLIN };

        if (c->w.fd < 0 || c->w.eof) {
                return BOOLEAN(true);
        }

        return BOOLEAN(poll(&p, 1, 0) != 0);
}

// _http.pending(conn: Ptr) -> Blob
TY_BUILTIN(http_pending)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        Value out = BlobOf(ty, BufHead(&c->in), BufLen(&c->in));
        BufClear(&c->in);

        return out;
}

bool
WsUtf8(void const *p, usize n);

usize
WsHeader(u8 hdr[14], int op, usize n, bool fin, bool rsv1, u8 const *mask);

void
WsFrameInto(Buf *out, int op, void const *p, usize n, bool fin, bool rsv1, bool masked);

static int
ws_fail(CConn *c, int code, char const *why)
{
        u8 body[2] = { code >> 8, code & 0xFF };
        Buf f = {0};

        if (!c->closed) {
                WsFrameInto(&f, OP_CLOSE, body, 2, true, false, true);
                wire_send(&c->w, BufHead(&f), BufLen(&f));
                BufFree(&f);
        }

        c->closed = true;
        c->code   = code;

        ty_snprintf(c->w.err, sizeof c->w.err, "%s", why);

        return E_PROTO;
}

// _http.ws-write(conn: Ptr, data: String | Blob, op: Int) -> Int
TY_BUILTIN(http_ws_write)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);
        char const *p;
        usize n;

        p = BytesOf(ty, _name__, data, &n);

        if (op == OP_CLOSE) {
                if (c->closed) {
                        return INTEGER(wire_flush(&c->w));
                }
        }

        BufClear(&c->out);
        WsFrameInto(&c->out, op, p, n, true, false, true);

        int rc = wire_send(&c->w, BufHead(&c->out), BufLen(&c->out));

        BufClear(&c->out);

        return INTEGER(rc);
}

// _http.ws-read(conn: Ptr, limit: Int) -> String | Blob | Int | nil
TY_BUILTIN(http_ws_read)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);

        for (;;) {
                while (BufLen(&c->in) >= 2) {
                        u8 *s = (u8 *)BufHead(&c->in);
                        usize avail = BufLen(&c->in);
                        bool fin = (s[0] & 0x80) != 0;
                        int op   = s[0] & 0x0F;

                        if ((s[0] & 0x70) != 0) {
                                return INTEGER(ws_fail(c, 1002, "reserved bits set"));
                        }

                        if (s[1] & 0x80) {
                                return INTEGER(ws_fail(c, 1002, "masked frame from the server"));
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
                                len = 0;
                                for (int i = 0; i < 8; ++i) {
                                        len = (len << 8) | s[2 + i];
                                }
                                if (len >> 63) {
                                        return INTEGER(ws_fail(c, 1002, "invalid frame length"));
                                }
                                hdr = 10;
                        }

                        if (op >= 0x8 && (len > 125 || !fin)) {
                                return INTEGER(ws_fail(c, 1002, "invalid control frame"));
                        }

                        if ((i64)len > limit || (c->frag && (i64)(BufLen(&c->msg) + len) > limit)) {
                                return INTEGER(ws_fail(c, 1009, "frame over max-message"));
                        }

                        if (avail < hdr + len) {
                                BufRoom(&c->in, hdr + len - avail);
                                break;
                        }

                        u8 *p = s + hdr;
                        Value out = NIL;

                        switch (op) {
                        case OP_CONT:
                                if (!c->frag) {
                                        return INTEGER(ws_fail(c, 1002, "unexpected continuation frame"));
                                }
                                BufPut(&c->msg, p, len);
                                if (fin) {
                                        c->frag = false;
                                        if (c->mop == OP_TEXT) {
                                                if (!WsUtf8((u8 *)BufHead(&c->msg), BufLen(&c->msg))) {
                                                        return INTEGER(ws_fail(c, 1007, "invalid UTF-8 in a text message"));
                                                }
                                                out = vSs(BufHead(&c->msg), BufLen(&c->msg));
                                        } else {
                                                out = BlobOf(ty, BufHead(&c->msg), BufLen(&c->msg));
                                        }
                                        BufClear(&c->msg);
                                }
                                break;

                        case OP_TEXT:
                        case OP_BINARY:
                                if (c->frag) {
                                        return INTEGER(ws_fail(c, 1002, "expected a continuation frame"));
                                }
                                if (!fin) {
                                        c->frag = true;
                                        c->mop  = op;
                                        BufClear(&c->msg);
                                        BufPut(&c->msg, p, len);
                                        break;
                                }
                                if (op == OP_TEXT) {
                                        if (!WsUtf8(p, len)) {
                                                return INTEGER(ws_fail(c, 1007, "invalid UTF-8 in a text message"));
                                        }
                                        out = vSs(p, len);
                                } else {
                                        out = BlobOf(ty, p, len);
                                }
                                break;

                        case OP_PING:
                                if (!c->closed) {
                                        BufClear(&c->out);
                                        WsFrameInto(&c->out, OP_PONG, p, len, true, false, true);
                                        wire_send(&c->w, BufHead(&c->out), BufLen(&c->out));
                                        BufClear(&c->out);
                                }
                                break;

                        case OP_PONG:
                                break;

                        case OP_CLOSE: {
                                int code = 1005;
                                if (len == 1) {
                                        return INTEGER(ws_fail(c, 1002, "truncated close frame"));
                                }
                                if (len >= 2) {
                                        code = (p[0] << 8) | p[1];
                                        bool ok = (code >= 1000 && code <= 1003) || (code >= 1007 && code <= 1011) || (code >= 3000 && code <= 4999);
                                        if (!ok) {
                                                return INTEGER(ws_fail(c, 1002, "invalid close code"));
                                        }
                                        if (!WsUtf8(p + 2, len - 2)) {
                                                return INTEGER(ws_fail(c, 1007, "invalid UTF-8 in a close reason"));
                                        }
                                        c->nreason = min(len - 2, sizeof c->creason);
                                        memcpy(c->creason, p + 2, c->nreason);
                                }
                                if (!c->closed) {
                                        u8 body[2] = { code >> 8, code & 0xFF };
                                        BufClear(&c->out);
                                        WsFrameInto(&c->out, OP_CLOSE, body, (code == 1005) ? 0 : 2, true, false, true);
                                        wire_send(&c->w, BufHead(&c->out), BufLen(&c->out));
                                        BufClear(&c->out);
                                }
                                c->closed = true;
                                c->code   = code;
                                BufEat(&c->in, hdr + len);
                                return NIL;
                        }

                        default:
                                return INTEGER(ws_fail(c, 1002, "unknown opcode"));
                        }

                        BufEat(&c->in, hdr + len);

                        if (out.type != VALUE_NIL) {
                                return out;
                        }
                }

                if (c->closed) {
                        return NIL;
                }

                isize r = wire_recv(&c->w, &c->in);

                if (r == 0) {
                        return INTEGER(WANT_READ);
                }

                if (r == -1) {
                        c->closed = true;
                        c->code   = (c->code == 0) ? 1006 : c->code;
                        return NIL;
                }

                if (r < 0) {
                        return INTEGER(r);
                }
        }
}

// _http.ws-status(conn: Ptr) -> (Int, String) | nil
TY_BUILTIN(http_ws_status)
{
        CConn *c = PtrArg(ty, _name__, "conn", conn);

        if (!c->closed) {
                return NIL;
        }

        GC_STOP();
        Value pair = vT(2);
        pair.items[0] = INTEGER(c->code);
        pair.items[1] = vSs(c->creason, c->nreason);
        GC_RESUME();

        return pair;
}

enum {
        W_HEAD   = 1,
        W_BODY   = 2,
        W_UPLOAD = 3
};

enum {
        STREAM_WINDOW = 4 * 1024 * 1024,
        CONN_WINDOW   = 32 * 1024 * 1024,
        UPLOAD_HIGH   = 1024 * 1024
};

typedef struct h2s H2S;

struct h2s {
        i32       sid;
        int       status;
        Buf       hd;
        vec(Span) hs;
        bool      head;
        bool      end;
        bool      closed;
        bool      refused;
        bool      deferred;
        bool      eof;
        u32       code;
        Buf       body;
        Buf       up;
        Loop     *nl;
        i64       nt;
        H2S      *next;
};

typedef struct {
        TyMutex          mu;
        TyCondVar        cv;
        TyThread         th;
        bool             started;
        Wire             w;
        Buf              in;
        nghttp2_session *s;
        int              wake[2];
        bool             dead;
        bool             stop;
        bool             goaway;
        int              max_streams;
        int              active;
        char             err[256];
        H2S             *streams;
        H2S             *free;
} H2C;

static nghttp2_session_callbacks *Client;

static H2S *
h2s_find(H2C *h, i32 sid)
{
        for (H2S *st = h->streams; st != NULL; st = st->next) {
                if (st->sid == sid) {
                        return st;
                }
        }

        return NULL;
}

static void
h2s_notify(H2S *st)
{
        if (st->nl != NULL) {
                LoopNotify(st->nl, st->nt);
                st->nl = NULL;
        }
}

static void
h2_changed(H2C *h, H2S *st)
{
        TyCondVarBroadcast(&h->cv);

        if (st != NULL) {
                h2s_notify(st);
        } else {
                for (H2S *x = h->streams; x != NULL; x = x->next) {
                        h2s_notify(x);
                }
        }
}

static void
h2_die(H2C *h, char const *why)
{
        if (!h->dead) {
                h->dead = true;
                ty_snprintf(h->err, sizeof h->err, "%s", why);
        }

        h2_changed(h, NULL);
}

static int
c_on_header(nghttp2_session *s, nghttp2_frame const *f, u8 const *name, size_t nn, u8 const *value, size_t vn, u8 flags, void *user)
{
        H2S *st = nghttp2_session_get_stream_user_data(s, f->hd.stream_id);

        if (st == NULL || st->head) {
                return 0;
        }

        if (nn == 7 && memcmp(name, ":status", 7) == 0) {
                st->status = 0;
                for (size_t i = 0; i < vn; ++i) {
                        st->status = st->status * 10 + (value[i] - '0');
                }
                return 0;
        }

        if (nn > 0 && name[0] == ':') {
                return 0;
        }

        u32 off = BufLen(&st->hd);

        BufPut(&st->hd, name, nn);
        BufPut(&st->hd, value, vn);

        xvP(st->hs, ((Span) { .off = off,      .len = nn }));
        xvP(st->hs, ((Span) { .off = off + nn, .len = vn }));

        return 0;
}

static int
c_on_frame(nghttp2_session *s, nghttp2_frame const *f, void *user)
{
        H2C *h = user;

        if (f->hd.type == NGHTTP2_GOAWAY) {
                h->goaway = true;
                for (H2S *st = h->streams; st != NULL; st = st->next) {
                        if (st->sid > f->goaway.last_stream_id && !st->head) {
                                st->refused = true;
                        }
                }
                h2_changed(h, NULL);
                return 0;
        }

        if (f->hd.type == NGHTTP2_SETTINGS && !(f->hd.flags & NGHTTP2_FLAG_ACK)) {
                u32 m = nghttp2_session_get_remote_settings(s, NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS);
                h->max_streams = max(1, min((int)min(m, 1000u), 1000));
                return 0;
        }

        H2S *st = nghttp2_session_get_stream_user_data(s, f->hd.stream_id);

        if (st == NULL) {
                return 0;
        }

        if (f->hd.type == NGHTTP2_HEADERS && !st->head) {
                if (st->status >= 100 && st->status < 200 && st->status != 101) {
                        st->status = 0;
                        BufClear(&st->hd);
                        v0(st->hs);
                } else {
                        st->head = true;
                }
        }

        if ((f->hd.type == NGHTTP2_HEADERS || f->hd.type == NGHTTP2_DATA) && (f->hd.flags & NGHTTP2_FLAG_END_STREAM)) {
                st->end = true;
        }

        h2_changed(h, st);

        return 0;
}

static int
c_on_chunk(nghttp2_session *s, u8 flags, i32 sid, u8 const *data, size_t n, void *user)
{
        H2C *h  = user;
        H2S *st = nghttp2_session_get_stream_user_data(s, sid);

        if (st == NULL) {
                nghttp2_session_consume(s, sid, n);
                return 0;
        }

        BufPut(&st->body, data, n);
        h2_changed(h, st);

        return 0;
}

static int
c_on_close(nghttp2_session *s, i32 sid, u32 code, void *user)
{
        H2C *h  = user;
        H2S *st = nghttp2_session_get_stream_user_data(s, sid);

        if (st == NULL) {
                return 0;
        }

        st->closed = true;
        st->code   = code;

        if (code == NGHTTP2_REFUSED_STREAM) {
                st->refused = true;
        }

        h->active -= 1;
        h2_changed(h, st);

        return 0;
}

static nghttp2_ssize
c_on_read(nghttp2_session *s, i32 sid, u8 *buf, size_t len, u32 *flags, nghttp2_data_source *src, void *user)
{
        H2S *st = src->ptr;
        usize n = min(len, BufLen(&st->up));

        memcpy(buf, BufHead(&st->up), n);
        BufEat(&st->up, n);

        if (st->eof && BufLen(&st->up) == 0) {
                *flags |= NGHTTP2_DATA_FLAG_EOF;
                return n;
        }

        if (n == 0) {
                st->deferred = true;
                return NGHTTP2_ERR_DEFERRED;
        }

        H2C *h = user;
        h2_changed(h, st);

        return n;
}

static void
init_client(void)
{
        nghttp2_session_callbacks_new(&Client);
        nghttp2_session_callbacks_set_on_header_callback(Client, c_on_header);
        nghttp2_session_callbacks_set_on_frame_recv_callback(Client, c_on_frame);
        nghttp2_session_callbacks_set_on_data_chunk_recv_callback(Client, c_on_chunk);
        nghttp2_session_callbacks_set_on_stream_close_callback(Client, c_on_close);
}

static void
h2_poke(H2C *h)
{
        char b = 1;
        (void)!write(h->wake[1], &b, 1);
}

static void
h2_send(H2C *h)
{
        for (;;) {
                u8 const *data;
                nghttp2_ssize n = nghttp2_session_mem_send2(h->s, &data);
                if (n < 0) {
                        h2_die(h, nghttp2_strerror(n));
                        return;
                }
                if (n == 0) {
                        break;
                }
                int rc = wire_send(&h->w, data, n);
                if (rc < 0 && rc != WANT_WRITE) {
                        h2_die(h, h->w.err[0] ? h->w.err : "write failed");
                        return;
                }
        }
}

static void
h2_recv(H2C *h)
{
        for (;;) {
                isize r = wire_recv(&h->w, &h->in);
                if (r == 0) {
                        break;
                }
                if (r == -1) {
                        h2_die(h, "the server closed the HTTP/2 connection");
                        return;
                }
                if (r < 0) {
                        h2_die(h, h->w.err[0] ? h->w.err : "read failed");
                        return;
                }
                nghttp2_ssize n = nghttp2_session_mem_recv2(h->s, (u8 const *)BufHead(&h->in), BufLen(&h->in));
                if (n < 0) {
                        h2_die(h, nghttp2_strerror(n));
                        return;
                }
                BufEat(&h->in, n);
        }
}

static bool
h2_pending_out(H2C const *h)
{
        return BufLen(&h->w.tout) > 0
            || (h->w.tls != NULL && TlsPending(h->w.tls) > 0)
            || (h->w.lower != NULL && BufLen(&h->w.lower->tout) > 0);
}

static void *
h2_main(void *arg)
{
        H2C *h = arg;

        TyMutexLock(&h->mu);

        while (!h->stop) {
                if (!h->dead) {
                        h2_send(h);
                }

                struct pollfd p[2] = {
                        { .fd = h->wake[0], .events = POLLIN },
                        { .fd = h->dead ? -1 : h->w.fd, .events = POLLIN | (h2_pending_out(h) ? POLLOUT : 0) }
                };

                TyMutexUnlock(&h->mu);
                int rc = poll(p, 2, -1);
                TyMutexLock(&h->mu);

                if (rc < 0) {
                        continue;
                }

                if (p[0].revents & POLLIN) {
                        char buf[64];
                        while (read(h->wake[0], buf, sizeof buf) > 0) {
                                continue;
                        }
                }

                if (h->dead || h->stop) {
                        continue;
                }

                if (p[1].revents & POLLOUT) {
                        int f = wire_flush(&h->w);
                        if (f < 0 && f != WANT_WRITE) {
                                h2_die(h, h->w.err[0] ? h->w.err : "write failed");
                                continue;
                        }
                }

                if (p[1].revents & (POLLIN | POLLHUP | POLLERR)) {
                        h2_recv(h);
                }
        }

        TyMutexUnlock(&h->mu);

        return NULL;
}

static void
h2_free(void *p)
{
        H2C *h = p;

        if (h->started) {
                TyMutexLock(&h->mu);
                h->stop = true;
                TyMutexUnlock(&h->mu);
                h2_poke(h);
                TyThreadJoin(h->th);
        }

        if (h->s != NULL) {
                nghttp2_session_del(h->s);
        }

        for (H2S *st = h->streams, *next; st != NULL; st = next) {
                next = st->next;
                BufFree(&st->hd);
                BufFree(&st->body);
                BufFree(&st->up);
                xvF(st->hs);
                xmF(st);
        }

        for (H2S *st = h->free, *next; st != NULL; st = next) {
                next = st->next;
                BufFree(&st->hd);
                BufFree(&st->body);
                BufFree(&st->up);
                xvF(st->hs);
                xmF(st);
        }

        wire_free(&h->w);

        if (h->w.lower != NULL) {
                wire_free(h->w.lower);
                xmF(h->w.lower);
        }

        BufFree(&h->in);
        close(h->wake[0]);
        close(h->wake[1]);
        TyMutexDestroy(&h->mu);
        TyCondVarDestroy(&h->cv);
        xmF(h);
}

// _http.h2-client(conn: Ptr) -> Ptr
TY_BUILTIN(http_h2_client)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, init_client);

        CConn *c = PtrArg(ty, _name__, "conn", conn);
        H2C *h   = xmA(sizeof *h);
        nghttp2_option *opt;

        *h = (H2C) { .w = c->w, .in = c->in, .max_streams = 100 };

        c->w  = (Wire) { .fd = -1 };
        c->in = (Buf) {0};

        TyMutexInit(&h->mu);
        TyCondVarInit(&h->cv);

        if (pipe(h->wake) != 0) {
                h2_free(h);
                bP("pipe: %s", strerror(errno));
        }

        fcntl(h->wake[0], F_SETFL, O_NONBLOCK);
        fcntl(h->wake[1], F_SETFL, O_NONBLOCK);

        nghttp2_option_new(&opt);
        nghttp2_option_set_no_auto_window_update(opt, 1);
        nghttp2_option_set_peer_max_concurrent_streams(opt, 100);
        int err = nghttp2_session_client_new2(&h->s, Client, h, opt);
        nghttp2_option_del(opt);

        if (err != 0) {
                h2_free(h);
                bP("%s", nghttp2_strerror(err));
        }

        nghttp2_settings_entry iv[] = {
                { NGHTTP2_SETTINGS_ENABLE_PUSH,            0             },
                { NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, 100           },
                { NGHTTP2_SETTINGS_INITIAL_WINDOW_SIZE,    STREAM_WINDOW }
        };

        nghttp2_submit_settings(h->s, NGHTTP2_FLAG_NONE, iv, countof(iv));
        nghttp2_session_set_local_window_size(h->s, NGHTTP2_FLAG_NONE, 0, CONN_WINDOW);

        if (TyThreadCreate(&h->th, h2_main, h) != 0) {
                h2_free(h);
                bP("cannot start the HTTP/2 driver thread");
        }

        h->started = true;

        return autoptr(ty, h, h2_free);
}

static bool
h2_hop(void const *p, usize n)
{
        switch (n) {
        case 2:  return MsgIeq(p, n, "te");
        case 4:  return MsgIeq(p, n, "host");
        case 7:  return MsgIeq(p, n, "upgrade");
        case 10: return MsgIeq(p, n, "connection") || MsgIeq(p, n, "keep-alive");
        case 16: return MsgIeq(p, n, "proxy-connection");
        case 17: return MsgIeq(p, n, "transfer-encoding");
        }

        return false;
}

static int
nv_push(nghttp2_nv *nv, int n, int cap, Value const *k, Value const *v)
{
        if (k->type != VALUE_STRING || h2_hop(ss(*k), sN(*k))) {
                return n;
        }

        Value const *xs = (v->type == VALUE_ARRAY) ? vv(*v->array) : v;
        usize nx        = (v->type == VALUE_ARRAY) ? vN(*v->array) : 1;

        for (usize i = 0; i < nx && n < cap; ++i) {
                if (xs[i].type == VALUE_STRING) {
                        nv[n++] = (nghttp2_nv) {
                                .name     = (u8 *)ss(*k),
                                .namelen  = sN(*k),
                                .value    = (u8 *)ss(xs[i]),
                                .valuelen = sN(xs[i])
                        };
                }
        }

        return n;
}

// _http.h2-request(h2: Ptr, method: String, scheme: String, authority: String, path: String, headers: Dict[String, _], length: Int = -1, body: Bool = false) -> Int
TY_BUILTIN(http_h2_request)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);
        nghttp2_nv nv[128];
        char len[24];
        int n = 0;

        nv[n++] = (nghttp2_nv) { (u8 *)":method",    (u8 *)ss(method),    7,  sN(method)    };
        nv[n++] = (nghttp2_nv) { (u8 *)":scheme",    (u8 *)ss(scheme),    7,  sN(scheme)    };
        nv[n++] = (nghttp2_nv) { (u8 *)":authority", (u8 *)ss(authority), 10, sN(authority) };
        nv[n++] = (nghttp2_nv) { (u8 *)":path",      (u8 *)ss(path),      5,  sN(path)      };

        if (headers.type == VALUE_DICT) {
                dfor(headers.dict, n = nv_push(nv, n, countof(nv) - 1, key, val));
                Value *te = dict_get_member(ty, headers.dict, "te");
                if (te != NULL && te->type == VALUE_STRING && MsgIeq(ss(*te), sN(*te), "trailers")) {
                        nv[n++] = (nghttp2_nv) { (u8 *)"te", (u8 *)"trailers", 2, 8 };
                }
        }

        if (length >= 0 && (headers.type != VALUE_DICT || dict_get_member(ty, headers.dict, "content-length") == NULL) && n < countof(nv)) {
                nv[n++] = (nghttp2_nv) { (u8 *)"content-length", (u8 *)len, 14, ty_snprintf(len, sizeof len, "%"PRIi64, length) };
        }

        TyMutexLock(&h->mu);

        if (h->dead || h->goaway) {
                TyMutexUnlock(&h->mu);
                return INTEGER(E_CLOSED);
        }

        H2S *st = h->free;

        if (st != NULL) {
                h->free = st->next;
        } else {
                st = xmA(sizeof *st);
                *st = (H2S) {0};
        }

        BufClear(&st->hd);
        BufClear(&st->body);
        BufClear(&st->up);
        v0(st->hs);

        st->status   = 0;
        st->head     = false;
        st->end      = false;
        st->closed   = false;
        st->refused  = false;
        st->deferred = false;
        st->eof      = !body;
        st->code     = 0;
        st->nl       = NULL;

        nghttp2_data_provider2 prd = { .source.ptr = st, .read_callback = c_on_read };

        i32 sid = nghttp2_submit_request2(h->s, NULL, nv, n, body ? &prd : NULL, st);

        if (sid < 0) {
                st->next = h->free;
                h->free  = st;
                TyMutexUnlock(&h->mu);
                return INTEGER(E_PROTO);
        }

        st->sid     = sid;
        st->next    = h->streams;
        h->streams  = st;
        h->active  += 1;

        TyMutexUnlock(&h->mu);
        h2_poke(h);

        return INTEGER(sid);
}

// _http.h2-upload(h2: Ptr, sid: Int, data: String | Blob | nil, eof: Bool = false) -> Int
TY_BUILTIN(http_h2_upload)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);
        char const *p;
        usize n;

        p = BytesOf(ty, _name__, data, &n);

        TyMutexLock(&h->mu);

        H2S *st = h2s_find(h, sid);
        i64 rc;

        if (st == NULL || st->closed || h->dead) {
                rc = E_CLOSED;
        } else {
                BufPut(&st->up, p, n);
                st->eof = st->eof || eof;
                if (st->deferred) {
                        st->deferred = false;
                        nghttp2_session_resume_data(h->s, sid);
                }
                rc = BufLen(&st->up);
        }

        TyMutexUnlock(&h->mu);
        h2_poke(h);

        return INTEGER(rc);
}

static bool
h2_ready(H2C *h, H2S *st, int what)
{
        if (st == NULL || h->dead || st->closed || st->refused) {
                return true;
        }

        switch (what) {
        case W_HEAD:   return st->head;
        case W_BODY:   return BufLen(&st->body) > 0 || st->end;
        case W_UPLOAD: return BufLen(&st->up) < UPLOAD_HIGH / 2 || st->head;
        }

        return true;
}

// _http.h2-wait(h2: Ptr, sid: Int, what: Int, timeout: Float = -1.0) -> Bool
TY_BUILTIN(http_h2_wait)
{
        H2C *h    = PtrArg(ty, _name__, "h2", h2);
        u64 until = TyThreadGetTime() + (u64)(max(timeout, 0.0) * 1e9);

        UnlockTy();
        TyMutexLock(&h->mu);

        bool ok = true;

        while (!h2_ready(h, h2s_find(h, sid), what)) {
                u64 now = TyThreadGetTime();
                if (timeout < 0) {
                        TyCondVarWait(&h->cv, &h->mu);
                } else if (
                        (now >= until)
                     || !TyCondVarTimedWaitRelative(&h->cv, &h->mu, (until - now) / TY_1e6 + 1)
                ) {
                        ok = h2_ready(h, h2s_find(h, sid), what);
                        break;
                }
        }

        TyMutexUnlock(&h->mu);
        LockTy();

        return BOOLEAN(ok);
}

// _http.h2-watch(h2: Ptr, sid: Int, what: Int, loop: Ptr, timer: Int) -> Bool
TY_BUILTIN(http_h2_watch)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        TyMutexLock(&h->mu);

        H2S *st = h2s_find(h, sid);
        bool ready = h2_ready(h, st, what);

        if (!ready) {
                st->nl = loop.ptr;
                st->nt = timer;
        }

        TyMutexUnlock(&h->mu);

        return BOOLEAN(ready);
}

// _http.h2-unwatch(h2: Ptr, sid: Int) -> nil
TY_BUILTIN(http_h2_unwatch)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        TyMutexLock(&h->mu);

        H2S *st = h2s_find(h, sid);

        if (st != NULL) {
                st->nl = NULL;
        }

        TyMutexUnlock(&h->mu);

        return NIL;
}

static Value
h2_failure(H2C *h, H2S *st)
{
        return (st == NULL)   ? INTEGER(E_CLOSED)
             : st->refused    ? INTEGER(E_CLOSED)
             : h->dead        ? INTEGER(E_IO)
             :                  INTEGER(E_PROTO);
}

// _http.h2-head(h2: Ptr, sid: Int) -> _
TY_BUILTIN(http_h2_head)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        TyMutexLock(&h->mu);

        H2S *st = h2s_find(h, sid);

        if (st == NULL || !st->head) {
                Value r = (st != NULL && !st->closed && !st->refused && !h->dead) ? INTEGER(WANT_READ) : h2_failure(h, st);
                TyMutexUnlock(&h->mu);
                return r;
        }

        Buf hd   = {0};
        int status = st->status;
        usize nh = vN(st->hs) / 2;
        Span *sp = xmA(max(vN(st->hs), 1) * sizeof (Span));

        BufPut(&hd, BufHead(&st->hd), BufLen(&st->hd));
        memcpy(sp, vv(st->hs), vN(st->hs) * sizeof (Span));

        TyMutexUnlock(&h->mu);

        GC_STOP();

        usize n  = BufLen(&hd);
        char *s  = value_string_alloc(ty, max(n, 1));
        Value hv = STRING(s, n);

        memcpy(s, BufHead(&hd), n);
        BufFree(&hd);

        Dict *d = dict_new_sized(ty, nh + 1);

        MsgFields(ty, d, hv, sp, nh);
        xmF(sp);

        Value rsp = MsgClientResponse(ty, status, xSz(MsgReason(status)), 20, d);

        GC_RESUME();

        return rsp;
}

// _http.h2-take(h2: Ptr, sid: Int, limit: Int = 1048576) -> Blob | Int | nil
TY_BUILTIN(http_h2_take)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        TyMutexLock(&h->mu);

        H2S *st = h2s_find(h, sid);
        usize n = (st == NULL) ? 0 : min(BufLen(&st->body), (usize)max(limit, 1));

        if (n == 0) {
                Value r = (st != NULL && st->end)                              ? NIL
                        : (st != NULL && !st->closed && !st->refused && !h->dead) ? INTEGER(WANT_READ)
                        :                                                          h2_failure(h, st);
                TyMutexUnlock(&h->mu);
                return r;
        }

        TyMutexUnlock(&h->mu);

        Blob *b   = value_blob_new(ty);
        Value out = BLOB(b);

        uvR(*b, n);

        TyMutexLock(&h->mu);

        st = h2s_find(h, sid);

        if (st != NULL) {
                n = min(n, BufLen(&st->body));
                memcpy(vv(*b), BufHead(&st->body), n);
                vN(*b) = n;
                BufEat(&st->body, n);
                if (h->s != NULL && !h->dead) {
                        nghttp2_session_consume(h->s, sid, n);
                }
        }

        TyMutexUnlock(&h->mu);
        h2_poke(h);

        return out;
}

// _http.h2-cancel(h2: Ptr, sid: Int) -> nil
TY_BUILTIN(http_h2_cancel)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        TyMutexLock(&h->mu);

        H2S **pp = &h->streams;

        while (*pp != NULL && (*pp)->sid != sid) {
                pp = &(*pp)->next;
        }

        H2S *st = *pp;

        if (st != NULL) {
                if (!h->dead && h->s != NULL) {
                        if (!st->closed && (!st->end || !st->eof || BufLen(&st->up) > 0)) {
                                nghttp2_submit_rst_stream(h->s, NGHTTP2_FLAG_NONE, sid, st->end ? NGHTTP2_NO_ERROR : NGHTTP2_CANCEL);
                        }
                        if (BufLen(&st->body) > 0) {
                                nghttp2_session_consume(h->s, sid, BufLen(&st->body));
                        }
                        nghttp2_session_set_stream_user_data(h->s, sid, NULL);
                }
                if (!st->closed) {
                        h->active -= 1;
                }
                *pp = st->next;
                st->next = h->free;
                h->free  = st;
                BufShrink(&st->body, 1 << 16);
                BufShrink(&st->up, 1 << 16);
        }

        TyMutexUnlock(&h->mu);
        h2_poke(h);

        return NIL;
}

// _http.h2-state(h2: Ptr) -> (Int, Int, Bool)
TY_BUILTIN(http_h2_state)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        TyMutexLock(&h->mu);
        int active = h->active;
        int most   = h->max_streams;
        bool ok    = !h->dead && !h->goaway;
        TyMutexUnlock(&h->mu);

        Value t = vT(3);
        t.items[0] = INTEGER(active);
        t.items[1] = INTEGER(most);
        t.items[2] = BOOLEAN(ok);

        return t;
}

// _http.h2-error(h2: Ptr, sid: Int) -> (String, Bool)
TY_BUILTIN(http_h2_error)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);
        char buf[300];

        TyMutexLock(&h->mu);

        H2S *st = h2s_find(h, sid);

        if (h->dead) {
                ty_snprintf(buf, sizeof buf, "%s", h->err);
        } else if (st == NULL) {
                ty_snprintf(buf, sizeof buf, "unknown stream");
        } else if (st->refused) {
                ty_snprintf(buf, sizeof buf, "refused the stream");
        } else if (st->closed && !st->end) {
                ty_snprintf(buf, sizeof buf, "reset the stream (%s)", nghttp2_http2_strerror(st->code));
        } else {
                ty_snprintf(buf, sizeof buf, "stream closed");
        }

        bool refused = st != NULL && st->refused;

        TyMutexUnlock(&h->mu);

        GC_STOP();
        Value t = vT(2);
        t.items[0] = vSsz(buf);
        t.items[1] = BOOLEAN(refused);
        GC_RESUME();

        return t;
}

// _http.h2-close(h2: Ptr) -> nil
TY_BUILTIN(http_h2_close)
{
        H2C *h = PtrArg(ty, _name__, "h2", h2);

        UnlockTy();
        TyMutexLock(&h->mu);

        if (!h->dead && h->s != NULL) {
                nghttp2_submit_goaway(h->s, NGHTTP2_FLAG_NONE, 0, NGHTTP2_NO_ERROR, NULL, 0);
                h2_send(h);
                wire_flush(&h->w);
        }

        h2_die(h, "the HTTP/2 connection was closed");
        h->stop = true;

        TyMutexUnlock(&h->mu);

        h2_poke(h);
        TyThreadJoin(h->th);
        h->started = false;

        LockTy();

        return NIL;
}

typedef struct {
        Buf   buf;
        Buf   event;
        Buf   data;
        Buf   id;
        bool  any;
        bool  has_id;
        bool  bom;
        bool  cr;
        i64   retry;
} Sse;

static void
sse_free(void *p)
{
        Sse *s = p;

        BufFree(&s->buf);
        BufFree(&s->event);
        BufFree(&s->data);
        BufFree(&s->id);
        xmF(s);
}

static void
sse_dispatch(Ty *ty, Sse *s, Array *out)
{
        if (!s->any) {
                BufClear(&s->event);
                return;
        }

        if (BufLen(&s->data) > 0 && BufHead(&s->data)[BufLen(&s->data) - 1] == '\n') {
                s->data.count -= 1;
        }

        GC_STOP();

        Value ev   = (BufLen(&s->event) == 0) ? xSz("message") : vSs(BufHead(&s->event), BufLen(&s->event));
        Value data = vSs(BufHead(&s->data), BufLen(&s->data));
        Value id   = s->has_id ? vSs(BufHead(&s->id), BufLen(&s->id)) : NIL;

        vAp(out, MsgEvent(ty, ev, data, id, (s->retry >= 0) ? INTEGER(s->retry) : NIL));

        GC_RESUME();

        BufClear(&s->event);
        BufClear(&s->data);
        s->any = false;
}

static void
sse_line(Ty *ty, Sse *s, char const *p, usize n, Array *out)
{
        if (n == 0) {
                sse_dispatch(ty, s, out);
                return;
        }

        if (p[0] == ':') {
                return;
        }

        char const *colon = memchr(p, ':', n);
        usize fn = (colon == NULL) ? n : (usize)(colon - p);
        char const *v = (colon == NULL) ? p + n : colon + 1;
        usize vn = (colon == NULL) ? 0 : n - fn - 1;

        if (vn > 0 && v[0] == ' ') {
                v  += 1;
                vn -= 1;
        }

        if (fn == 5 && memcmp(p, "event", 5) == 0) {
                BufClear(&s->event);
                BufPut(&s->event, v, vn);
        } else if (fn == 4 && memcmp(p, "data", 4) == 0) {
                BufPut(&s->data, v, vn);
                BufPutc(&s->data, '\n');
                s->any = true;
        } else if (fn == 2 && memcmp(p, "id", 2) == 0) {
                if (memchr(v, '\0', vn) == NULL) {
                        BufClear(&s->id);
                        BufPut(&s->id, v, vn);
                        s->has_id = true;
                }
        } else if (fn == 5 && memcmp(p, "retry", 5) == 0) {
                i64 r = 0;
                bool ok = vn > 0;
                for (usize i = 0; i < vn; ++i) {
                        if (v[i] < '0' || v[i] > '9') {
                                ok = false;
                                break;
                        }
                        r = 10 * r + (v[i] - '0');
                }
                if (ok) {
                        s->retry = r;
                }
        }
}

// _http.sse-parser(last-id: String | nil = nil) -> Ptr
TY_BUILTIN(http_sse_parser)
{
        Sse *s = xmA(sizeof *s);

        *s = (Sse) { .bom = true, .retry = -1 };

        if (last_id.type == VALUE_STRING) {
                BufStr(&s->id, last_id);
                s->has_id = true;
        }

        return autoptr(ty, s, sse_free);
}

// _http.sse-feed[e](parser: Ptr, chunk: String | Blob | nil, out: Array[e], end: Bool = false) -> Array[e]
TY_BUILTIN(http_sse_feed)
{
        Sse *s = PtrArg(ty, _name__, "parser", parser);
        char const *p;
        usize n;

        if (out.type != VALUE_ARRAY) {
                TyBuiltinBadArg(ty, _name__, "out", "Array", &out);
        }

        p = BytesOf(ty, _name__, chunk, &n);
        BufPut(&s->buf, p, n);

        if (s->bom && BufLen(&s->buf) >= 3) {
                if (memcmp(BufHead(&s->buf), "\xEF\xBB\xBF", 3) == 0) {
                        BufEat(&s->buf, 3);
                }
                s->bom = false;
        }

        char const *b = BufHead(&s->buf);
        usize len = BufLen(&s->buf);
        usize start = 0;

        for (usize i = 0; i < len; ++i) {
                if (b[i] == '\n' && s->cr) {
                        s->cr = false;
                        start = i + 1;
                        continue;
                }
                s->cr = false;
                if (b[i] == '\n' || b[i] == '\r') {
                        sse_line(ty, s, b + start, i - start, out.array);
                        s->cr = b[i] == '\r';
                        start = i + 1;
                }
        }

        BufEat(&s->buf, start);

        if (end && BufLen(&s->buf) > 0) {
                sse_line(ty, s, BufHead(&s->buf), BufLen(&s->buf), out.array);
                BufClear(&s->buf);
                sse_dispatch(ty, s, out.array);
        }

        return out;
}

/* vim: set sts=8 sw=8 expandtab: */
