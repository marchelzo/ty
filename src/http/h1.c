#include <string.h>

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"

enum {
        SP_METHOD = 1,
        SP_URL    = 2,
        SP_FIELD  = 4,
        SP_VALUE  = 8
};

static char const Preface[] = "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n";
static char const Continue[] = "HTTP/1.1 100 Continue\r\n\r\n";

static llhttp_settings_t Settings;

inline static Conn *
C(llhttp_t const *p)
{
        return p->data;
}

inline static u32
offset_of(Conn *c, char const *at)
{
        return at - BufHead(&c->in);
}

inline static void
extend(Span *s, u32 off, usize len, bool open)
{
        if (!open) {
                s->off = off;
                s->len = 0;
        }

        s->len += len;
}

static int
on_begin(llhttp_t *p)
{
        Conn *c = C(p);
        Loop *L = c->L;

        c->x      = XchNew(L, c);
        c->hstate = HS_HEAD;
        c->rk     = RT_HEADER;

        ConnTimer(c, TM_READ, L->g->cfg.t_header);

        return HPE_OK;
}

static int
on_method(llhttp_t *p, char const *at, size_t n)
{
        Xch *x = C(p)->x;

        extend(&x->method, offset_of(C(p), at), n, x->span & SP_METHOD);
        x->span |= SP_METHOD;

        return HPE_OK;
}

static int
on_method_done(llhttp_t *p)
{
        C(p)->x->span &= ~SP_METHOD;
        return HPE_OK;
}

static int
on_url(llhttp_t *p, char const *at, size_t n)
{
        Xch *x = C(p)->x;

        extend(&x->target, offset_of(C(p), at), n, x->span & SP_URL);
        x->span |= SP_URL;

        return HPE_OK;
}

static int
on_url_done(llhttp_t *p)
{
        C(p)->x->span &= ~SP_URL;
        return HPE_OK;
}

static int
on_field(llhttp_t *p, char const *at, size_t n)
{
        Conn *c = C(p);
        Xch *x  = c->x;
        u32 off = offset_of(c, at);

        if (!(x->span & SP_FIELD)) {
                if ((i64)vN(x->hs) / 2 >= c->L->g->cfg.max_headers) {
                        x->flags |= X_REJECTED;
                        return HPE_USER;
                }
                xvP(x->hs, ((Span) { .off = off }));
                xvP(x->hs, ((Span) { .off = off + n }));
                x->span |= SP_FIELD;
        }

        v_L(x->hs).off += n;
        v__(x->hs, vN(x->hs) - 2).len += n;

        return HPE_OK;
}

static int
on_field_done(llhttp_t *p)
{
        C(p)->x->span &= ~SP_FIELD;
        return HPE_OK;
}

static int
on_value(llhttp_t *p, char const *at, size_t n)
{
        Conn *c = C(p);
        Xch *x  = c->x;

        extend(&v_L(x->hs), offset_of(c, at), n, x->span & SP_VALUE);
        x->span |= SP_VALUE;

        return HPE_OK;
}

static int
on_value_done(llhttp_t *p)
{
        Conn *c = C(p);
        Xch *x  = c->x;
        Span *k = v_(x->hs, vN(x->hs) - 2);
        Span *v = &v_L(x->hs);
        char const *b = BufHead(&c->in);

        x->span &= ~SP_VALUE;

        while (v->len > 0 && (b[v->off + v->len - 1] == ' ' || b[v->off + v->len - 1] == '\t')) {
                v->len -= 1;
        }

        if (MsgIeq(b + k->off, k->len, "host")) {
                x->flags |= X_HOST;
        } else if (MsgIeq(b + k->off, k->len, "expect") && MsgIeq(b + v->off, v->len, "100-continue")) {
                x->flags |= X_CONTINUE;
        }

        return HPE_OK;
}

static int
on_headers(llhttp_t *p)
{
        C(p)->hstate = HS_HEAD_DONE;
        return HPE_PAUSED;
}

static int
on_body(llhttp_t *p, char const *at, size_t n)
{
        Conn *c = C(p);
        Xch *x  = c->x;
        Loop *L = c->L;

        if (x->flags & X_REJECTED) {
                return HPE_OK;
        }

        if (x->got + (i64)n > L->g->cfg.max_body) {
                x->flags |= X_REJECTED;
                if (!(x->flags & X_DISPATCHED)) {
                        return HPE_USER;
                }
                BufClear(&x->body);
                return HPE_OK;
        }

        if (x->clen >= 0 && !(x->flags & X_DISPATCHED)) {
                Value s = Pinned(L, x).items[1];
                memcpy((char *)s.str + x->got, at, n);
        } else {
                BufPut(&x->body, at, n);
        }

        x->got += n;

        if ((x->flags & X_WAITING) && !(x->flags & X_BUFFER)) {
                x->flags &= ~X_WAITING;
                Emit(L, EV_READABLE, XchHandle(x), NIL, NIL);
        }

        return HPE_OK;
}

static int
on_complete(llhttp_t *p)
{
        C(p)->hstate = HS_DONE;
        return HPE_PAUSED;
}

static void
init_settings(void)
{
        llhttp_settings_init(&Settings);

        Settings.on_message_begin         = on_begin;
        Settings.on_method                = on_method;
        Settings.on_method_complete       = on_method_done;
        Settings.on_url                   = on_url;
        Settings.on_url_complete          = on_url_done;
        Settings.on_header_field          = on_field;
        Settings.on_header_field_complete = on_field_done;
        Settings.on_header_value          = on_value;
        Settings.on_header_value_complete = on_value_done;
        Settings.on_headers_complete      = on_headers;
        Settings.on_body                  = on_body;
        Settings.on_message_complete      = on_complete;
}

void
H1Open(Conn *c)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, init_settings);

        c->proto  = P_H1;
        c->hstate = HS_IDLE;
        c->fed    = 0;
        c->rk     = RT_IDLE;

        llhttp_init(&c->p, HTTP_REQUEST, &Settings);
        c->p.data = c;

        ConnTimer(c, TM_READ, c->L->g->cfg.t_idle);

        if (BufLen(&c->in) > 0) {
                H1Data(c);
        } else {
                ConnRead(c);
        }
}

void
H1Error(Conn *c, int status)
{
        Loop *L = c->L;
        Buf *b  = &L->tmp;
        char line[64];
        char const *reason = MsgReason(status);
        usize nreason = strlen(reason);

        BufClear(b);
        BufPut(b, line, MsgStatusLine(line, status));
        BufLit(b, "Date: ");
        BufPut(b, L->date, L->ndate);
        BufLit(b, "\r\n");

        if (L->g->cfg.nserver > 0) {
                BufLit(b, "Server: ");
                BufPut(b, L->g->cfg.server, L->g->cfg.nserver);
                BufLit(b, "\r\n");
        }

        BufLit(b, "Content-Type: text/plain; charset=utf-8\r\nContent-Length: ");
        BufInt(b, nreason);
        BufLit(b, "\r\nConnection: close\r\n\r\n");
        BufPut(b, reason, nreason);

        ConnWrite(c, BufHead(b), BufLen(b));

        if (c->x != NULL && !(c->x->flags & X_DISPATCHED)) {
                Xch *x = c->x;
                c->x = NULL;
                XchDrop(L, x);
        }

        c->hstate = HS_DONE;
        c->rk     = RT_NONE;
        c->tm[TM_READ] = 0;

        ConnFinish(c);
}

static int
error_status(Conn *c, llhttp_errno_t rc)
{
        if (c->x != NULL && (c->x->flags & X_REJECTED)) {
                return (c->hstate == HS_HEAD) ? 431 : 413;
        }

        return (rc == HPE_INVALID_VERSION) ? 505 : 400;
}

static bool
h2c_preface(Conn *c)
{
        usize n = BufLen(&c->in);
        usize k = min(n, sizeof Preface - 1);

        return c->reqs == 0
            && c->tls == NULL
            && c->L->g->cfg.h2
            && k > 0
            && memcmp(BufHead(&c->in), Preface, k) == 0;
}

static void
head_done(Conn *c, u32 hlen)
{
        Loop *L = c->L;
        Xch *x  = c->x;
        Config const *cfg = &L->g->cfg;
        llhttp_t *p = &c->p;

        x->hlen = hlen;
        x->v    = p->http_major * 10 + p->http_minor;

        if (p->http_major != 1 || p->http_minor > 1) {
                H1Error(c, 505);
                return;
        }

        if (x->v == 11 && !(x->flags & X_HOST)) {
                H1Error(c, 400);
                return;
        }

        if (p->method == HTTP_HEAD) {
                x->flags |= X_HEAD_REQ;
        }

        if (p->upgrade) {
                x->flags |= X_UPGRADE;
        }

        x->clen = (p->flags & F_CONTENT_LENGTH) ? (i64)p->content_length : -1;

        bool chunked = (p->flags & F_CHUNKED) != 0;
        bool body    = chunked || x->clen > 0;

        if (x->clen > cfg->max_body) {
                H1Error(c, 413);
                return;
        }

        Value head = MsgHeadString(L, x, BufHead(&c->in), hlen);

        Pin(L, x, head);

        c->hstate = HS_BODY;

        if (!body) {
                c->rk = RT_NONE;
                c->tm[TM_READ] = 0;
                return;
        }

        c->rk = RT_REQUEST;
        ConnTimer(c, TM_READ, cfg->t_request);

        if (x->flags & X_CONTINUE) {
                ConnWrite(c, Continue, sizeof Continue - 1);
        }

        if (atomic_load(&L->g->streams)) {
                XchDispatch(L, x, MsgRequest(L, x, head, NIL), true);
                return;
        }

        if (x->clen > 0) {
                Ty *ty = L->ty;
                GC_STOP();
                Value pair = vT(2);
                pair.items[0] = head;
                pair.items[1] = STRING(value_string_alloc(ty, x->clen), x->clen);
                Pin(L, x, pair);
                GC_RESUME();
        }
}

static void
message_done(Conn *c)
{
        Loop *L = c->L;
        Xch *x  = c->x;
        Ty *ty  = L->ty;

        c->rk = RT_NONE;
        c->tm[TM_READ] = 0;

        if (llhttp_should_keep_alive(&c->p)) {
                x->flags |= X_KEEP;
        }

        x->flags |= X_BODY_DONE;

        if (x->flags & X_DISPATCHED) {
                if (x->flags & X_BUFFER) {
                        x->flags &= ~X_BUFFER;
                        Value body = (x->flags & X_REJECTED) ? INTEGER(413) : vSs(BufHead(&x->body), BufLen(&x->body));
                        BufClear(&x->body);
                        Emit(L, EV_BODY, XchHandle(x), body, NIL);
                } else if (x->flags & X_WAITING) {
                        x->flags &= ~X_WAITING;
                        Emit(L, EV_READABLE, XchHandle(x), NIL, NIL);
                }
                return;
        }

        GC_STOP();

        Value pin  = Pinned(L, x);
        Value head = pin;
        Value body = NIL;

        if (pin.type == VALUE_TUPLE) {
                head = pin.items[0];
                body = pin.items[1];
        } else if (x->got > 0) {
                body = vSs(BufHead(&x->body), BufLen(&x->body));
                BufClear(&x->body);
        }

        XchDispatch(L, x, MsgRequest(L, x, head, body), false);

        GC_RESUME();
}

static void
h1_parse(Conn *c)
{
        Loop *L = c->L;
        Config const *cfg = &L->g->cfg;
        bool resumed = false;

        for (;;) {
                if (c->closing || c->finishing || c->proto != P_H1) {
                        return;
                }

                if (c->hstate == HS_DONE) {
                        if (BufLen(&c->in) > (usize)cfg->max_head) {
                                c->paused = true;
                        } else {
                                ConnRead(c);
                        }
                        return;
                }

                if (c->hstate == HS_IDLE && h2c_preface(c)) {
                        if (BufLen(&c->in) < sizeof Preface - 1) {
                                ConnRead(c);
                                return;
                        }
                        c->tm[TM_READ] = 0;
                        H2Open(c, true);
                        return;
                }

                usize avail = BufLen(&c->in) - c->fed;

                if (avail == 0 && !resumed) {
                        ConnRead(c);
                        return;
                }

                resumed = false;

                char *start = BufHead(&c->in) + c->fed;
                llhttp_errno_t rc = llhttp_execute(&c->p, start, avail);
                usize used = (rc == HPE_OK) ? avail : (usize)(llhttp_get_error_pos(&c->p) - start);

                switch (rc) {
                case HPE_OK:
                        if (c->hstate == HS_HEAD) {
                                c->fed += used;
                                if ((i64)c->fed > cfg->max_head) {
                                        c->x->flags |= X_REJECTED;
                                        H1Error(c, 431);
                                        return;
                                }
                        } else {
                                BufEat(&c->in, c->fed + used);
                                c->fed = 0;
                        }
                        if (c->x != NULL && (c->x->flags & X_DISPATCHED) && BufLen(&c->x->body) > (usize)cfg->high) {
                                c->paused = true;
                                return;
                        }
                        ConnRead(c);
                        return;

                case HPE_PAUSED:
                case HPE_PAUSED_UPGRADE:
                        if (c->hstate == HS_HEAD_DONE) {
                                u32 hlen = c->fed + used;
                                if ((i64)hlen > cfg->max_head) {
                                        c->x->flags |= X_REJECTED;
                                        c->hstate = HS_HEAD;
                                        H1Error(c, 431);
                                        return;
                                }
                                head_done(c, hlen);
                                if (c->hstate != HS_BODY) {
                                        return;
                                }
                                BufEat(&c->in, hlen);
                                c->fed = 0;
                                llhttp_resume(&c->p);
                                resumed = true;
                                continue;
                        }
                        BufEat(&c->in, c->fed + used);
                        c->fed = 0;
                        if (c->hstate == HS_DONE) {
                                message_done(c);
                        }
                        continue;

                default:
                        H1Error(c, error_status(c, rc));
                        return;
                }
        }
}

void
H1Data(Conn *c)
{
        h1_parse(c);
}

void
H1Resume(Conn *c)
{
        if (c->paused && !c->closing) {
                c->paused = false;
                h1_parse(c);
        }
}

void
H1Eof(Conn *c)
{
        Xch *x = c->x;

        if (x == NULL || c->hstate == HS_IDLE || c->hstate == HS_HEAD) {
                ConnClose(c);
                return;
        }

        if ((x->flags & X_STARTED) || !(x->flags & X_BODY_DONE)) {
                ConnClose(c);
                return;
        }

        x->flags |= X_CLOSE;
}

void
H1Timeout(Conn *c, int kind)
{
        Xch *x = c->x;

        if (kind == RT_HEADER && c->hstate == HS_HEAD) {
                H1Error(c, 408);
                return;
        }

        if (kind == RT_REQUEST && x != NULL && !(x->flags & (X_STARTED | X_DISPATCHED))) {
                H1Error(c, 408);
                return;
        }

        ConnClose(c);
}

void
H1Drained(Conn *c)
{
        if (c->x != NULL) {
                XchPump(c->x);
        }
}

void
H1Shutdown(Conn *c)
{
        if (c->x == NULL && (c->hstate == HS_IDLE || c->hstate == HS_HEAD)) {
                ConnClose(c);
                return;
        }

        if (c->x != NULL) {
                c->x->flags |= X_CLOSE;
        }
}

void
H1Closed(Conn *c)
{
        Xch *x = c->x;

        if (x != NULL) {
                c->x = NULL;
                XchClosed(c->L, x);
        }
}

void
H1Done(Conn *c, Xch *x)
{
        Loop *L = c->L;
        Config const *cfg = &L->g->cfg;

        Observe(L, x);

        if (c->x != x) {
                return;
        }

        bool close = !(x->flags & X_KEEP)
                  || (x->flags & X_CLOSE)
                  || !(x->flags & X_BODY_DONE)
                  || (x->flags & X_UPGRADE)
                  || L->stopping
                  || (cfg->max_reqs > 0 && (i64)c->reqs >= cfg->max_reqs);

        c->x = NULL;
        XchClosed(L, x);

        if (close) {
                c->hstate = HS_DONE;
                ConnFinish(c);
                return;
        }

        c->hstate = HS_IDLE;
        c->paused = false;
        c->rk     = RT_IDLE;

        llhttp_resume(&c->p);
        ConnTimer(c, TM_READ, cfg->t_idle);

        if (BufLen(&c->in) > 0) {
                h1_parse(c);
        } else {
                ConnRead(c);
        }
}

bool
H1Head(Xch *x, int status, Value ctype, Value headers, i64 length)
{
        Conn *c = x->c;
        Loop *L = x->L;
        Ty *ty  = L->ty;
        Config const *cfg = &L->g->cfg;
        Buf *b  = &L->tmp;
        char line[64];

        bool bodiless = status < 200 || status == 204 || status == 304;
        bool head     = (x->flags & X_HEAD_REQ) != 0;
        bool v10      = x->v == 10;

        bool close = !(x->flags & X_KEEP)
                  || (x->flags & X_CLOSE)
                  || ((x->flags & X_UPGRADE) && status != 101)
                  || L->stopping
                  || (cfg->max_reqs > 0 && (i64)c->reqs >= cfg->max_reqs);

        bool chunked = length < 0 && !v10 && !bodiless && !head;

        if (length < 0 && v10 && !bodiless && !head) {
                close = true;
        }

        BufClear(b);
        BufPut(b, line, MsgStatusLine(line, status));
        BufLit(b, "Date: ");
        BufPut(b, L->date, L->ndate);
        BufLit(b, "\r\n");

        if (cfg->nserver > 0) {
                BufLit(b, "Server: ");
                BufPut(b, cfg->server, cfg->nserver);
                BufLit(b, "\r\n");
        }

        if (!bodiless && ctype.type == VALUE_STRING) {
                BufLit(b, "Content-Type: ");
                BufStr(b, ctype);
                BufLit(b, "\r\n");
        }

        if (chunked) {
                BufLit(b, "Transfer-Encoding: chunked\r\n");
        } else if (!bodiless && length >= 0) {
                BufLit(b, "Content-Length: ");
                BufInt(b, length);
                BufLit(b, "\r\n");
        }

        if (headers.type == VALUE_DICT) {
                Value *v = dict_get_member(ty, headers.dict, "connection");
                if (v != NULL && v->type == VALUE_STRING && MsgIeq(ss(*v), sN(*v), "close")) {
                        close = true;
                }
        }

        if (close) {
                BufLit(b, "Connection: close\r\n");
        } else if (v10) {
                BufLit(b, "Connection: keep-alive\r\n");
        }

        if (cfg->nridh > 0 && x->nrid > 0) {
                BufPut(b, cfg->ridh, cfg->nridh);
                BufLit(b, ": ");
                BufPut(b, x->rid, x->nrid);
                BufLit(b, "\r\n");
        }

        MsgHeaders(ty, b, headers, false, true);
        BufLit(b, "\r\n");

        ConnWrite(c, BufHead(b), BufLen(b));

        if (close) {
                x->flags = (x->flags & ~X_KEEP) | X_CLOSE;
        }

        x->flags  |= X_STARTED | (chunked ? X_CHUNKED : 0);
        x->status  = status;
        x->length  = bodiless ? 0 : length;
        x->last    = L->now;

        if (status == 101) {
                x->flags |= X_UPGRADED;
        }

        return true;
}

void
H1Chunk(Xch *x, void const *p, usize n)
{
        Conn *c = x->c;

        if (n == 0 || (x->flags & X_HEAD_REQ)) {
                x->sent += (x->flags & X_HEAD_REQ) ? 0 : n;
                return;
        }

        if (x->flags & X_CHUNKED) {
                char hex[24];
                usize k = ty_snprintf(hex, sizeof hex, "%zx\r\n", n);
                ConnWrite(c, hex, k);
                ConnWrite(c, p, n);
                ConnWrite(c, "\r\n", 2);
        } else {
                ConnWrite(c, p, n);
        }

        x->sent += n;
        x->last  = x->L->now;
}

void
H1End(Xch *x)
{
        Conn *c = x->c;

        if (x->flags & X_ENDED) {
                return;
        }

        x->flags |= X_ENDED;

        if (x->flags & X_CHUNKED) {
                ConnWrite(c, "0\r\n\r\n", 5);
        } else if (!(x->flags & X_HEAD_REQ) && x->length >= 0 && x->sent != x->length) {
                x->flags |= X_CLOSE;
        } else if (x->length < 0 && !(x->flags & X_HEAD_REQ) && x->status >= 200) {
                x->flags |= X_CLOSE;
        }

        H1Done(c, x);
}

/* vim: set sts=8 sw=8 expandtab: */
