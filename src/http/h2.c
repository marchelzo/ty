#include <string.h>

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"

static nghttp2_session_callbacks *Server;

inline static Conn *
C(void *user)
{
        return user;
}

inline static Xch *
stream(nghttp2_session *s, i32 sid)
{
        return nghttp2_session_get_stream_user_data(s, sid);
}

static bool
hop_by_hop(void const *p, usize n)
{
        switch (n) {
        case 2:  return MsgIeq(p, n, "te");
        case 4:  return MsgIeq(p, n, "host");
        case 7:  return MsgIeq(p, n, "upgrade");
        case 16: return MsgIeq(p, n, "proxy-connection");
        }

        return MsgReserved(p, n);
}

static void
dispatch(Conn *c, Xch *x, bool pending)
{
        Loop *L = c->L;
        Ty *ty  = L->ty;

        GC_STOP();

        Value head = MsgHeadString(L, x, BufHead(&x->hd), BufLen(&x->hd));
        Value body = NIL;

        if (!pending && BufLen(&x->body) > 0) {
                body = vSs(BufHead(&x->body), BufLen(&x->body));
                BufClear(&x->body);
        }

        XchDispatch(L, x, MsgRequest(L, x, head, body), pending);

        GC_RESUME();
}

static void
reject(Conn *c, Xch *x, int status)
{
        x->flags |= X_REJECTED | X_EOF;
        H2Head(x, status, NIL, NIL, 0, false);
}

static int
on_begin(nghttp2_session *s, nghttp2_frame const *f, void *user)
{
        Conn *c = C(user);

        if (f->hd.type != NGHTTP2_HEADERS || f->headers.cat != NGHTTP2_HCAT_REQUEST) {
                return 0;
        }

        Xch *x = XchNew(c->L, c);

        x->sid = f->hd.stream_id;
        x->v   = 20;

        nghttp2_session_set_stream_user_data(s, x->sid, x);

        c->nx += 1;
        c->tm[TM_READ] = 0;

        return 0;
}

static int
on_header(
        nghttp2_session *s,
        nghttp2_frame const *f,
        u8 const *name,
        size_t nn,
        u8 const *value,
        size_t vn,
        u8 flags,
        void *user
)
{
        Conn *c = C(user);
        Xch *x  = stream(s, f->hd.stream_id);
        Config const *cfg = &c->L->g->cfg;

        if (x == NULL || f->hd.type != NGHTTP2_HEADERS || (x->flags & X_DISPATCHED)) {
                return 0;
        }

        x->hlen += nn + vn + 32;

        if (x->hlen > cfg->max_head) {
                return NGHTTP2_ERR_TEMPORAL_CALLBACK_FAILURE;
        }

        u32 off = BufLen(&x->hd);

        if (nn > 0 && name[0] == ':') {
                BufPut(&x->hd, value, vn);
                Span sp = { .off = off, .len = vn };
                if      (MsgIeq((char const *)name, nn, ":method"))    { x->method    = sp; }
                else if (MsgIeq((char const *)name, nn, ":path"))      { x->target    = sp; }
                else if (MsgIeq((char const *)name, nn, ":scheme"))    { x->scheme    = sp; }
                else if (MsgIeq((char const *)name, nn, ":authority")) { x->authority = sp; }
                return 0;
        }

        if ((i64)vN(x->hs) / 2 >= cfg->max_headers) {
                return NGHTTP2_ERR_TEMPORAL_CALLBACK_FAILURE;
        }

        BufPut(&x->hd, name, nn);
        BufPut(&x->hd, value, vn);

        xvP(x->hs, ((Span) { .off = off,      .len = nn }));
        xvP(x->hs, ((Span) { .off = off + nn, .len = vn }));

        return 0;
}

static int
on_frame(nghttp2_session *s, nghttp2_frame const *f, void *user)
{
        Conn *c = C(user);
        Loop *L = c->L;
        Ty *ty  = L->ty;

        if (f->hd.type != NGHTTP2_HEADERS && f->hd.type != NGHTTP2_DATA) {
                return 0;
        }

        Xch *x = stream(s, f->hd.stream_id);

        if (x == NULL || (x->flags & X_REJECTED)) {
                return 0;
        }

        bool end = (f->hd.flags & NGHTTP2_FLAG_END_STREAM) != 0;

        if (f->hd.type == NGHTTP2_HEADERS && !(x->flags & X_DISPATCHED)) {
                if (MsgIeq(BufHead(&x->hd) + x->method.off, x->method.len, "head")) {
                        x->flags |= X_HEAD_REQ;
                }
                if (end) {
                        x->flags |= X_BODY_DONE;
                        dispatch(c, x, false);
                } else if (atomic_load(&L->g->streams)) {
                        dispatch(c, x, true);
                }
                return 0;
        }

        if (!end) {
                return 0;
        }

        x->flags |= X_BODY_DONE;

        if (!(x->flags & X_DISPATCHED)) {
                dispatch(c, x, false);
        } else if (x->flags & X_BUFFER) {
                x->flags &= ~X_BUFFER;
                Value body = vSs(BufHead(&x->body), BufLen(&x->body));
                BufClear(&x->body);
                Emit(L, EV_BODY, XchHandle(x), body, NIL);
        } else if (x->flags & X_WAITING) {
                x->flags &= ~X_WAITING;
                Emit(L, EV_READABLE, XchHandle(x), NIL, NIL);
        }

        return 0;
}

static int
on_chunk(nghttp2_session *s, u8 flags, i32 sid, u8 const *data, size_t n, void *user)
{
        Conn *c = C(user);
        Loop *L = c->L;
        Xch *x  = stream(s, sid);

        if (x == NULL || (x->flags & X_REJECTED)) {
                return 0;
        }

        if (x->got + (i64)n > L->g->cfg.max_body) {
                BufClear(&x->body);
                if (!(x->flags & X_DISPATCHED)) {
                        reject(c, x, 413);
                        return 0;
                }
                x->flags |= X_REJECTED;
                if (x->flags & X_BUFFER) {
                        x->flags &= ~X_BUFFER;
                        Emit(L, EV_BODY, XchHandle(x), INTEGER(413), NIL);
                } else if (x->flags & X_WAITING) {
                        x->flags &= ~X_WAITING;
                        Emit(L, EV_READABLE, XchHandle(x), NIL, NIL);
                }
                return 0;
        }

        BufPut(&x->body, data, n);
        x->got += n;

        if ((x->flags & X_WAITING) && !(x->flags & X_BUFFER)) {
                x->flags &= ~X_WAITING;
                Emit(L, EV_READABLE, XchHandle(x), NIL, NIL);
        }

        return 0;
}

static int
on_close(nghttp2_session *s, i32 sid, u32 code, void *user)
{
        Conn *c = C(user);
        Loop *L = c->L;
        Xch *x  = stream(s, sid);

        if (x == NULL) {
                return 0;
        }

        nghttp2_session_set_stream_user_data(s, sid, NULL);

        c->nx -= 1;

        if ((x->flags & X_WAITING) || (x->flags & X_BUFFER)) {
                x->flags &= ~(X_WAITING | X_BUFFER);
                Emit(L, EV_READABLE, XchHandle(x), NIL, NIL);
        }

        XchClosed(L, x);

        if (c->nx == 0) {
                c->rk = RT_IDLE;
                ConnTimer(c, TM_READ, L->g->cfg.t_idle);
                if (c->goaway) {
                        ConnFinish(c);
                }
        }

        return 0;
}

static nghttp2_ssize
on_read(nghttp2_session *s, i32 sid, u8 *buf, size_t len, u32 *flags, nghttp2_data_source *src, void *user)
{
        Xch *x  = src->ptr;
        usize n = min(len, BufLen(&x->out));

        memcpy(buf, BufHead(&x->out), n);
        BufEat(&x->out, n);

        if ((x->flags & X_EOF) && BufLen(&x->out) == 0) {
                *flags |= NGHTTP2_DATA_FLAG_EOF;
                return n;
        }

        if (n == 0) {
                x->flags |= X_DEFERRED;
                return NGHTTP2_ERR_DEFERRED;
        }

        return n;
}

static void
init_callbacks(void)
{
        nghttp2_session_callbacks_new(&Server);
        nghttp2_session_callbacks_set_on_begin_headers_callback(Server, on_begin);
        nghttp2_session_callbacks_set_on_header_callback(Server, on_header);
        nghttp2_session_callbacks_set_on_frame_recv_callback(Server, on_frame);
        nghttp2_session_callbacks_set_on_data_chunk_recv_callback(Server, on_chunk);
        nghttp2_session_callbacks_set_on_stream_close_callback(Server, on_close);
}

bool
H2Open(Conn *c, bool upgrade)
{
        static TyOnce once = TY_ONCE_INIT;
        TyOnceRun(&once, init_callbacks);

        Config const *cfg = &c->L->g->cfg;
        nghttp2_option *opt;

        nghttp2_option_new(&opt);
        nghttp2_option_set_max_settings(opt, 64);

        int err = nghttp2_session_server_new2(&c->h2, Server, c, opt);
        nghttp2_option_del(opt);

        if (err != 0) {
                ConnClose(c);
                return false;
        }

        nghttp2_settings_entry iv[] = {
                { NGHTTP2_SETTINGS_MAX_CONCURRENT_STREAMS, cfg->h2_streams },
                { NGHTTP2_SETTINGS_INITIAL_WINDOW_SIZE,    cfg->h2_window  },
                { NGHTTP2_SETTINGS_MAX_HEADER_LIST_SIZE,   cfg->max_head   },
                { NGHTTP2_SETTINGS_MAX_FRAME_SIZE,         max(16384, min(cfg->h2_frame, 16777215)) }
        };

        nghttp2_submit_settings(c->h2, NGHTTP2_FLAG_NONE, iv, countof(iv));
        nghttp2_session_set_local_window_size(c->h2, NGHTTP2_FLAG_NONE, 0, min(max(cfg->h2_window * 4, 65535), 0x7FFFFFFF));

        c->proto = P_H2;
        c->h2c   = upgrade;
        c->rk    = RT_IDLE;

        ConnTimer(c, TM_READ, cfg->t_idle);
        ConnDirty(c);

        if (BufLen(&c->in) > 0) {
                H2Data(c);
        } else {
                ConnRead(c);
        }

        return true;
}

void
H2Data(Conn *c)
{
        if (c->h2 == NULL || c->closing) {
                return;
        }

        nghttp2_ssize n = nghttp2_session_mem_recv2(c->h2, (u8 const *)BufHead(&c->in), BufLen(&c->in));

        if (n < 0) {
                BufClear(&c->in);
                ConnDirty(c);
                ConnFinish(c);
                return;
        }

        BufEat(&c->in, n);
        ConnDirty(c);

        if (!c->finishing) {
                ConnRead(c);
        }
}

void
H2Flush(Conn *c)
{
        Loop *L = c->L;
        Buf *out = (c->tls != NULL) ? &c->ptx : &c->pend;

        if (c->h2 == NULL) {
                return;
        }

        while (ConnBuffered(c) < (usize)L->g->cfg.high) {
                u8 const *data;
                nghttp2_ssize n = nghttp2_session_mem_send2(c->h2, &data);
                if (n < 0) {
                        ConnClose(c);
                        return;
                }
                if (n == 0) {
                        break;
                }
                BufPut(out, data, n);
        }

        if (c->nx == 0 && !nghttp2_session_want_read(c->h2) && !nghttp2_session_want_write(c->h2)) {
                ConnFinish(c);
        }
}

static void
each_stream(Conn *c, void (*f)(Xch *))
{
        Loop *L = c->L;

        for (usize i = 0; i < vN(L->xs); ++i) {
                Xch *x = v__(L->xs, i);
                if ((x->flags & X_LIVE) && x->c == c && x->sid > 0) {
                        f(x);
                }
        }
}

void
H2Drained(Conn *c)
{
        each_stream(c, XchPump);
        ConnDirty(c);
}

void
H2Timeout(Conn *c, int kind)
{
        if (c->nx == 0) {
                H2Shutdown(c);
                ConnFinish(c);
        } else {
                ConnClose(c);
        }
}

void
H2Shutdown(Conn *c)
{
        if (c->h2 == NULL) {
                return;
        }

        if (c->goaway) {
                return;
        }

        c->goaway = true;

        i32 last = nghttp2_session_get_last_proc_stream_id(c->h2);
        nghttp2_submit_goaway(c->h2, NGHTTP2_FLAG_NONE, last, NGHTTP2_NO_ERROR, NULL, 0);
        ConnDirty(c);

        if (c->nx == 0) {
                ConnFinish(c);
        }
}

static void
abort_stream(Xch *x)
{
        XchClosed(x->L, x);
}

void
H2Closed(Conn *c)
{
        each_stream(c, abort_stream);

        if (c->h2 != NULL) {
                nghttp2_session_del(c->h2);
                c->h2 = NULL;
        }

        c->nx = 0;
}

static int
nv_field(nghttp2_nv *nv, int n, int cap, Value const *k, Value const *v)
{
        if (k->type != VALUE_STRING || hop_by_hop(ss(*k), sN(*k))) {
                return n;
        }

        Value const *xs = (v->type == VALUE_ARRAY) ? vv(*v->array) : v;
        usize nx        = (v->type == VALUE_ARRAY) ? vN(*v->array) : 1;

        for (usize i = 0; i < nx && n < cap; ++i) {
                if (xs[i].type != VALUE_STRING) {
                        continue;
                }
                nv[n++] = (nghttp2_nv) {
                        .name     = (u8 *)ss(*k),
                        .namelen  = sN(*k),
                        .value    = (u8 *)ss(xs[i]),
                        .valuelen = sN(xs[i]),
                        .flags    = NGHTTP2_NV_FLAG_NONE
                };
        }

        return n;
}

bool
H2Head(Xch *x, int status, Value ctype, Value headers, i64 length, bool body)
{
        Conn *c = x->c;
        Loop *L = x->L;
        Config const *cfg = &L->g->cfg;
        char code[8];
        char len[24];
        nghttp2_nv nv[128];
        int n = 0;

        bool bodiless = status < 200 || status == 204 || status == 304;

/* ========================================================================= */
#define NV(k, kn, v, vn) do {                                                          \
        if (n < countof(nv)) {                                                         \
                nv[n++] = (nghttp2_nv) {                                               \
                        .name     = (u8 *)(k),                                         \
                        .namelen  = (kn),                                              \
                        .value    = (u8 *)(v),                                         \
                        .valuelen = (vn),                                              \
                        .flags    = NGHTTP2_NV_FLAG_NONE                               \
                };                                                                     \
        }                                                                              \
} while (0)
#define NVS(k, v, vn) NV((k), sizeof (k) - 1, (v), (vn))
/* ------------------------------------------------------------------------- */
        NVS(":status", code, ty_snprintf(code, sizeof code, "%d", status));
        NVS("date", L->date, L->ndate);

        if (cfg->nserver > 0) {
                NVS("server", cfg->server, cfg->nserver);
        }

        if (!bodiless && ctype.type == VALUE_STRING) {
                NVS("content-type", ss(ctype), sN(ctype));
        }

        if (!bodiless && length >= 0) {
                NVS("content-length", len, ty_snprintf(len, sizeof len, "%"PRIi64, length));
        }

        if (cfg->nridh > 0 && x->nrid > 0) {
                BufClear(&L->tmp);
                for (int i = 0; i < cfg->nridh; ++i) {
                        BufPutc(&L->tmp, cfg->ridh[i] | ((cfg->ridh[i] >= 'A' && cfg->ridh[i] <= 'Z') ? 0x20 : 0));
                }
                NV(BufHead(&L->tmp), cfg->nridh, x->rid, x->nrid);
        }

        if (headers.type == VALUE_DICT) {
                dfor(headers.dict, n = nv_field(nv, n, countof(nv), key, val));
        }
/* ------------------------------------------------------------------------- */
#undef NVS
#undef NV
/* ========================================================================= */

        bool data = body && !bodiless && !(x->flags & X_HEAD_REQ);

        nghttp2_data_provider2 prd = {
                .source.ptr    = x,
                .read_callback = on_read
        };

        if (!data) {
                x->flags |= X_EOF;
        }

        int rc = nghttp2_submit_response2(c->h2, x->sid, nv, n, data ? &prd : NULL);

        x->flags  |= X_STARTED;
        x->status  = status;
        x->length  = length;
        x->last    = L->now;

        if (rc != 0) {
                H2Reset(x, NGHTTP2_INTERNAL_ERROR);
                return false;
        }

        ConnDirty(c);

        return true;
}

void
H2Resume(Xch *x)
{
        if ((x->flags & X_DEFERRED) && x->c != NULL && x->c->h2 != NULL) {
                x->flags &= ~X_DEFERRED;
                nghttp2_session_resume_data(x->c->h2, x->sid);
        }
}

void
H2Chunk(Xch *x, void const *p, usize n)
{
        if (n == 0 || (x->flags & (X_HEAD_REQ | X_EOF))) {
                return;
        }

        BufPut(&x->out, p, n);

        x->sent += n;
        x->last  = x->L->now;

        H2Resume(x);
        ConnDirty(x->c);
}

void
H2End(Xch *x)
{
        if (x->flags & X_ENDED) {
                return;
        }

        x->flags |= X_ENDED | X_EOF;

        Observe(x->L, x);
        H2Resume(x);
        ConnDirty(x->c);
}

void
H2Reset(Xch *x, u32 code)
{
        Conn *c = x->c;

        if (c == NULL || c->h2 == NULL) {
                return;
        }

        nghttp2_submit_rst_stream(c->h2, NGHTTP2_FLAG_NONE, x->sid, code);
        ConnDirty(c);
}

/* vim: set sts=8 sw=8 expandtab: */
