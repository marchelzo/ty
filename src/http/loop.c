#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>

#if defined(__linux__) || defined(__FreeBSD__)
#include <sys/random.h>
#endif

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"

_Thread_local Loop *HttpLoop;

static char const Overloaded[] =
        "HTTP/1.1 503 Service Unavailable\r\n"
        "Content-Type: text/plain\r\n"
        "Content-Length: 19\r\n"
        "Connection: close\r\n"
        "Retry-After: 1\r\n"
        "\r\n"
        "Service Unavailable";

static double const Buckets[] = {
        0.001, 0.0025, 0.005, 0.01, 0.025, 0.05, 0.1, 0.25, 0.5, 1.0, 2.5, 5.0, 10.0
};

void
BufInt(Buf *b, i64 n)
{
        char tmp[24];
        char *p = tmp + sizeof tmp;
        u64 u = (n < 0) ? -(u64)n : (u64)n;

        do {
                *--p = '0' + (u % 10);
                u /= 10;
        } while (u != 0);

        if (n < 0) {
                *--p = '-';
        }

        BufPut(b, p, tmp + sizeof tmp - p);
}

void
BufHex(Buf *b, u64 n)
{
        static char const hex[] = "0123456789abcdef";
        char tmp[16];
        char *p = tmp + sizeof tmp;

        do {
                *--p = hex[n & 15];
                n >>= 4;
        } while (n != 0);

        BufPut(b, p, tmp + sizeof tmp - p);
}

inline static i64
clock_ms(void)
{
        struct timespec ts;
        clock_gettime(CLOCK_MONOTONIC, &ts);
        return (i64)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

inline static i64
clock_us(void)
{
        struct timespec ts;
        clock_gettime(CLOCK_MONOTONIC, &ts);
        return (i64)ts.tv_sec * 1000000 + ts.tv_nsec / 1000;
}

void
LoopTick(Loop *L)
{
        L->now = clock_ms();
}

void
LoopDate(Loop *L)
{
        static char const *const days[]   = { "Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat" };
        static char const *const months[] = { "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec" };
        time_t t = time(NULL);
        struct tm tm;

        if (t == L->dsec) {
                return;
        }

        L->dsec = t;
        gmtime_r(&t, &tm);

        L->ndate = ty_snprintf(
                L->date,
                sizeof L->date,
                "%s, %02d %s %04d %02d:%02d:%02d GMT",
                days[tm.tm_wday],
                tm.tm_mday,
                months[tm.tm_mon],
                tm.tm_year + 1900,
                tm.tm_hour,
                tm.tm_min,
                tm.tm_sec
        );
}

void
Count(Loop *L, int stat, i64 n)
{
        atomic_fetch_add_explicit(&L->st[stat], n, memory_order_relaxed);
}

void
Observe(Loop *L, Xch *x)
{
        double secs = (double)(clock_us() - x->t0) / 1e6;
        int i = 0;

        while (i < countof(Buckets) && secs > Buckets[i]) {
                i += 1;
        }

        Count(L, S_REQUESTS,   1);
        Count(L, S_1XX + min(max(x->status / 100, 1), 5) - 1, 1);
        Count(L, S_BYTES,      x->sent);
        Count(L, S_LATENCY_US, (i64)(secs * 1e6));
        Count(L, S_BUCKET + i, 1);
}

void
Emit(Loop *L, int kind, i64 id, Value a, Value b)
{
        Ty *ty = L->ty;
        Array *evs = L->evs;

        if (vN(*evs) + 4 > vC(*evs)) {
                GC_STOP();
                vvR(*evs, max(vC(*evs) * 2, 64));
                GC_RESUME();
        }

        vPx(*evs, INTEGER(kind));
        vPx(*evs, INTEGER(id));
        vPx(*evs, a);
        vPx(*evs, b);
}

inline static void
pin_at(Loop *L, Array *a, u32 slot, Value v)
{
        Ty *ty = L->ty;

        if (vN(*a) <= slot) {
                GC_STOP();
                while (vN(*a) <= slot) {
                        vAp(a, NIL);
                }
                GC_RESUME();
        }

        v__(*a, slot) = v;
}

void
Pin(Loop *L, Xch *x, Value v)
{
        pin_at(L, L->pins, x->slot, v);
}

Value
Pinned(Loop *L, Xch const *x)
{
        return (x->slot < vN(*L->pins)) ? v__(*L->pins, x->slot) : NIL;
}

void
Unpin(Loop *L, Xch const *x)
{
        if (x->slot < vN(*L->pins)) {
                v__(*L->pins, x->slot) = NIL;
        }
}

static void
heap_up(Loop *L, usize i)
{
        Timer t = v__(L->heap, i);

        while (i > 0) {
                usize p = (i - 1) / 2;
                if (v__(L->heap, p).at <= t.at) {
                        break;
                }
                v__(L->heap, i) = v__(L->heap, p);
                i = p;
        }

        v__(L->heap, i) = t;
}

static void
heap_down(Loop *L, usize i)
{
        usize n = vN(L->heap);
        Timer t = v__(L->heap, i);

        for (;;) {
                usize l = 2 * i + 1;
                usize r = l + 1;
                usize m = i;
                i64 at  = t.at;
                if (l < n && v__(L->heap, l).at < at) {
                        m  = l;
                        at = v__(L->heap, l).at;
                }
                if (r < n && v__(L->heap, r).at < at) {
                        m = r;
                }
                if (m == i) {
                        break;
                }
                v__(L->heap, i) = v__(L->heap, m);
                i = m;
        }

        v__(L->heap, i) = t;
}

void
Arm(Loop *L, int kind, u32 slot, u32 gen, int which, i64 at)
{
        xvP(L->heap, ((Timer) { .at = at, .slot = slot, .gen = gen, .kind = kind, .which = which }));
        heap_up(L, vN(L->heap) - 1);
}

static Timer
heap_pop(Loop *L)
{
        Timer t = v__(L->heap, 0);

        v__(L->heap, 0) = v__(L->heap, vN(L->heap) - 1);
        vN(L->heap) -= 1;

        if (vN(L->heap) > 0) {
                heap_down(L, 0);
        }

        return t;
}

void
ConnTimer(Conn *c, int which, i64 ms)
{
        if (ms <= 0) {
                c->tm[which] = 0;
                return;
        }

        i64 at = c->L->now + ms;

        c->tm[which] = at;

        if (c->tq[which] == 0 || at < c->tq[which]) {
                c->tq[which] = at;
                Arm(c->L, TK_CONN, c->slot, c->gen, which, at);
        }
}

static bool
timer_live(Loop const *L, Timer const *t)
{
        switch (t->kind) {
        case TK_CONN:
                if (t->slot < vN(L->conns)) {
                        Conn const *c = v__(L->conns, t->slot);
                        return c->gen == t->gen && c->fd >= 0 && c->tq[t->which] == t->at;
                }
                return false;

        case TK_XCH:
                if (t->slot < vN(L->xs)) {
                        Xch const *x = v__(L->xs, t->slot);
                        return x->gen == t->gen && (x->flags & X_LIVE) && x->ka_at == t->at;
                }
                return false;

        case TK_USER:
                return t->slot < vN(L->ut) && v_(L->ut, t->slot)->live && v_(L->ut, t->slot)->gen == t->gen;
        }

        return true;
}

static void
heap_compact(Loop *L)
{
        usize n = 0;

        for (usize i = 0; i < vN(L->heap); ++i) {
                if (timer_live(L, v_(L->heap, i))) {
                        v__(L->heap, n++) = v__(L->heap, i);
                }
        }

        vN(L->heap) = n;

        for (usize i = n / 2; i-- > 0;) {
                heap_down(L, i);
        }

        L->live = n;
}

static void
maybe_compact(Loop *L)
{
        if (vN(L->heap) > 4096 && vN(L->heap) > 4 * L->live) {
                heap_compact(L);
        }
}

static Conn *
conn_new(Loop *L)
{
        Conn *c;

        if (vN(L->cfree) > 0) {
                c = v__(L->conns, *vvX(L->cfree));
        } else {
                c = xmA(sizeof *c);
                *c = (Conn) { .L = L, .slot = vN(L->conns), .fd = -1 };
                xvP(L->conns, c);
        }

        c->gen      = (c->gen + 1) & 0xFFFFFF;
        c->fd       = -1;
        c->proto    = P_NEW;
        c->rk       = RT_NONE;
        c->reading  = false;
        c->sending  = false;
        c->eof      = false;
        c->closing  = false;
        c->finishing = false;
        c->notified = false;
        c->linger   = false;
        c->dirty    = false;
        c->paused   = false;
        c->h2c      = false;
        c->goaway   = false;
        c->tls      = NULL;
        c->fed      = 0;
        c->hstate   = 0;
        c->x        = NULL;
        c->h2       = NULL;
        c->ws       = NULL;
        c->reqs     = 0;
        c->nx       = 0;
        c->next     = NULL;
        c->npeer    = 0;
        c->opened   = L->now;
        c->tm[0]    = 0;
        c->tm[1]    = 0;
        c->tm[2]    = 0;
        c->tq[0]    = 0;
        c->tq[1]    = 0;
        c->tq[2]    = 0;

        BufClear(&c->in);
        BufClear(&c->tin);
        BufClear(&c->out);
        BufClear(&c->pend);
        BufClear(&c->ptx);

        return c;
}

static void
conn_release(Conn *c)
{
        Loop *L = c->L;

        if (c->fd >= 0) {
                close(c->fd);
                c->fd = -1;
        }

        TlsFree(c->tls);
        c->tls = NULL;

        if (c->ws != NULL) {
                WsFree(c->ws);
                c->ws = NULL;
        }

        BufShrink(&c->in,   1 << 16);
        BufShrink(&c->tin,  1 << 16);
        BufShrink(&c->out,  1 << 16);
        BufShrink(&c->pend, 1 << 16);
        BufShrink(&c->ptx,  1 << 16);

        c->gen = (c->gen + 1) & 0xFFFFFF;
        xvP(L->cfree, c->slot);

        atomic_fetch_sub(&L->g->active, 1);

        if (!L->accepting && !L->stopping && !L->backoff) {
                IoAccept(L);
        }
}

static void
conn_maybe_release(Conn *c)
{
        if (!c->reading && !c->sending && c->fd >= 0) {
                conn_release(c);
        }
}

void
ConnDirty(Conn *c)
{
        if (!c->dirty && !c->closing) {
                c->dirty  = true;
                c->next   = c->L->dirty;
                c->L->dirty = c;
        }
}

void
ConnWrite(Conn *c, void const *p, usize n)
{
        if (c->closing || c->notified || n == 0) {
                return;
        }

        BufPut((c->tls != NULL) ? &c->ptx : &c->pend, p, n);
        ConnDirty(c);
}

usize
ConnBuffered(Conn const *c)
{
        return BufLen(&c->out) + BufLen(&c->pend) + BufLen(&c->ptx);
}

void
ConnRead(Conn *c)
{
        if (c->reading || c->eof || c->closing || c->paused) {
                return;
        }

        Buf *b = (c->tls != NULL) ? &c->tin : &c->in;
        char *p = BufRoom(b, 16384);

        c->reading = true;
        IoRecv(c->L, c, p, b->capacity - b->count);
}

static void
tls_drain(Conn *c)
{
        usize n;

        while ((n = TlsPending(c->tls)) > 0) {
                char *p = BufRoom(&c->pend, n);
                isize k = TlsDrain(c->tls, p, n);
                if (k <= 0) {
                        break;
                }
                c->pend.count += k;
        }
}

static void
start_send(Conn *c)
{
        if (c->sending || BufLen(&c->pend) == 0) {
                return;
        }

        if (BufLen(&c->out) == 0) {
                BufSwap(&c->out, &c->pend);
                BufClear(&c->pend);
        }

        c->sending = true;
        IoSend(c->L, c, BufHead(&c->out), BufLen(&c->out));
        ConnTimer(c, TM_WRITE, c->L->g->cfg.t_write);
}

static void
finish_step(Conn *c)
{
        if (!c->finishing || c->linger || c->sending || ConnBuffered(c) > 0) {
                return;
        }

        if (c->tls != NULL && !c->notified) {
                c->notified = true;
                TlsShutdown(c->tls);
                tls_drain(c);
                start_send(c);
                if (c->sending) {
                        return;
                }
        }

        if (c->eof) {
                ConnClose(c);
                return;
        }

        shutdown(c->fd, SHUT_WR);

        c->linger = true;
        c->rk     = RT_LINGER;
        c->paused = false;

        ConnTimer(c, TM_READ, c->L->g->cfg.t_linger);
        ConnRead(c);
}

void
ConnFlush(Conn *c)
{
        c->dirty = false;

        if (c->closing) {
                return;
        }

        if (c->proto == P_H2) {
                H2Flush(c);
        }

        if (c->tls != NULL && BufLen(&c->ptx) > 0) {
                isize n = TlsWrite(c->tls, BufHead(&c->ptx), BufLen(&c->ptx));
                if (n < 0) {
                        ConnClose(c);
                        return;
                }
                BufEat(&c->ptx, n);
        }

        if (c->tls != NULL) {
                tls_drain(c);
        }

        start_send(c);
        finish_step(c);
}

void
ConnFinish(Conn *c)
{
        if (c->closing || c->finishing) {
                return;
        }

        c->finishing = true;

        ConnDirty(c);
}

static void
drained(Conn *c)
{
        Loop *L = c->L;

        switch (c->proto) {
        case P_H1: H1Drained(c); break;
        case P_H2: H2Drained(c); break;
        }

        for (usize i = 0; i < vN(L->drains);) {
                Xch *x = v__(L->xs, v__(L->drains, i));
                if (x->c != c || x->drain < 0) {
                        i += 1;
                        continue;
                }
                usize n = ConnBuffered(c) + BufLen(&x->out);
                if ((i64)n > x->drain) {
                        i += 1;
                        continue;
                }
                x->drain = -1;
                v__(L->drains, i) = *vvL(L->drains);
                vN(L->drains) -= 1;
                Emit(L, EV_DRAIN, XchHandle(x), NIL, NIL);
        }
}

void
ConnClose(Conn *c)
{
        if (c->closing) {
                return;
        }

        c->closing = true;
        c->tm[0]   = 0;
        c->tm[1]   = 0;
        c->tm[2]   = 0;

        switch (c->proto) {
        case P_H1: H1Closed(c); break;
        case P_H2: H2Closed(c); break;
        case P_WS: WsClosed(c); break;
        }

        IoKill(c->L, c);

        if (c->L->io != IO_URING) {
                c->reading = false;
                c->sending = false;
        }

        conn_maybe_release(c);
}

static void
dispatch_data(Conn *c)
{
        switch (c->proto) {
        case P_H1: H1Data(c); break;
        case P_H2: H2Data(c); break;
        case P_WS: WsData(c); break;
        }
}

static void
tls_opened(Conn *c)
{
        char const *alpn;
        unsigned n;

        c->tm[TM_READ] = 0;
        c->rk          = RT_NONE;

        if (
                TlsAlpn(c->tls, &alpn, &n)
             && n == 2
             && memcmp(alpn, "h2", 2) == 0
             && c->L->g->cfg.h2
        ) {
                H2Open(c, false);
        } else {
                H1Open(c);
        }
}

static bool
tls_input(Conn *c)
{
        Loop *L = c->L;
        Ty *ty  = L->ty;

        if (!TlsFeed(c->tls, BufHead(&c->tin), BufLen(&c->tin))) {
                ConnClose(c);
                return false;
        }

        BufClear(&c->tin);

        if (!TlsDone(c->tls)) {
                int rc = TlsHandshake(ty, c->tls, &L->g->tls);
                tls_drain(c);
                start_send(c);
                if (rc < 0) {
                        ConnClose(c);
                        return false;
                }
                if (rc == 0) {
                        return false;
                }
                tls_opened(c);
        }

        for (;;) {
                char *p = BufRoom(&c->in, 16384);
                isize k = TlsRead(c->tls, p, c->in.capacity - c->in.count);
                if (k > 0) {
                        c->in.count += k;
                        continue;
                }
                if (k < 0) {
                        c->eof = true;
                }
                break;
        }

        if (TlsPending(c->tls) > 0) {
                ConnDirty(c);
        }

        return true;
}

static void
conn_eof(Conn *c)
{
        switch (c->proto) {
        case P_H1: H1Eof(c);      break;
        default:   ConnClose(c);  break;
        }
}

void
OnRecv(Loop *L, Conn *c, i64 res)
{
        c->reading = false;

        if (c->closing) {
                conn_maybe_release(c);
                return;
        }

        if (res <= 0) {
                c->eof = true;
                if (c->linger || c->finishing || c->proto == P_TLS || c->proto == P_NEW) {
                        ConnClose(c);
                } else {
                        conn_eof(c);
                }
                return;
        }

        if (c->linger) {
                BufClear(&c->in);
                BufClear(&c->tin);
                ConnRead(c);
                return;
        }

        if (c->tls != NULL) {
                c->tin.count += res;
                if (!tls_input(c)) {
                        if (!c->closing) {
                                ConnRead(c);
                        }
                        return;
                }
        } else {
                c->in.count += res;
        }

        dispatch_data(c);

        if (c->eof && !c->closing) {
                conn_eof(c);
        }
}

void
OnSent(Loop *L, Conn *c, i64 res)
{
        c->sending = false;

        if (c->closing) {
                conn_maybe_release(c);
                return;
        }

        if (res < 0) {
                ConnClose(c);
                return;
        }

        BufEat(&c->out, res);

        if (BufLen(&c->out) > 0) {
                c->sending = true;
                IoSend(L, c, BufHead(&c->out), BufLen(&c->out));
                ConnTimer(c, TM_WRITE, L->g->cfg.t_write);
                return;
        }

        if (BufLen(&c->pend) > 0) {
                start_send(c);
        } else {
                c->tm[TM_WRITE] = 0;
        }

        if (!c->sending) {
                drained(c);
        }

        finish_step(c);
}

static void
open_conn(Loop *L, int fd)
{
        Group *g = L->g;
        Conn *c  = conn_new(L);
        int one  = 1;

        c->fd = fd;
        IoPeer(c);
        setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);

        IoOpen(L, c);
        Count(L, S_CONNS_TOTAL, 1);

        if (g->ctx != NULL) {
                c->tls = TlsNew(g->ctx, true, NULL);
                if (c->tls == NULL) {
                        ConnClose(c);
                        return;
                }
                c->proto = P_TLS;
                c->rk    = RT_HANDSHAKE;
                ConnTimer(c, TM_READ, g->cfg.t_handshake);
                ConnRead(c);
        } else {
                H1Open(c);
        }
}

void
OnAccept(Loop *L, i64 res)
{
        Group *g = L->g;

        if (L->io == IO_URING) {
                L->accepting = false;
        }

        if (res < 0) {
                switch (-res) {
                case ECANCELED:
                case EINVAL:
                case EBADF:
                        L->accepting = false;
                        return;

                case EMFILE:
                case ENFILE:
                case ENOBUFS:
                case ENOMEM:
                        IoPause(L);
                        Arm(L, TK_ACCEPT, 0, 0, 0, L->now + 100);
                        return;
                }
                if (L->io == IO_URING && !L->stopping) {
                        IoAccept(L);
                }
                return;
        }

        int fd = res;

        if (L->stopping) {
                close(fd);
                return;
        }

        if (atomic_fetch_add(&g->active, 1) >= g->cfg.max_conns) {
                atomic_fetch_sub(&g->active, 1);
                Count(L, S_REJECTED, 1);
                if (g->ctx == NULL) {
                        (void)!send(fd, Overloaded, sizeof Overloaded - 1, HTTP_SEND_FLAGS);
                }
                close(fd);
        } else {
                open_conn(L, fd);
        }

        if (L->io == IO_URING && !L->stopping) {
                IoAccept(L);
        }
}

static void
begin_stop(Loop *L)
{
        if (L->stopping) {
                return;
        }

        L->stopping = true;
        L->stop_at  = L->now + L->g->cfg.t_shutdown;

        IoCancelAccept(L);

        Arm(L, TK_ACCEPT, 1, 0, 0, L->stop_at);

        for (usize i = 0; i < vN(L->conns); ++i) {
                Conn *c = v__(L->conns, i);
                if (c->fd < 0 || c->closing) {
                        continue;
                }
                switch (c->proto) {
                case P_H1: H1Shutdown(c); break;
                case P_H2: H2Shutdown(c); break;
                case P_WS: WsShutdown(c); break;
                default:   ConnClose(c);  break;
                }
        }
}

static void
force_stop(Loop *L)
{
        for (usize i = 0; i < vN(L->conns); ++i) {
                Conn *c = v__(L->conns, i);
                if (c->fd >= 0 && !c->closing) {
                        ConnClose(c);
                }
        }
}

void
LoopNotify(Loop *L, i64 timer)
{
        TyMutexLock(&L->nmu);
        xvP(L->notes, timer);
        TyMutexUnlock(&L->nmu);

        atomic_store(&L->woken, 0);
        IoWake(L);
}

static void
fire_user(Loop *L, u32 slot, u32 gen)
{
        if (slot >= vN(L->ut)) {
                return;
        }

        UTimer *u = v_(L->ut, slot);

        if (!u->live || u->gen != gen) {
                return;
        }

        u->live = false;
        u->gen += 1;
        xvP(L->utfree, slot);

        u32 i = 2 * slot;
        Value tok = (i < vN(*L->tokens)) ? v__(*L->tokens, i) : NIL;

        if (i < vN(*L->tokens)) {
                v__(*L->tokens, i) = NIL;
        }

        Emit(L, EV_TIMER, 0, tok, NIL);
}

void
OnWake(Loop *L)
{
        atomic_store(&L->woken, 0);

        TyMutexLock(&L->nmu);
        i64 *notes = vv(L->notes);
        usize n    = vN(L->notes);
        v00(L->notes);
        TyMutexUnlock(&L->nmu);

        for (usize i = 0; i < n; ++i) {
                fire_user(L, (u32)notes[i], (u32)(notes[i] >> 32));
        }

        xmF(notes);

        if (atomic_load(&L->stop) && !L->stopping) {
                begin_stop(L);
        }

        Emit(L, EV_WAKE, 0, NIL, NIL);
}

void
OnWatch(Loop *L, u32 slot, u32 gen, i64 revents)
{
        if (slot >= vN(L->wt)) {
                return;
        }

        Watch *w = v_(L->wt, slot);

        if (!w->live || (w->gen & 0xFFFFFF) != (gen & 0xFFFFFF)) {
                return;
        }

        w->live = false;
        w->gen += 1;
        xvP(L->wtfree, slot);

        u32 i = 2 * slot + 1;
        Value tok = (i < vN(*L->tokens)) ? v__(*L->tokens, i) : NIL;

        if (i < vN(*L->tokens)) {
                v__(*L->tokens, i) = NIL;
        }

        Emit(L, EV_FD, revents, tok, NIL);
}

static void
conn_timeout(Conn *c, int which)
{
        if (which == TM_WRITE) {
                ConnClose(c);
                return;
        }

        if (which == TM_AUX) {
                if (c->proto == P_WS) {
                        WsPing(c);
                }
                return;
        }

        switch (c->rk) {
        case RT_HEADER:
        case RT_REQUEST:
                if (c->proto == P_H1) {
                        H1Timeout(c, c->rk);
                        return;
                }
                break;

        case RT_IDLE:
                if (c->proto == P_H2) {
                        H2Timeout(c, c->rk);
                        return;
                }
                break;

        case RT_WS:
                if (c->proto == P_WS) {
                        WsTimeout(c, c->rk);
                        return;
                }
                break;
        }

        ConnClose(c);
}

static void
xch_keepalive(Loop *L, Xch *x)
{
        if (x->ka <= 0 || (x->flags & (X_ENDED | X_CLOSED)) || x->c == NULL) {
                return;
        }

        if (L->now - x->last >= x->ka && ConnBuffered(x->c) == 0) {
                if (x->sid > 0) {
                        H2Chunk(x, ":\n\n", 3);
                } else {
                        H1Chunk(x, ":\n\n", 3);
                }
                x->last = L->now;
        }

        x->ka_at = max(x->last, L->now - x->ka) + x->ka;
        Arm(L, TK_XCH, x->slot, x->gen, 0, x->ka_at);
}

static void
fire(Loop *L)
{
        maybe_compact(L);

        while (vN(L->heap) > 0 && v__(L->heap, 0).at <= L->now) {
                Timer t = heap_pop(L);

                switch (t.kind) {
                case TK_CONN:
                        if (t.slot < vN(L->conns)) {
                                Conn *c = v__(L->conns, t.slot);
                                if (c->gen != t.gen || c->fd < 0 || c->closing || c->tq[t.which] != t.at) {
                                        break;
                                }
                                c->tq[t.which] = 0;
                                if (c->tm[t.which] == 0) {
                                        break;
                                }
                                if (c->tm[t.which] > L->now) {
                                        c->tq[t.which] = c->tm[t.which];
                                        Arm(L, TK_CONN, c->slot, c->gen, t.which, c->tm[t.which]);
                                        break;
                                }
                                c->tm[t.which] = 0;
                                conn_timeout(c, t.which);
                        }
                        break;

                case TK_XCH:
                        if (t.slot < vN(L->xs)) {
                                Xch *x = v__(L->xs, t.slot);
                                if (x->gen == t.gen && (x->flags & X_LIVE) && x->ka_at == t.at) {
                                        xch_keepalive(L, x);
                                }
                        }
                        break;

                case TK_USER:
                        fire_user(L, t.slot, t.gen);
                        break;

                case TK_ACCEPT:
                        if (t.slot == 1) {
                                if (L->stopping) {
                                        force_stop(L);
                                }
                        } else if (!L->stopping) {
                                L->accepting = false;
                                IoAccept(L);
                        }
                        break;
                }
        }
}

static void
flush_all(Loop *L)
{
        while (L->dirty != NULL) {
                Conn *c  = L->dirty;
                L->dirty = NULL;
                while (c != NULL) {
                        Conn *next = c->next;
                        c->next = NULL;
                        if (c->dirty) {
                                ConnFlush(c);
                        }
                        c = next;
                }
        }
}

static bool
idle(Loop const *L)
{
        if (L->accepting) {
                return false;
        }

        for (usize i = 0; i < vN(L->conns); ++i) {
                if (v__(L->conns, i)->fd >= 0) {
                        return false;
                }
        }

        return true;
}

Xch *
XchNew(Loop *L, Conn *c)
{
        Xch *x;

        if (vN(L->xfree) > 0) {
                x = v__(L->xs, *vvX(L->xfree));
        } else {
                x = xmA(sizeof *x);
                *x = (Xch) { .L = L, .slot = vN(L->xs), .ffd = -1 };
                xvP(L->xs, x);
        }

        x->gen    = (x->gen + 1) & 0x7FFFFFFF;
        x->c      = c;
        x->cgen   = (c != NULL) ? c->gen : 0;
        x->sid    = 0;
        x->flags  = X_LIVE;
        x->v      = 11;
        x->span   = 0;
        x->status = 0;
        x->method    = (Span) {0};
        x->target    = (Span) {0};
        x->scheme    = (Span) {0};
        x->authority = (Span) {0};
        x->hlen   = 0;
        x->clen   = -1;
        x->got    = 0;
        x->sent   = 0;
        x->length = -1;
        x->t0     = clock_us();
        x->drain  = -1;
        x->ka     = 0;
        x->ka_at  = 0;
        x->last   = L->now;
        x->z      = NULL;
        x->ffd    = -1;
        x->foff   = 0;
        x->fleft  = 0;
        x->nrid   = 0;

        v0(x->hs);
        BufClear(&x->hd);
        BufClear(&x->body);
        BufClear(&x->out);

        return x;
}

void
XchDispatch(Loop *L, Xch *x, Value req, bool pending)
{
        if (x->c != NULL) {
                x->c->reqs += 1;
        }

        x->flags |= X_DISPATCHED;
        Count(L, S_IN_FLIGHT, 1);

        Emit(L, EV_REQUEST, XchHandle(x), req, INTEGER(pending));
}

Xch *
XchGet(Loop *L, i64 id)
{
        u32 slot = (u32)id;
        u32 gen  = (u32)(id >> 32);

        if (slot >= vN(L->xs)) {
                return NULL;
        }

        Xch *x = v__(L->xs, slot);

        return (x->gen == gen && (x->flags & X_LIVE)) ? x : NULL;
}

void
XchDrop(Loop *L, Xch *x)
{
        if (!(x->flags & X_LIVE)) {
                return;
        }

        Unpin(L, x);

        if (x->drain >= 0) {
                for (usize i = 0; i < vN(L->drains); ++i) {
                        if (v__(L->drains, i) == x->slot) {
                                v__(L->drains, i) = *vvL(L->drains);
                                vN(L->drains) -= 1;
                                break;
                        }
                }
        }

        if (x->ffd >= 0) {
                close(x->ffd);
                x->ffd = -1;
        }

        CodecFree(x->z);

        x->z     = NULL;
        x->flags = 0;
        x->c     = NULL;
        x->gen   = (x->gen + 1) & 0x7FFFFFFF;

        BufShrink(&x->hd,   1 << 14);
        BufShrink(&x->body, 1 << 16);
        BufShrink(&x->out,  1 << 16);

        if (vC(x->hs) > 256) {
                xvF(x->hs);
                v00(x->hs);
        }

        xvP(L->xfree, x->slot);
}

void
XchClosed(Loop *L, Xch *x)
{
        if (!(x->flags & X_LIVE) || (x->flags & X_CLOSED)) {
                return;
        }

        bool aborted = !(x->flags & X_ENDED);

        x->flags |= X_CLOSED;
        x->c      = NULL;

        if (x->ffd >= 0) {
                close(x->ffd);
                x->ffd = -1;
        }

        if (!(x->flags & X_DISPATCHED)) {
                XchDrop(L, x);
                return;
        }

        if (aborted) {
                Count(L, S_ABORTED, 1);
        }

        if (x->flags & X_RELEASED) {
                XchDrop(L, x);
                return;
        }

        if (aborted || (x->flags & X_NOTIFY)) {
                Emit(L, EV_CLOSE, XchHandle(x), NIL, NIL);
        }
}

static void
read_config(Ty *ty, Config *cfg, Dict *d)
{
/* ========================================================================= */
#define I(f, k) do {                                                             \
        Value *v = dict_get_member(ty, d, k);                                    \
        cfg->f = (v != NULL && v->type == VALUE_INTEGER) ? v->z : cfg->f;        \
} while (0)
#define T(f, k) do {                                                             \
        Value *v = dict_get_member(ty, d, k);                                    \
        cfg->f = (v == NULL)                ? cfg->f                             \
               : (v->type == VALUE_REAL)    ? (i64)(v->real * 1000.0)            \
               : (v->type == VALUE_INTEGER) ? v->z * 1000                        \
               :                              cfg->f;                            \
} while (0)
#define B(f, k) do {                                                             \
        Value *v = dict_get_member(ty, d, k);                                    \
        cfg->f = (v != NULL && v->type == VALUE_BOOLEAN) ? v->boolean : cfg->f;  \
} while (0)
#define S(f, k) do {                                                             \
        Value *v = dict_get_member(ty, d, k);                                    \
        if (v != NULL && v->type == VALUE_STRING) {                              \
                cfg->n##f = min(sN(*v), sizeof cfg->f);                          \
                memcpy(cfg->f, ss(*v), cfg->n##f);                               \
        }                                                                        \
} while (0)
/* ------------------------------------------------------------------------- */
        I(max_conns,   "maxConnections");
        I(max_head,    "maxHeaderSize");
        I(max_headers, "maxHeaders");
        I(max_body,    "maxBodySize");
        I(max_reqs,    "maxRequestsPerConnection");
        I(max_wbuf,    "maxWriteBuffer");
        I(high,        "writeHighWater");
        I(ws_max,      "wsMaxMessage");
        I(ws_zmin,     "wsCompressMin");
        I(h2_streams,  "h2MaxConcurrentStreams");
        I(h2_window,   "h2InitialWindow");
        I(h2_frame,    "h2MaxFrame");
        T(t_header,    "headerTimeout");
        T(t_request,   "requestTimeout");
        T(t_idle,      "idleTimeout");
        T(t_write,     "writeTimeout");
        T(t_handshake, "handshakeTimeout");
        T(t_linger,    "lingerTimeout");
        T(t_shutdown,  "shutdownTimeout");
        T(t_ws_ping,   "wsPingInterval");
        T(t_ws_idle,   "wsIdleTimeout");
        B(ws_z,        "wsCompression");
        B(h2,          "h2");
        B(trust_rid,   "trustRequestId");
        S(server,      "serverName");
        S(ridh,        "requestIdHeader");
/* ------------------------------------------------------------------------- */
#undef S
#undef B
#undef T
#undef I
/* ========================================================================= */
}

static void
random_hex(char *out, usize n)
{
        static char const hex[] = "0123456789abcdef";
        u8 raw[16];

#if defined(__linux__) || defined(__FreeBSD__)
        while (getrandom(raw, sizeof raw, 0) != sizeof raw) {
                continue;
        }
#else
        arc4random_buf(raw, sizeof raw);
#endif

        for (usize i = 0; i < n; ++i) {
                out[i] = hex[(raw[i / 2] >> ((i & 1) ? 0 : 4)) & 15];
        }
}

static void
group_free(void *p)
{
        xmF(p);
}

static Value
autoptr(Ty *ty, void *p, void (*dtor)(void *))
{
        Value *d = mAo(sizeof (Value [2]), GC_FFI_AUTO);

        d[0] = PTR((void *)dtor);
        d[1] = PTR(p);

        return GCPTR(p, d);
}

// _http.group(listen: Int, config: Dict[String, _], tls: Ptr | nil = nil, context: _ = nil) -> Ptr
TY_BUILTIN(http_group)
{
        if (config.type != VALUE_DICT) {
                TyBuiltinBadArg(ty, _name__, "config", "Dict", &config);
        }

        Group *g = xmA(sizeof *g);

        *g = (Group) {
                .lfd = listen,
                .tls = NIL,
                .cfg = {
                        .max_conns   = 10000,
                        .max_head    = 64 * 1024,
                        .max_headers = 100,
                        .max_body    = 16 * 1024 * 1024,
                        .max_wbuf    = 8 * 1024 * 1024,
                        .high        = 256 * 1024,
                        .ws_max      = 16 * 1024 * 1024,
                        .ws_zmin     = 256,
                        .h2_streams  = 128,
                        .h2_window   = 1024 * 1024,
                        .h2_frame    = 16384,
                        .t_header    = 10000,
                        .t_request   = 60000,
                        .t_idle      = 60000,
                        .t_write     = 60000,
                        .t_handshake = 10000,
                        .t_linger    = 2000,
                        .t_shutdown  = 10000,
                        .t_ws_ping   = 30000,
                        .t_ws_idle   = 120000,
                        .ws_z        = true,
                        .h2          = true,
                        .trust_rid   = true
                }
        };

        read_config(ty, &g->cfg, config.dict);
        random_hex(g->rid, 8);

        if (tls.type == VALUE_PTR && tls.ptr != NULL) {
                g->ctx = tls.ptr;
                g->tls = context;
        }

        return autoptr(ty, g, group_free);
}

// _http.streams(group: Ptr, on: Bool) -> nil
TY_BUILTIN(http_streams)
{
        atomic_store(&((Group *)PtrArg(ty, _name__, "group", group))->streams, on);
        return NIL;
}

// _http.active(group: Ptr) -> Int
TY_BUILTIN(http_active)
{
        return INTEGER(atomic_load(&((Group *)PtrArg(ty, _name__, "group", group))->active));
}

// _http.loop(group: Ptr, index: Int, evs: Array[_], pins: Array[_], tokens: Array[_]) -> Ptr
TY_BUILTIN(http_loop)
{
        Group *g = PtrArg(ty, _name__, "group", group);

        if (evs.type != VALUE_ARRAY || pins.type != VALUE_ARRAY || tokens.type != VALUE_ARRAY) {
                bP("evs, pins and tokens must be arrays");
        }

        Loop *L = xmA(sizeof *L);

        *L = (Loop) {
                .g      = g,
                .ty     = ty,
                .index  = index,
                .pfd    = -1,
                .efd    = -1,
                .wfd    = -1,
                .evs    = evs.array,
                .pins   = pins.array,
                .tokens = tokens.array,
                .now    = clock_ms()
        };

        TyMutexInit(&L->nmu);

        int err = IoInit(L);

        if (err < 0) {
                IoFree(L);
                xmF(L);
                bP("%s", strerror(-err));
        }

        LoopDate(L);

        return PTR(L);
}

// _http.backend(loop: Ptr) -> String
TY_BUILTIN(http_backend)
{
        return xSz(IoName(PtrArg(ty, _name__, "loop", loop)));
}

// _http.listen(loop: Ptr) -> nil
TY_BUILTIN(http_listen)
{
        Loop *L = LoopArg(ty, _name__, loop);

        HttpLoop = L;

        if (!atomic_load(&L->stop)) {
                IoAccept(L);
        }

        return NIL;
}

// _http.poll(loop: Ptr, timeout: Float = -1.0) -> Int
TY_BUILTIN(http_poll)
{
        Loop *L = LoopArg(ty, _name__, loop);

        HttpLoop = L;
        L->now   = clock_ms();

        if (atomic_load(&L->stop) && !L->stopping) {
                begin_stop(L);
        }

        LoopDate(L);
        fire(L);
        flush_all(L);

        if (L->stopping && idle(L)) {
                L->done = true;
                return INTEGER((vN(*L->evs) > 0) ? (i64)vN(*L->evs) / 4 : -1);
        }

        i64 ms = (timeout < 0) ? 1000 : (i64)(timeout * 1000.0);

        if (vN(L->heap) > 0) {
                ms = min(ms, max(v__(L->heap, 0).at - L->now, 0));
        }

        if (vN(*L->evs) > 0) {
                ms = 0;
        }

        int rc = IoWait(L, ms);

        if (rc < 0 && rc != -EINTR) {
                bP("%s", strerror(-rc));
        }

        L->now = clock_ms();

        fire(L);
        flush_all(L);

        return INTEGER(vN(*L->evs) / 4);
}

// _http.flush(loop: Ptr) -> nil
TY_BUILTIN(http_flush)
{
        flush_all(LoopArg(ty, _name__, loop));
        return NIL;
}

// _http.stop(loop: Ptr) -> nil
TY_BUILTIN(http_stop)
{
        Loop *L = PtrArg(ty, _name__, "loop", loop);

        atomic_store(&L->stop, 1);
        atomic_store(&L->woken, 0);
        IoWake(L);

        return NIL;
}

// _http.wake(loop: Ptr) -> nil
TY_BUILTIN(http_wake)
{
        IoWake(PtrArg(ty, _name__, "loop", loop));

        return NIL;
}

// _http.stopping?(loop: Ptr) -> Bool
TY_BUILTIN(http_stopping)
{
        Loop *L = PtrArg(ty, _name__, "loop", loop);
        return BOOLEAN(L->stopping || atomic_load(&L->stop));
}

// _http.wait-fd(fd: Int, events: Int, timeout: Float = -1.0) -> Bool
TY_BUILTIN(http_wait_fd)
{
        struct pollfd p = { .fd = fd, .events = events };
        int ms = (timeout < 0) ? -1 : (int)min(timeout * 1000.0, INT32_MAX);
        int rc;

        UnlockTy();
        do {
                rc = poll(&p, 1, ms);
        } while (rc < 0 && errno == EINTR);
        LockTy();

        return BOOLEAN(rc > 0);
}

// _http.free(loop: Ptr) -> nil
TY_BUILTIN(http_free)
{
        Loop *L = LoopArg(ty, _name__, loop);

        for (usize i = 0; i < vN(L->conns); ++i) {
                Conn *c = v__(L->conns, i);
                if (c->fd >= 0) {
                        close(c->fd);
                        atomic_fetch_sub(&L->g->active, 1);
                }
                if (c->h2 != NULL) {
                        nghttp2_session_del(c->h2);
                }
                TlsFree(c->tls);
                if (c->ws != NULL) {
                        WsFree(c->ws);
                }
                BufFree(&c->in);
                BufFree(&c->tin);
                BufFree(&c->out);
                BufFree(&c->pend);
                BufFree(&c->ptx);
                xmF(c);
        }

        for (usize i = 0; i < vN(L->xs); ++i) {
                Xch *x = v__(L->xs, i);
                if (x->ffd >= 0) {
                        close(x->ffd);
                }
                CodecFree(x->z);
                BufFree(&x->hd);
                BufFree(&x->body);
                BufFree(&x->out);
                xvF(x->hs);
                xmF(x);
        }

        IoFree(L);

        xvF(L->conns);
        xvF(L->cfree);
        xvF(L->xs);
        xvF(L->xfree);
        xvF(L->heap);
        xvF(L->ut);
        xvF(L->utfree);
        xvF(L->wt);
        xvF(L->wtfree);
        xvF(L->ready);
        xvF(L->drains);
        xvF(L->notes);
        TyMutexDestroy(&L->nmu);
        BufFree(&L->tmp);

        if (HttpLoop == L) {
                HttpLoop = NULL;
        }

        xmF(L);

        return NIL;
}

// _http.stats(loop: Ptr, out: Array[Int]) -> Array[Int]
TY_BUILTIN(http_stats)
{
        Loop *L = PtrArg(ty, _name__, "loop", loop);

        if (out.type != VALUE_ARRAY) {
                TyBuiltinBadArg(ty, _name__, "out", "Array", &out);
        }

        for (int i = 0; i < S_N; ++i) {
                i64 n = atomic_load_explicit(&L->st[i], memory_order_relaxed);
                if (i < vN(*out.array)) {
                        Value *v = v_(*out.array, i);
                        *v = INTEGER(((v->type == VALUE_INTEGER) ? v->z : 0) + n);
                } else {
                        vAp(out.array, INTEGER(n));
                }
        }

        return out;
}

// _http.count(loop: Ptr, stat: Int, n: Int = 1) -> nil
TY_BUILTIN(http_count)
{
        if (stat < 0 || stat >= S_N) {
                bP("bad stat: %"PRIi64, stat);
        }

        Count(LoopArg(ty, _name__, loop), stat, n);

        return NIL;
}

// _http.timer(loop: Ptr, seconds: Float, token: _) -> Int
TY_BUILTIN(http_timer)
{
        Loop *L = LoopArg(ty, _name__, loop);
        u32 slot;

        if (vN(L->utfree) > 0) {
                slot = *vvX(L->utfree);
        } else {
                slot = vN(L->ut);
                xvP(L->ut, ((UTimer) {0}));
        }

        UTimer *u = v_(L->ut, slot);

        u->live = true;
        u->gen  = (u->gen + 1) & 0x7FFFFFFF;

        pin_at(L, L->tokens, 2 * slot, token);

        L->now = clock_ms();
        Arm(L, TK_USER, slot, u->gen, 0, L->now + max((i64)(seconds * 1000.0), 0));

        return INTEGER(((i64)u->gen << 32) | slot);
}

// _http.untimer(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_untimer)
{
        Loop *L = LoopArg(ty, _name__, loop);
        u32 slot = (u32)id;
        u32 gen  = (u32)(id >> 32);

        if (slot < vN(L->ut)) {
                UTimer *u = v_(L->ut, slot);
                if (u->live && u->gen == gen) {
                        u->live = false;
                        u->gen += 1;
                        xvP(L->utfree, slot);
                        if (2 * slot < vN(*L->tokens)) {
                                v__(*L->tokens, 2 * slot) = NIL;
                        }
                }
        }

        return NIL;
}

// _http.watch(loop: Ptr, fd: Int, events: Int, token: _) -> Int
TY_BUILTIN(http_watch)
{
        Loop *L = LoopArg(ty, _name__, loop);
        u32 slot;

        if (vN(L->wtfree) > 0) {
                slot = *vvX(L->wtfree);
        } else {
                slot = vN(L->wt);
                xvP(L->wt, ((Watch) {0}));
        }

        Watch *w = v_(L->wt, slot);

        w->live = true;
        w->fd   = fd;
        w->gen  = (w->gen + 1) & 0xFFFFFF;

        int rc = IoWatch(L, slot, fd, events);

        if (rc < 0) {
                w->live = false;
                xvP(L->wtfree, slot);
                return INTEGER(rc);
        }

        pin_at(L, L->tokens, 2 * slot + 1, token);

        return INTEGER(((i64)w->gen << 32) | slot);
}

// _http.unwatch(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_unwatch)
{
        Loop *L = LoopArg(ty, _name__, loop);
        u32 slot = (u32)id;
        u32 gen  = (u32)(id >> 32);

        if (slot < vN(L->wt)) {
                Watch *w = v_(L->wt, slot);
                if (w->live && w->gen == gen) {
                        IoUnwatch(L, slot, w->fd);
                        w->live = false;
                        w->gen  = (w->gen + 1) & 0xFFFFFF;
                        xvP(L->wtfree, slot);
                        if (2 * slot + 1 < vN(*L->tokens)) {
                                v__(*L->tokens, 2 * slot + 1) = NIL;
                        }
                }
        }

        return NIL;
}

/* vim: set sts=8 sw=8 expandtab: */
