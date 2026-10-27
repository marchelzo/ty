#include <errno.h>
#include <unistd.h>

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"

enum {
        FILE_CHUNK = 256 * 1024
};

inline static bool
open_xch(Xch const *x)
{
        return x != NULL && x->c != NULL && !(x->flags & X_CLOSED) && !x->c->closing;
}

static usize
buffered(Xch const *x)
{
        return open_xch(x) ? ConnBuffered(x->c) + BufLen(&x->out) : 0;
}

static void
chunk(Xch *x, void const *p, usize n)
{
        if (x->sid > 0) {
                H2Chunk(x, p, n);
        } else {
                H1Chunk(x, p, n);
        }
}

static void
finish(Xch *x)
{
        if (x->sid > 0) {
                H2End(x);
        } else {
                H1End(x);
        }
}

static bool
head(Xch *x, int status, Value ctype, Value headers, i64 length, bool body)
{
        return (x->sid > 0) ? H2Head(x, status, ctype, headers, length, body)
             :                H1Head(x, status, ctype, headers, length);
}

static Codec *
encoder(Ty *ty, char const *ctx, Value coding, Value level)
{
        if (coding.type != VALUE_STRING) {
                return NULL;
        }

        char const *err;
        int lvl = (level.type == VALUE_INTEGER) ? level.z
                : MsgIeq(ss(coding), sN(coding), "br")   ? 4
                : MsgIeq(ss(coding), sN(coding), "zstd") ? 3
                :                                          6;

        Codec *z = CodecNew((char const *)ss(coding), sN(coding), true, lvl, &err);

        if (z == NULL) {
                zP("%s: %.*s: %s", ctx, (int)sN(coding), ss(coding), err);
        }

        return z;
}

static void
file_pump(Xch *x)
{
        Loop *L = x->L;

        while (open_xch(x) && x->ffd >= 0 && x->fleft > 0 && buffered(x) < (usize)L->g->cfg.high) {
                usize want = min(x->fleft, FILE_CHUNK);
                char *p = BufRoom(&L->tmp, want);
                isize n;

                do {
                        n = pread(x->ffd, p, want, x->foff);
                } while (n < 0 && errno == EINTR);

                if (n <= 0) {
                        x->fleft = 0;
                        break;
                }

                chunk(x, p, n);

                x->foff  += n;
                x->fleft -= n;
        }

        if (x->ffd >= 0 && x->fleft == 0) {
                close(x->ffd);
                x->ffd = -1;
                if (open_xch(x)) {
                        finish(x);
                }
        }
}

void
XchPump(Xch *x)
{
        if (x->ffd >= 0) {
                file_pump(x);
        }
}

// _http.respond(loop: Ptr, id: Int, status: Int, ctype: String | nil, headers: Dict[String, _] | nil, body: String | Blob | nil, coding: String | nil = nil) -> Bool
TY_BUILTIN(http_respond)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || (x->flags & X_STARTED)) {
                return BOOLEAN(false);
        }

        char const *p;
        usize n;

        p = BytesOf(ty, _name__, body, &n);

        Codec *z = encoder(ty, _name__, coding, NIL);
        Buf zbuf = {0};

        if (z != NULL) {
                if (CodecRun(ty, z, p, n, CODEC_FINISH, (CodecBytes *)&zbuf, false, -1) != CODEC_OK) {
                        CodecFree(z);
                        BufFree(&zbuf);
                        bP("compression failed");
                }
                CodecFree(z);
                p = BufHead(&zbuf);
                n = BufLen(&zbuf);
        }

        bool bodiless = status < 200 || status == 204 || status == 304;

        head(x, status, ctype, headers, bodiless ? -1 : (i64)n, n > 0 && !bodiless && !(x->flags & X_HEAD_REQ));

        if (!bodiless) {
                chunk(x, p, n);
        }

        finish(x);
        BufFree(&zbuf);

        return BOOLEAN(true);
}

// _http.start(loop: Ptr, id: Int, status: Int, ctype: String | nil, headers: Dict[String, _] | nil, length: Int = -1, coding: String | nil = nil, level: Int | nil = nil) -> Bool
TY_BUILTIN(http_start)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || (x->flags & X_STARTED)) {
                return BOOLEAN(false);
        }

        x->z = encoder(ty, _name__, coding, level);

        head(x, status, ctype, headers, length, !(x->flags & X_HEAD_REQ));

        return BOOLEAN(true);
}

// _http.write(loop: Ptr, id: Int, data: String | Blob) -> Int
TY_BUILTIN(http_write)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || (x->flags & X_ENDED) || !(x->flags & X_STARTED)) {
                return INTEGER(-1);
        }

        char const *p;
        usize n;

        p = BytesOf(ty, _name__, data, &n);

        if (x->z != NULL && n > 0) {
                BufClear(&L->tmp);
                if (CodecRun(ty, x->z, p, n, CODEC_FLUSH, (CodecBytes *)&L->tmp, false, -1) != CODEC_OK) {
                        bP("compression failed: %s", CodecError(x->z));
                }
                chunk(x, BufHead(&L->tmp), BufLen(&L->tmp));
        } else if (n > 0) {
                chunk(x, p, n);
        }

        return INTEGER(buffered(x));
}

// _http.end(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_end)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || (x->flags & X_ENDED) || !(x->flags & X_STARTED)) {
                return NIL;
        }

        if (x->ffd >= 0) {
                return NIL;
        }

        if (x->z != NULL) {
                BufClear(&L->tmp);
                CodecRun(ty, x->z, NULL, 0, CODEC_FINISH, (CodecBytes *)&L->tmp, false, -1);
                CodecFree(x->z);
                x->z = NULL;
                chunk(x, BufHead(&L->tmp), BufLen(&L->tmp));
        }

        finish(x);

        return NIL;
}

// _http.abort(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_abort)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x)) {
                return NIL;
        }

        if (x->sid > 0) {
                H2Reset(x, NGHTTP2_INTERNAL_ERROR);
        } else {
                ConnClose(x->c);
        }

        return NIL;
}

// _http.buffered(loop: Ptr, id: Int) -> Int
TY_BUILTIN(http_buffered)
{
        Loop *L = LoopArg(ty, _name__, loop);
        return INTEGER(buffered(XchGet(L, id)));
}

// _http.closed?(loop: Ptr, id: Int) -> Bool
TY_BUILTIN(http_closed)
{
        Loop *L = LoopArg(ty, _name__, loop);
        return BOOLEAN(!open_xch(XchGet(L, id)));
}

// _http.drain(loop: Ptr, id: Int, below: Int) -> Bool
TY_BUILTIN(http_drain)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || buffered(x) <= (usize)max(below, 0)) {
                return BOOLEAN(true);
        }

        if (x->drain < 0) {
                xvP(L->drains, x->slot);
        }

        x->drain = max(below, 0);

        return BOOLEAN(false);
}

// _http.read(loop: Ptr, id: Int, limit: Int) -> String | Int | nil
TY_BUILTIN(http_read)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (x == NULL) {
                return INTEGER(-3);
        }

        if (x->flags & X_REJECTED) {
                return INTEGER(-2);
        }

        usize n = BufLen(&x->body);

        if (n > 0) {
                usize k = min(n, (usize)max(limit, 1));
                Value s = vSs(BufHead(&x->body), k);
                BufEat(&x->body, k);
                if (x->sid == 0 && x->c != NULL && x->c->x == x && BufLen(&x->body) < (usize)L->g->cfg.high) {
                        H1Resume(x->c);
                }
                return s;
        }

        if (x->flags & X_BODY_DONE) {
                return NIL;
        }

        if (!open_xch(x)) {
                return INTEGER(-3);
        }

        x->flags |= X_WAITING;

        if (x->sid == 0 && x->c->x == x) {
                H1Resume(x->c);
        }

        return INTEGER(-1);
}

// _http.buffer(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_buffer)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (x == NULL) {
                return NIL;
        }

        if (x->flags & (X_BODY_DONE | X_REJECTED)) {
                Value body = (x->flags & X_REJECTED) ? INTEGER(413) : vSs(BufHead(&x->body), BufLen(&x->body));
                BufClear(&x->body);
                Emit(L, EV_BODY, XchHandle(x), body, NIL);
                return NIL;
        }

        if (!open_xch(x)) {
                Emit(L, EV_BODY, XchHandle(x), INTEGER(-3), NIL);
                return NIL;
        }

        x->flags |= X_BUFFER;

        if (x->sid == 0 && x->c->x == x) {
                H1Resume(x->c);
        }

        return NIL;
}

// _http.notify(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_notify)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (x == NULL) {
                return NIL;
        }

        x->flags |= X_NOTIFY;

        if (x->flags & X_CLOSED) {
                Emit(L, EV_CLOSE, XchHandle(x), NIL, NIL);
        }

        return NIL;
}

// _http.release(loop: Ptr, id: Int) -> nil
TY_BUILTIN(http_release)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (x == NULL) {
                return NIL;
        }

        x->flags |= X_RELEASED;

        if (x->flags & X_DISPATCHED) {
                Count(L, S_IN_FLIGHT, -1);
        }

        if (x->flags & X_CLOSED) {
                XchDrop(L, x);
                return NIL;
        }

        if (open_xch(x) && !(x->flags & (X_ENDED | X_WS)) && x->ffd < 0) {
                if (x->sid > 0) {
                        H2Reset(x, NGHTTP2_INTERNAL_ERROR);
                } else {
                        ConnClose(x->c);
                }
        }

        return NIL;
}

// _http.send-file(loop: Ptr, id: Int, fd: Int, offset: Int, length: Int) -> Bool
TY_BUILTIN(http_send_file)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || !(x->flags & X_STARTED) || (x->flags & X_ENDED)) {
                close(fd);
                return BOOLEAN(false);
        }

        if (x->flags & X_HEAD_REQ) {
                close(fd);
                finish(x);
                return BOOLEAN(true);
        }

        x->ffd   = fd;
        x->foff  = offset;
        x->fleft = length;

        file_pump(x);

        return BOOLEAN(true);
}

// _http.keepalive(loop: Ptr, id: Int, seconds: Float) -> nil
TY_BUILTIN(http_keepalive)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);

        if (!open_xch(x) || seconds <= 0) {
                return NIL;
        }

        x->ka    = (i64)(seconds * 1000.0);
        x->ka_at = L->now + x->ka;
        x->last  = L->now;

        Arm(L, TK_XCH, x->slot, x->gen, 0, x->ka_at);

        return NIL;
}

// _http.sent(loop: Ptr, id: Int) -> Int
TY_BUILTIN(http_sent)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);
        return INTEGER((x == NULL) ? 0 : x->sent);
}

// _http.version(loop: Ptr, id: Int) -> Int
TY_BUILTIN(http_version)
{
        Loop *L = LoopArg(ty, _name__, loop);
        Xch *x  = XchGet(L, id);
        return INTEGER((x == NULL) ? 0 : x->v);
}

/* vim: set sts=8 sw=8 expandtab: */
