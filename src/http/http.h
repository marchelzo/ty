#ifndef HTTP_INTERNAL_H_INCLUDED
#define HTTP_INTERNAL_H_INCLUDED

#include <stdarg.h>
#include <string.h>
#include <sys/socket.h>

#include <llhttp.h>
#include <nghttp2/nghttp2.h>

#include "polyfill_stdatomic.h"
#include "ty.h"
#include "value.h"
#include "codec.h"
#include "tls.h"

#if defined(__APPLE__)
 #define HTTP_SEND_FLAGS 0
#else
 #define HTTP_SEND_FLAGS MSG_NOSIGNAL
#endif

typedef struct group Group;
typedef struct loop  Loop;
typedef struct conn  Conn;
typedef struct xch   Xch;
typedef struct ws    Ws;
typedef struct ring  Ring;

typedef struct {
        char  *items;
        usize  count;
        usize  capacity;
        usize  off;
} Buf;

enum {
        IO_URING = 1,
        IO_EPOLL,
        IO_KQUEUE
};

enum {
        P_NEW,
        P_TLS,
        P_H1,
        P_H2,
        P_WS
};

enum {
        RT_NONE,
        RT_HANDSHAKE,
        RT_IDLE,
        RT_HEADER,
        RT_REQUEST,
        RT_WS,
        RT_CLOSING,
        RT_LINGER
};

enum {
        TM_READ,
        TM_WRITE,
        TM_AUX
};

enum {
        TK_CONN,
        TK_XCH,
        TK_USER,
        TK_ACCEPT
};

enum {
        EV_REQUEST = 1,
        EV_BODY,
        EV_READABLE,
        EV_DRAIN,
        EV_CLOSE,
        EV_MESSAGE,
        EV_TIMER,
        EV_FD,
        EV_WAKE
};

enum {
        X_LIVE       = 1 << 0,
        X_DISPATCHED = 1 << 1,
        X_RELEASED   = 1 << 2,
        X_STARTED    = 1 << 3,
        X_ENDED      = 1 << 4,
        X_CLOSED     = 1 << 5,
        X_NOTIFY     = 1 << 6,
        X_STREAM     = 1 << 7,
        X_BUFFER     = 1 << 8,
        X_BODY_DONE  = 1 << 9,
        X_HEAD_REQ   = 1 << 10,
        X_CHUNKED    = 1 << 11,
        X_KEEP       = 1 << 12,
        X_UPGRADE    = 1 << 13,
        X_HEAD_DONE  = 1 << 14,
        X_DEFERRED   = 1 << 15,
        X_REJECTED   = 1 << 16,
        X_WS         = 1 << 17,
        X_EOF        = 1 << 18,
        X_PAUSED     = 1 << 19,
        X_HOST       = 1 << 20,
        X_WAITING    = 1 << 21,
        X_UPGRADED   = 1 << 22,
        X_CONTINUE   = 1 << 23,
        X_CLOSE      = 1 << 24
};

enum {
        HS_IDLE,
        HS_HEAD,
        HS_HEAD_DONE,
        HS_BODY,
        HS_DONE
};

enum {
        S_REQUESTS,
        S_1XX,
        S_2XX,
        S_3XX,
        S_4XX,
        S_5XX,
        S_BYTES,
        S_ERRORS,
        S_ABORTED,
        S_IN_FLIGHT,
        S_WS,
        S_WS_TOTAL,
        S_CONNS_TOTAL,
        S_REJECTED,
        S_LATENCY_US,
        S_BUCKET,
        S_N = S_BUCKET + 14
};

typedef struct {
        i64  max_conns;
        i64  max_head;
        i64  max_headers;
        i64  max_body;
        i64  max_reqs;
        i64  max_wbuf;
        i64  high;
        i64  ws_max;
        i64  ws_zmin;
        i64  h2_streams;
        i64  h2_window;
        i64  h2_frame;
        i64  t_header;
        i64  t_request;
        i64  t_idle;
        i64  t_write;
        i64  t_handshake;
        i64  t_linger;
        i64  t_shutdown;
        i64  t_ws_ping;
        i64  t_ws_idle;
        bool ws_z;
        bool h2;
        bool trust_rid;
        u8   nserver;
        u8   nridh;
        char server[64];
        char ridh[64];
} Config;

struct group {
        Config      cfg;
        int         lfd;
        void       *ctx;
        Value       tls;
        atomic_long active;
        atomic_int  streams;
        char        rid[9];
};

typedef struct {
        i64 at;
        u32 slot;
        u32 gen;
        u8  kind;
        u8  which;
} Timer;

typedef struct {
        u32   gen;
        bool  live;
        Value token;
} UTimer;

typedef struct {
        u32  gen;
        bool live;
        int  fd;
        i64  token;
} Watch;

typedef struct {
        u32  slot;
        u32  gen;
        u8   op;
        i64  res;
} Done;

struct conn {
        Loop            *L;
        u32              slot;
        u32              gen;
        int              fd;
        u8               proto;
        u8               rk;
        bool             reading;
        bool             sending;
        bool             rready;
        bool             wready;
        bool             eof;
        bool             closing;
        bool             finishing;
        bool             notified;
        bool             linger;
        bool             dirty;
        bool             paused;
        bool             h2c;
        bool             goaway;
        bool             watched;
        Tls             *tls;
        char            *rp;
        usize            rn;
        char const      *sp;
        usize            sn;
        Buf              in;
        Buf              tin;
        Buf              out;
        Buf              pend;
        Buf              ptx;
        i64              tm[3];
        i64              tq[3];
        llhttp_t         p;
        u32              fed;
        u8               hstate;
        Xch             *x;
        nghttp2_session *h2;
        Ws              *ws;
        u32              reqs;
        u32              nx;
        i64              opened;
        Conn            *next;
        u8               npeer;
        char             peer[64];
};

typedef struct {
        u32 off;
        u32 len;
} Span;

struct xch {
        Loop    *L;
        u32      slot;
        u32      gen;
        Conn    *c;
        u32      cgen;
        i32      sid;
        u32      flags;
        u8       v;
        u8       span;
        int      status;
        Span     method;
        Span     target;
        Span     scheme;
        Span     authority;
        vec(Span) hs;
        Buf      hd;
        u32      hlen;
        i64      clen;
        i64      got;
        Buf      body;
        Buf      out;
        i64      sent;
        i64      length;
        i64      t0;
        i64      drain;
        i64      ka;
        i64      ka_at;
        i64      last;
        Codec   *z;
        int      ffd;
        i64      foff;
        i64      fleft;
        u8       nrid;
        char     rid[136];
};

struct loop {
        Group       *g;
        Ty          *ty;
        int          io;
        int          index;
        int          pfd;
        Ring        *ring;
        int          efd;
        int          wfd;
        u64          ebuf;
        bool         armed_wake;
        atomic_int   woken;
        atomic_int   stop;
        bool         stopping;
        bool         done;
        bool         accepting;
        bool         backoff;
        i64          now;
        i64          stop_at;
        i64          dsec;
        u8           ndate;
        char         date[32];
        vec(Conn *)  conns;
        vec(u32)     cfree;
        vec(Xch *)   xs;
        vec(u32)     xfree;
        vec(Timer)   heap;
        usize        live;
        vec(UTimer)  ut;
        vec(u32)     utfree;
        vec(Watch)   wt;
        vec(u32)     wtfree;
        vec(Done)    ready;
        Conn        *dirty;
        Array       *evs;
        Array       *pins;
        Array       *tokens;
        vec(u32)     drains;
        u64          seq;
        Buf          tmp;
        TyMutex      nmu;
        vec(i64)     notes;
        atomic_long  st[S_N];
};

extern _Thread_local Loop *HttpLoop;

inline static usize
BufLen(Buf const *b)
{
        return b->count - b->off;
}

inline static char *
BufHead(Buf const *b)
{
        return b->items + b->off;
}

inline static void
BufClear(Buf *b)
{
        b->off   = 0;
        b->count = 0;
}

inline static void
BufEat(Buf *b, usize n)
{
        b->off += n;
        if (b->off >= b->count) {
                b->off   = 0;
                b->count = 0;
        }
}

inline static char *
BufRoom(Buf *b, usize n)
{
        if (b->count + n > b->capacity) {
                if (b->off > 0) {
                        memmove(b->items, b->items + b->off, b->count - b->off);
                        b->count -= b->off;
                        b->off    = 0;
                }
                if (b->count + n > b->capacity) {
                        b->capacity = fit2(max(b->capacity, 1024), b->count + n);
                        mresize(b->items, b->capacity);
                }
        }

        return b->items + b->count;
}

inline static void
BufPut(Buf *b, void const *p, usize n)
{
        if (n > 0) {
                memcpy(BufRoom(b, n), p, n);
                b->count += n;
        }
}

inline static void
BufPutc(Buf *b, char c)
{
        *BufRoom(b, 1) = c;
        b->count += 1;
}

inline static void
BufFree(Buf *b)
{
        xmF(b->items);
        *b = (Buf) {0};
}

inline static void
BufShrink(Buf *b, usize keep)
{
        if (b->capacity > keep && BufLen(b) == 0) {
                BufFree(b);
        }
}

inline static void
BufSwap(Buf *a, Buf *b)
{
        Buf t = *a;
        *a = *b;
        *b = t;
}

inline static void
TrimSpan(void const *s, usize *a, usize *b, char const *junk)
{
        char const *p = s;

        while (*a < *b && p[*a] != 0 && strchr(junk, p[*a]) != NULL) {
                *a += 1;
        }

        while (*b > *a && p[*b - 1] != 0 && strchr(junk, p[*b - 1]) != NULL) {
                *b -= 1;
        }
}

#define BufLit(b, s) BufPut((b), (s), sizeof (s) - 1)
#define BufStr(b, v) BufPut((b), ss(v), sN(v))

void
BufInt(Buf *b, i64 n);

void
BufHex(Buf *b, u64 n);

inline static i64
XchHandle(Xch const *x)
{
        return ((i64)x->gen << 32) | x->slot;
}

Xch *
XchGet(Loop *L, i64 id);

Xch *
XchNew(Loop *L, Conn *c);

void
XchDrop(Loop *L, Xch *x);

void
XchClosed(Loop *L, Xch *x);

void
XchPump(Xch *x);

void
XchDispatch(Loop *L, Xch *x, Value req, bool pending);

void
Emit(Loop *L, int kind, i64 id, Value a, Value b);

void
Pin(Loop *L, Xch *x, Value v);

Value
Pinned(Loop *L, Xch const *x);

void
Unpin(Loop *L, Xch const *x);

void
ConnRead(Conn *c);

void
ConnWrite(Conn *c, void const *p, usize n);

void
ConnDirty(Conn *c);

void
ConnClose(Conn *c);

void
ConnFinish(Conn *c);

void
ConnTimer(Conn *c, int which, i64 ms);

void
ConnFlush(Conn *c);

usize
ConnBuffered(Conn const *c);

void
Count(Loop *L, int stat, i64 n);

void
Observe(Loop *L, Xch *x);

void
Arm(Loop *L, int kind, u32 slot, u32 gen, int which, i64 at);

void
LoopDate(Loop *L);

void
LoopTick(Loop *L);

void
LoopNotify(Loop *L, i64 timer);

int
IoInit(Loop *L);

void
IoFree(Loop *L);

void
IoRecv(Loop *L, Conn *c, char *p, usize n);

void
IoSend(Loop *L, Conn *c, char const *p, usize n);

void
IoAccept(Loop *L);

void
IoCancelAccept(Loop *L);

void
IoOpen(Loop *L, Conn *c);

void
IoKill(Loop *L, Conn *c);

int
IoWatch(Loop *L, u32 slot, int fd, int events);

void
IoUnwatch(Loop *L, u32 slot, int fd);

void
IoWake(Loop *L);

void
IoPeer(Conn *c);

void
IoPause(Loop *L);

int
IoWait(Loop *L, i64 ms);

char const *
IoName(Loop const *L);

void
OnRecv(Loop *L, Conn *c, i64 res);

void
OnSent(Loop *L, Conn *c, i64 res);

void
OnAccept(Loop *L, i64 res);

void
OnWake(Loop *L);

void
OnWatch(Loop *L, u32 slot, u32 gen, i64 revents);

void
H1Open(Conn *c);

void
H1Data(Conn *c);

void
H1Eof(Conn *c);

void
H1Timeout(Conn *c, int kind);

void
H1Drained(Conn *c);

void
H1Shutdown(Conn *c);

void
H1Closed(Conn *c);

void
H1Done(Conn *c, Xch *x);

void
H1Resume(Conn *c);

bool
H1Head(Xch *x, int status, Value ctype, Value headers, i64 length);

void
H1Chunk(Xch *x, void const *p, usize n);

void
H1End(Xch *x);

void
H1Error(Conn *c, int status);

bool
H2Open(Conn *c, bool upgrade);

void
H2Data(Conn *c);

void
H2Timeout(Conn *c, int kind);

void
H2Drained(Conn *c);

void
H2Shutdown(Conn *c);

void
H2Closed(Conn *c);

void
H2Flush(Conn *c);

bool
H2Head(Xch *x, int status, Value ctype, Value headers, i64 length, bool body);

void
H2Chunk(Xch *x, void const *p, usize n);

void
H2End(Xch *x);

void
H2Reset(Xch *x, u32 code);

void
H2Resume(Xch *x);

bool
WsAccept(Xch *x, Value key, Value protocol, Value offer);

void
WsData(Conn *c);

void
WsTimeout(Conn *c, int kind);

void
WsShutdown(Conn *c);

void
WsClosed(Conn *c);

isize
WsSend(Xch *x, void const *p, usize n, int op);

void
WsClose(Xch *x, int code, Value reason);

void
WsPing(Conn *c);

void
WsFree(Ws *ws);

Value
MsgRequest(Loop *L, Xch *x, Value head, Value body);

Value
MsgHeadString(Loop *L, Xch *x, char const *p, usize n);

inline static void *
PtrArg(Ty *ty, char const *ctx, char const *name, Value v)
{
        if (v.type != VALUE_PTR || v.ptr == NULL) {
                TyBuiltinBadArg(ty, ctx, name, "Ptr", &v);
        }

        return v.ptr;
}

inline static Loop *
LoopArg(Ty *ty, char const *ctx, Value v)
{
        Loop *L = PtrArg(ty, ctx, "loop", v);
        L->ty   = ty;
        return L;
}

inline static Value
BlobOf(Ty *ty, void const *p, usize n)
{
        Blob *b = value_blob_new(ty);
        uvPn(*b, p, n);
        return BLOB(b);
}

inline static void const *
BytesOf(Ty *ty, char const *ctx, Value v, usize *n)
{
        switch (v.type) {
        case VALUE_STRING: *n = sN(v);       return ss(v);
        case VALUE_BLOB:   *n = vN(*v.blob); return vv(*v.blob);
        case VALUE_NIL:    *n = 0;           return "";
        }

        TyBuiltinBadArg(ty, ctx, "data", "String | Blob", &v);
}

void
MsgHeaders(Ty *ty, Buf *out, Value headers, bool lower, bool server);

bool
MsgReserved(void const *p, usize n);

char const *
MsgReason(int status);

usize
MsgStatusLine(char *out, int status);

bool
MsgIeq(void const *a, usize n, char const *b);

Value
MsgHeadersObject(Ty *ty, Dict *d);

void
MsgFields(Ty *ty, Dict *d, Value head, Span const *hs, usize n);

void
MsgSetup(Ty *ty, Value request, Value headers, Value v10, Value v11, Value v20);

void
MsgSetupClient(Ty *ty, Value response, Value event);

Value
MsgEvent(Ty *ty, Value event, Value data, Value id, Value retry);

Value
MsgVersion(int v);

Value
MsgClientResponse(Ty *ty, int status, Value reason, int version, Dict *headers);

void
Sha1(void const *p, usize n, u8 out[20]);

usize
Base64(u8 const *p, usize n, char *out);

#endif

/* vim: set sts=8 sw=8 expandtab: */
