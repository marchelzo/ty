#include "ty/debug.h"

#if !defined(_WIN32)

#include <ctype.h>
#include <limits.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <unistd.h>

#include "ast.h"
#include "class.h"
#include "compiler.h"
#include "dict.h"
#include "gc.h"
#include "jit.h"
#include "scope.h"
#include "tags.h"
#include "value.h"
#include "vm.h"

volatile sig_atomic_t DebugInterrupt;
volatile sig_atomic_t DebugJitOff;

enum {
        REASON_BREAKPOINT,
        REASON_FUNCTION,
        REASON_STEP,
        REASON_PAUSE,
        REASON_EXCEPTION
};

enum {
        EXC_RAISED   = 1,
        EXC_UNCAUGHT = 2
};

enum {
        EV_STOP,
        EV_OUTPUT,
        EV_THREAD_START,
        EV_THREAD_EXIT,
        EV_BREAKPOINT
};

enum {
        BP_LINE,
        BP_FUNCTION
};

enum {
        H_LOCALS,
        H_CLOSURE,
        H_GLOBALS,
        H_VALUE
};

enum {
        J_NULL,
        J_BOOL,
        J_NUM,
        J_STR,
        J_ARR,
        J_OBJ
};

typedef struct json Json;

struct json {
        u8 kind;
        bool b;
        double n;
        char *s;
        char *key;
        Json *child;
        Json *next;
};

typedef struct {
        char const *p;
        char const *end;
        bool bad;
} JsonCursor;

typedef struct {
        byte_vector b;
        int depth;
        bool keyed;
        bool first[64];
} JsonWriter;

typedef struct {
        char *ip;
        u8 op;
        int refs;
        int disarmed;
} Trap;

typedef struct {
        i64 id;
        int kind;
        char *path;
        int line;
        int actual;
        char *name;
        char *cond;
        char *hit;
        char *log;
        i64 hits;
        bool verified;
        vec(char *) ips;
} Breakpoint;

typedef struct {
        i64 id;
        char *cond;
        char *hit;
        char *log;
        int kind;
} BreakpointHit;

typedef struct {
        char *src;
        Scope *scope;
        char *code;
} CompiledExpr;

typedef struct {
        int kind;
        u64 gen;
        u64 thread;
        i64 bp;
        char *text;
} DebugEvent;

struct debug_job {
        co_state *st;
        isize index;
        char const *ip;
        char const *src;
        bool done;
        bool ok;
        char *text;
        char *type;
};

typedef struct {
        int kind;
        isize frame;
        Module const *mod;
        Value v;
        bool mark;
} Handle;

typedef struct {
        DebugFrame f;
        TyDebugThread *d;
} FrameRef;

typedef vec(DebugFrame) DebugFrameVector;

typedef struct {
        uptr ip;
        Expr const *e;
        bool start;
} LineSlot;

static struct {
        pthread_mutex_t lock;
        pthread_cond_t cond;

        vec(TyDebugThread *) threads;

        bool session;
        bool agent;
        bool stopped;
        u64 gen;
        TyDebugThread *stopper;
        int reason;
        char *text;
        char *exc_type;
        vec(i64) hits;
        u64 pause_thread;
        int exc_filters;
        int rearms;

        vec(Trap) traps;
        vec(Breakpoint *) bps;
        i64 next_bp;

        vec(DebugEvent) events;
        int wake[2];

        int client;
        bool lines1;
        bool cols1;

        vec(FrameRef) frames;
        vec(Handle) handles;
        vec(Module const *) sources;
        Value job_result;

        int urg;
} D = {
        .lock   = PTHREAD_MUTEX_INITIALIZER,
        .cond   = PTHREAD_COND_INITIALIZER,
        .wake   = { -1, -1 },
        .client = -1,
        .lines1 = true,
        .cols1  = true
};

static pthread_mutex_t LocLock     = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t CacheLock   = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t CompileLock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t SendLock    = PTHREAD_MUTEX_INITIALIZER;

static vec(CompiledExpr) Compiled;

static LineSlot *LineCache;
static usize     LineCap;
static usize     LineCount;

static int WatchPipe[2] = { -1, -1 };
static atomic_llong Seq;

static _Thread_local bool AgentThread;
static _Thread_local Expr const *EvalContext;

static char const *ReasonNames[] = {
        [REASON_BREAKPOINT] = "breakpoint",
        [REASON_FUNCTION]   = "function breakpoint",
        [REASON_STEP]       = "step",
        [REASON_PAUSE]      = "pause",
        [REASON_EXCEPTION]  = "exception"
};

static char *
xstrdup(char const *s)
{
        return (s == NULL) ? NULL : strdup(s);
}

static char *
xstrndup(char const *s, usize n)
{
        char *out = malloc(n + 1);
        memcpy(out, s, n);
        out[n] = '\0';
        return out;
}

static void
JsonFree(Json *j)
{
        while (j != NULL) {
                Json *next = j->next;
                JsonFree(j->child);
                free(j->s);
                free(j->key);
                free(j);
                j = next;
        }
}

static void
JsonSkip(JsonCursor *c)
{
        while (c->p < c->end && isspace((u8)*c->p)) {
                c->p += 1;
        }
}

static int
HexDigit(char c)
{
        if (c >= '0' && c <= '9') {
                return c - '0';
        }

        if (c >= 'a' && c <= 'f') {
                return c - 'a' + 10;
        }

        if (c >= 'A' && c <= 'F') {
                return c - 'A' + 10;
        }

        return -1;
}

static u32
JsonHex4(JsonCursor *c)
{
        u32 cp = 0;

        for (int i = 0; i < 4; ++i) {
                int d = (c->p < c->end) ? HexDigit(*c->p) : -1;
                if (d < 0) {
                        c->bad = true;
                        return 0;
                }
                cp = (cp << 4) | (u32)d;
                c->p += 1;
        }

        return cp;
}

static void
PutUtf8(byte_vector *out, u32 cp)
{
        if (cp < 0x80) {
                xvP(*out, (char)cp);
        } else if (cp < 0x800) {
                xvP(*out, (char)(0xC0 | (cp >> 6)));
                xvP(*out, (char)(0x80 | (cp & 0x3F)));
        } else if (cp < 0x10000) {
                xvP(*out, (char)(0xE0 | (cp >> 12)));
                xvP(*out, (char)(0x80 | ((cp >> 6) & 0x3F)));
                xvP(*out, (char)(0x80 | (cp & 0x3F)));
        } else {
                xvP(*out, (char)(0xF0 | (cp >> 18)));
                xvP(*out, (char)(0x80 | ((cp >> 12) & 0x3F)));
                xvP(*out, (char)(0x80 | ((cp >> 6) & 0x3F)));
                xvP(*out, (char)(0x80 | (cp & 0x3F)));
        }
}

static char *
JsonString(JsonCursor *c)
{
        byte_vector out = {0};

        c->p += 1;

        while (c->p < c->end && *c->p != '"') {
                char ch = *c->p++;

                if (ch != '\\') {
                        xvP(out, ch);
                        continue;
                }

                if (c->p >= c->end) {
                        break;
                }

                u32 cp;

                switch ((ch = *c->p++)) {
                case 'n':  xvP(out, '\n'); break;
                case 't':  xvP(out, '\t'); break;
                case 'r':  xvP(out, '\r'); break;
                case 'b':  xvP(out, '\b'); break;
                case 'f':  xvP(out, '\f'); break;
                case 'u':
                        cp = JsonHex4(c);
                        if (
                                (cp >= 0xD800 && cp < 0xDC00)
                             && (c->p + 1 < c->end)
                             && (c->p[0] == '\\')
                             && (c->p[1] == 'u')
                        ) {
                                c->p += 2;
                                u32 lo = JsonHex4(c);
                                cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                        }
                        PutUtf8(&out, cp);
                        break;
                default:
                        xvP(out, ch);
                        break;
                }
        }

        if (c->p >= c->end) {
                c->bad = true;
        } else {
                c->p += 1;
        }

        xvP(out, '\0');

        return vv(out);
}

static Json *
JsonValue(JsonCursor *c, int depth);

static Json *
JsonAggregate(JsonCursor *c, int depth, bool object)
{
        Json *j = calloc(1, sizeof *j);
        Json **tail = &j->child;
        char close = object ? '}' : ']';

        j->kind = object ? J_OBJ : J_ARR;
        c->p += 1;

        JsonSkip(c);

        if (c->p < c->end && *c->p == close) {
                c->p += 1;
                return j;
        }

        while (!c->bad) {
                char *key = NULL;

                JsonSkip(c);

                if (object) {
                        if (c->p >= c->end || *c->p != '"') {
                                c->bad = true;
                                break;
                        }
                        key = JsonString(c);
                        JsonSkip(c);
                        if (c->p >= c->end || *c->p != ':') {
                                free(key);
                                c->bad = true;
                                break;
                        }
                        c->p += 1;
                }

                Json *item = JsonValue(c, depth + 1);

                if (item == NULL) {
                        free(key);
                        c->bad = true;
                        break;
                }

                item->key = key;
                *tail = item;
                tail = &item->next;

                JsonSkip(c);

                if (c->p < c->end && *c->p == ',') {
                        c->p += 1;
                        continue;
                }

                if (c->p < c->end && *c->p == close) {
                        c->p += 1;
                        break;
                }

                c->bad = true;
        }

        return j;
}

static Json *
JsonValue(JsonCursor *c, int depth)
{
        JsonSkip(c);

        if (c->p >= c->end || depth > 64) {
                c->bad = true;
                return NULL;
        }

        Json *j;

        switch (*c->p) {
        case '{':
                return JsonAggregate(c, depth, true);

        case '[':
                return JsonAggregate(c, depth, false);

        case '"':
                j = calloc(1, sizeof *j);
                j->kind = J_STR;
                j->s = JsonString(c);
                return j;

        case 't':
        case 'f':
        case 'n':
                j = calloc(1, sizeof *j);
                if (c->end - c->p >= 4 && memcmp(c->p, "true", 4) == 0) {
                        j->kind = J_BOOL;
                        j->b = true;
                        c->p += 4;
                } else if (c->end - c->p >= 5 && memcmp(c->p, "false", 5) == 0) {
                        j->kind = J_BOOL;
                        c->p += 5;
                } else if (c->end - c->p >= 4 && memcmp(c->p, "null", 4) == 0) {
                        j->kind = J_NULL;
                        c->p += 4;
                } else {
                        c->bad = true;
                }
                return j;

        default:
                j = calloc(1, sizeof *j);
                j->kind = J_NUM;
                char buf[64];
                usize n = 0;
                while (
                        (c->p < c->end)
                     && (n + 1 < sizeof buf)
                     && (strchr("+-0123456789.eE", *c->p) != NULL)
                ) {
                        buf[n++] = *c->p++;
                }
                buf[n] = '\0';
                if (n == 0) {
                        c->bad = true;
                }
                j->n = strtod(buf, NULL);
                return j;
        }
}

static Json *
JsonParse(char const *s, usize n)
{
        JsonCursor c = { .p = s, .end = s + n };
        Json *j = JsonValue(&c, 0);

        if (c.bad) {
                JsonFree(j);
                return NULL;
        }

        return j;
}

static Json const *
JGet(Json const *j, char const *key)
{
        if (j == NULL || j->kind != J_OBJ) {
                return NULL;
        }

        for (Json const *it = j->child; it != NULL; it = it->next) {
                if (strcmp(it->key, key) == 0) {
                        return it;
                }
        }

        return NULL;
}

static char const *
JStr(Json const *j, char const *key)
{
        Json const *v = JGet(j, key);
        return (v != NULL && v->kind == J_STR) ? v->s : NULL;
}

static i64
JInt(Json const *j, char const *key, i64 dflt)
{
        Json const *v = JGet(j, key);
        return (v != NULL && v->kind == J_NUM) ? (i64)v->n : dflt;
}

static bool
JBool(Json const *j, char const *key, bool dflt)
{
        Json const *v = JGet(j, key);
        return (v != NULL && v->kind == J_BOOL) ? v->b : dflt;
}

static void
jw_sep(JsonWriter *w)
{
        if (w->keyed) {
                w->keyed = false;
                return;
        }

        if (w->depth > 0 && !w->first[w->depth]) {
                xvP(w->b, ',');
        }

        w->first[w->depth] = false;
}

static void
jw_escape(JsonWriter *w, char const *s)
{
        u8 const *p = (u8 const *)((s == NULL) ? "" : s);

        xvP(w->b, '"');

        while (*p != '\0') {
                u8 c = *p;
                int len = (c < 0x80) ? 1
                        : ((c & 0xE0) == 0xC0) ? 2
                        : ((c & 0xF0) == 0xE0) ? 3
                        : ((c & 0xF8) == 0xF0) ? 4
                        : 0;

                bool ok = (len > 0);

                for (int i = 1; ok && i < len; ++i) {
                        ok = ((p[i] & 0xC0) == 0x80);
                }

                if (!ok) {
                        xvPn(w->b, "\xEF\xBF\xBD", 3);
                        p += 1;
                        continue;
                }

                if (len > 1) {
                        xvPn(w->b, (char const *)p, len);
                        p += len;
                        continue;
                }

                switch (c) {
                case '"':  xvPn(w->b, "\\\"", 2); break;
                case '\\': xvPn(w->b, "\\\\", 2); break;
                case '\n': xvPn(w->b, "\\n", 2);  break;
                case '\r': xvPn(w->b, "\\r", 2);  break;
                case '\t': xvPn(w->b, "\\t", 2);  break;
                default:
                        if (c < 0x20) {
                                char buf[8];
                                snprintf(buf, sizeof buf, "\\u%04x", c);
                                xvPn(w->b, buf, 6);
                        } else {
                                xvP(w->b, (char)c);
                        }
                }

                p += 1;
        }

        xvP(w->b, '"');
}

static void
jw_open(JsonWriter *w, char c)
{
        jw_sep(w);
        xvP(w->b, c);
        w->depth += 1;
        w->first[w->depth] = true;
}

static void
jw_close(JsonWriter *w, char c)
{
        xvP(w->b, c);
        w->depth -= 1;
}

static void
jw_key(JsonWriter *w, char const *k)
{
        jw_sep(w);
        jw_escape(w, k);
        xvP(w->b, ':');
        w->keyed = true;
}

static void
jw_str(JsonWriter *w, char const *s)
{
        jw_sep(w);
        jw_escape(w, s);
}

static void
jw_int(JsonWriter *w, i64 n)
{
        char buf[32];
        int len = snprintf(buf, sizeof buf, "%lld", (long long)n);
        jw_sep(w);
        xvPn(w->b, buf, len);
}

static void
jw_bool(JsonWriter *w, bool b)
{
        jw_sep(w);
        xvPn(w->b, b ? "true" : "false", b ? 4 : 5);
}

static void
jw_raw(JsonWriter *w, char const *s, usize n)
{
        jw_sep(w);
        xvPn(w->b, s, n);
}

static void
jw_kstr(JsonWriter *w, char const *k, char const *s)
{
        jw_key(w, k);
        jw_str(w, s);
}

static void
jw_kint(JsonWriter *w, char const *k, i64 n)
{
        jw_key(w, k);
        jw_int(w, n);
}

static void
jw_kbool(JsonWriter *w, char const *k, bool b)
{
        jw_key(w, k);
        jw_bool(w, b);
}

static bool
WriteAll(int fd, char const *p, usize n)
{
        while (n > 0) {
                ssize_t k = write(fd, p, n);
                if (k < 0 && errno == EINTR) {
                        continue;
                }
                if (k <= 0) {
                        return false;
                }
                p += k;
                n -= (usize)k;
        }

        return true;
}

static void
SendMessage(JsonWriter *w)
{
        char header[64];
        int n = snprintf(header, sizeof header, "Content-Length: %zu\r\n\r\n", vN(w->b));

        pthread_mutex_lock(&SendLock);

        if (D.client >= 0) {
                WriteAll(D.client, header, n);
                WriteAll(D.client, vv(w->b), vN(w->b));
        }

        pthread_mutex_unlock(&SendLock);

        xvF(w->b);
}

static void
SendEvent(char const *event, JsonWriter *body)
{
        JsonWriter w = {0};

        jw_open(&w, '{');
        jw_kint(&w, "seq", ++Seq);
        jw_kstr(&w, "type", "event");
        jw_kstr(&w, "event", event);

        if (body != NULL) {
                jw_key(&w, "body");
                jw_raw(&w, vv(body->b), vN(body->b));
                xvF(body->b);
        }

        jw_close(&w, '}');

        SendMessage(&w);
}

static void
Respond(Json const *req, char const *error, JsonWriter *body)
{
        JsonWriter w = {0};

        jw_open(&w, '{');
        jw_kint(&w, "seq", ++Seq);
        jw_kstr(&w, "type", "response");
        jw_kint(&w, "request_seq", JInt(req, "seq", 0));
        jw_kbool(&w, "success", error == NULL);
        jw_kstr(&w, "command", JStr(req, "command"));

        if (error != NULL) {
                jw_kstr(&w, "message", error);
        }

        if (body != NULL && error == NULL) {
                jw_key(&w, "body");
                jw_raw(&w, vv(body->b), vN(body->b));
        }

        if (body != NULL) {
                xvF(body->b);
        }

        jw_close(&w, '}');

        SendMessage(&w);
}

static void
Wake(void)
{
        char c = 1;

        if (D.wake[1] >= 0) {
                (void)!write(D.wake[1], &c, 1);
        }
}

static void
PostEvent(DebugEvent ev)
{
        ev.gen = D.gen;
        xvP(D.events, ev);
        Wake();
}

void
DebugLockLocations(void)
{
        pthread_mutex_lock(&LocLock);
}

void
DebugUnlockLocations(void)
{
        pthread_mutex_unlock(&LocLock);
}

Expr const *
DebugEvalContext(Ty *ty)
{
        return EvalContext;
}

static bool
IsFunctionExpr(Expr const *e);

static Expr const *
FindExpr(char const *ip, bool *start)
{
        uptr c = (uptr)ip;
        isize nl;
        Expr const *e = NULL;

        *start = false;

        pthread_mutex_lock(&LocLock);

        location_vector const *lists = compiler_location_lists(&nl);

        for (isize l = 0; l < nl; ++l) {
                location_vector const *locs = &lists[l];

                if (vN(*locs) == 0 || c < v_(*locs, 0)->p_start) {
                        continue;
                }

                uptr end = 0;
                for (isize i = 0; i < vN(*locs); ++i) {
                        if (v_(*locs, i)->p_end > end) {
                                end = v_(*locs, i)->p_end;
                        }
                }

                if (c >= end) {
                        continue;
                }

                uptr width = UINTPTR_MAX;

                for (isize i = 0; i < vN(*locs); ++i) {
                        struct eloc const *loc = v_(*locs, i);

                        if (loc->p_start > c) {
                                break;
                        }

                        if (c >= loc->p_end || loc->e == NULL || IsFunctionExpr(loc->e)) {
                                continue;
                        }

                        if (loc->p_start == c) {
                                *start = true;
                        }

                        if (loc->p_end - loc->p_start < width) {
                                width = loc->p_end - loc->p_start;
                                e = loc->e;
                        }
                }

                break;
        }

        pthread_mutex_unlock(&LocLock);

        return e;
}

static void
LineCacheGrow(void)
{
        usize cap = (LineCap == 0) ? 4096 : 2 * LineCap;
        LineSlot *slots = calloc(cap, sizeof *slots);

        for (usize i = 0; i < LineCap; ++i) {
                if (LineCache[i].ip == 0) {
                        continue;
                }
                usize h = (LineCache[i].ip * 0x9E3779B97F4A7C15ULL) >> 20;
                while (slots[h & (cap - 1)].ip != 0) {
                        h += 1;
                }
                slots[h & (cap - 1)] = LineCache[i];
        }

        free(LineCache);
        LineCache = slots;
        LineCap = cap;
}

static Expr const *
LocAt(char const *ip, bool *start)
{
        *start = false;

        if (ip == NULL || ip == &JIT) {
                return NULL;
        }

        uptr key = (uptr)ip;

        pthread_mutex_lock(&CacheLock);

        if (LineCap > 0) {
                usize h = (key * 0x9E3779B97F4A7C15ULL) >> 20;
                for (;;) {
                        LineSlot *slot = &LineCache[h & (LineCap - 1)];
                        if (slot->ip == key) {
                                Expr const *e = slot->e;
                                *start = slot->start;
                                pthread_mutex_unlock(&CacheLock);
                                return e;
                        }
                        if (slot->ip == 0) {
                                break;
                        }
                        h += 1;
                }
        }

        Expr const *e = FindExpr(ip, start);

        if (2 * (LineCount + 1) > LineCap) {
                LineCacheGrow();
        }

        usize h = (key * 0x9E3779B97F4A7C15ULL) >> 20;
        while (LineCache[h & (LineCap - 1)].ip != 0) {
                h += 1;
        }

        LineCache[h & (LineCap - 1)] = (LineSlot) { .ip = key, .e = e, .start = *start };
        LineCount += 1;

        pthread_mutex_unlock(&CacheLock);

        return e;
}

static Expr const *
ExprAt(Ty *ty, char const *ip)
{
        bool start;
        return LocAt(ip, &start);
}

static bool
IsSourcePath(char const *path)
{
        return (path != NULL) && (path[0] != '(');
}

static bool
HasLocation(Expr const *e)
{
        return (e != NULL)
            && (e->mod != NULL)
            && IsSourcePath(e->mod->path);
}

static bool
SameLine(Expr const *a, Expr const *b)
{
        return (a != NULL)
            && (b != NULL)
            && (a->mod == b->mod)
            && (a->start.line == b->start.line);
}

static Value *
StackOf(Ty *t, co_state *st)
{
        return (st == t->st) ? vv(t->stack) : vv(st->stack);
}

static isize
StackCount(Ty *t, co_state *st)
{
        return (st == t->st) ? vN(t->stack) : vN(st->stack);
}

static Generator *
RunningGenerator(Ty *t, co_state *st)
{
        if (vN(st->frames) == 0) {
                return NULL;
        }

        isize fp = v_(st->frames, 0)->fp;

        if (fp < 1 || fp > StackCount(t, st)) {
                return NULL;
        }

        Value const *v = &StackOf(t, st)[fp - 1];

        if (v->type != VALUE_GENERATOR) {
                return NULL;
        }

        Generator *gen = v->gen;

        if (
                (gen->ip != NULL)
             || (gen->st == NULL)
             || (gen->st == st)
             || (vN(gen->st->frames) == 0)
        ) {
                return NULL;
        }

        return gen;
}

static isize
LogicalDepth(Ty *t)
{
        co_state *st = t->st;
        isize depth = vN(st->frames);

        for (int hops = 0; hops < 64; ++hops) {
                Generator *gen = RunningGenerator(t, st);
                if (gen == NULL) {
                        break;
                }
                st = gen->st;
                depth += vN(st->frames) - 1;
        }

        return depth;
}

static void
WalkFrames(TyDebugThread *d, DebugFrameVector *out)
{
        Ty *t = d->ty;
        co_state *st = t->st;
        char const *ip = (d->state == DBG_PARKED) ? d->stop_ip : t->ip;
        isize nf = vN(st->frames);

        for (int n = 0; n < 100000 && ip != NULL; ++n) {
                Frame const *frame = (nf > 0) ? v_(st->frames, nf - 1) : NULL;
                char const *fip = jit_frame_ip(frame, ip);

                DebugFrame f = {
                        .ty    = t,
                        .st    = st,
                        .index = nf - 1,
                        .ip    = fip
                };

                if (frame != NULL) {
                        f.fun     = frame->f;
                        f.has_fun = true;
                        f.fp      = frame->fp;
                        f.nslot   = frame->f.info[FUN_INFO_BOUND];
                }

                bool hidden = (frame != NULL) && is_hidden_fun(&frame->f);

                if (!hidden && (frame != NULL || HasLocation(ExprAt(t, fip - 1)))) {
                        xvP(*out, f);
                }

                if (frame == NULL) {
                        break;
                }

                ip = frame->ip;
                nf -= 1;

                if (nf == 0) {
                        Generator *gen = RunningGenerator(t, st);
                        if (gen != NULL) {
                                st = gen->st;
                                nf = vN(st->frames) - 1;
                                ip = v_(st->frames, nf)->ip;
                        }
                }
        }
}

static Value *
FrameSlot(DebugFrame const *f, isize i)
{
        isize k = f->fp + i;

        if (k < 0 || k >= StackCount(f->ty, f->st)) {
                return NULL;
        }

        return &StackOf(f->ty, f->st)[k];
}

static Value
Deref(Value const *v)
{
        Value x = *v;

        for (int i = 0; i < 64 && x.type == VALUE_REF && x.ref != NULL; ++i) {
                x = *x.ref;
        }

        return x;
}

static bool
TrapFind(char const *ip, isize *out)
{
        for (isize i = 0; i < vN(D.traps); ++i) {
                if (v_(D.traps, i)->ip == ip) {
                        *out = i;
                        return true;
                }
        }

        return false;
}

static void
TrapAdd(char *ip)
{
        isize i;

        if (TrapFind(ip, &i)) {
                v_(D.traps, i)->refs += 1;
                return;
        }

        xvP(D.traps, ((Trap) { .ip = ip, .op = (u8)*ip, .refs = 1 }));
        *(volatile char *)ip = (char)INSTR_TRAP_TY;
}

static void
TrapDel(char *ip)
{
        isize i;

        if (!TrapFind(ip, &i)) {
                return;
        }

        Trap *trap = v_(D.traps, i);

        if (--trap->refs > 0) {
                return;
        }

        *(volatile char *)ip = (char)trap->op;
        *trap = vXx(D.traps);
}

static void
TrapDisarm(char *ip)
{
        isize i;

        if (TrapFind(ip, &i) && v_(D.traps, i)->disarmed++ == 0) {
                *(volatile char *)ip = (char)v_(D.traps, i)->op;
        }
}

static void
TrapRearm(char *ip)
{
        isize i;

        if (TrapFind(ip, &i) && --v_(D.traps, i)->disarmed == 0) {
                *(volatile char *)ip = (char)INSTR_TRAP_TY;
        }
}

static bool
AnyStepping(void);

static void
RecomputeInterrupt(void)
{
        DebugInterrupt = D.stopped || (D.rearms > 0) || AnyStepping();
}

static void
RearmLocked(TyDebugThread *d)
{
        if (d->rearm == NULL) {
                return;
        }

        TrapRearm(d->rearm);
        d->rearm = NULL;
        D.rearms -= 1;

        RecomputeInterrupt();
}

static void
DisarmLocked(TyDebugThread *d, char *ip)
{
        RearmLocked(d);
        TrapDisarm(ip);

        d->rearm = ip;
        D.rearms += 1;

        DebugInterrupt = 1;
}

void
DebugRearm(Ty *ty)
{
        pthread_mutex_lock(&D.lock);
        RearmLocked(ty->dbg);
        pthread_mutex_unlock(&D.lock);
}

u8
DebugOriginalOp(char const *ip)
{
        isize i;
        u8 op;

        pthread_mutex_lock(&D.lock);
        op = TrapFind(ip, &i) ? v_(D.traps, i)->op : (u8)*ip;
        pthread_mutex_unlock(&D.lock);

        return op;
}

void
DebugSanitizeCode(char const *src, char *dst, usize n)
{
        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.traps); ++i) {
                Trap const *trap = v_(D.traps, i);
                if (trap->ip >= src && trap->ip < src + n) {
                        dst[trap->ip - src] = (char)trap->op;
                }
        }

        pthread_mutex_unlock(&D.lock);
}

static bool
HasHandler(Ty *t)
{
        co_state *st = t->st;

        for (int hops = 0; hops < 64 && st != NULL; ++hops) {
                for (isize i = vN(st->try_stack) - 1; i >= 0; --i) {
                        struct try const *try = v__(st->try_stack, i);
                        if (try->state == TRY_TRY && !try->native) {
                                return true;
                        }
                }
                Generator *gen = RunningGenerator(t, st);
                st = (gen == NULL) ? NULL : gen->st;
        }

        return false;
}

static char *
StripAnsi(char *s)
{
        char *out = s;

        for (char const *p = s; *p != '\0'; ++p) {
                if (p[0] != '\x1b' || p[1] != '[') {
                        *out++ = *p;
                        continue;
                }
                p += 2;
                while (*p != '\0' && !isalpha((u8)*p)) {
                        p += 1;
                }
                if (*p == '\0') {
                        break;
                }
        }

        *out = '\0';

        return s;
}

static char *
SafeShow(Ty *ty, Value const *v, u32 flags, usize max)
{
        Value x = Deref(v);

        if (x.type == VALUE_UNINITIALIZED) {
                return xstrdup("<uninitialized>");
        }

        if (x.type == VALUE_ZERO) {
                return xstrdup("<unset>");
        }

        char *out;

        if (TY_CATCH_ERROR()) {
                (void)TY_CATCH();
                return xstrdup("<unprintable>");
        }

        char const *s = StripAnsi(value_show(ty, &x, flags | TY_SHOW_NOCOLOR));
        usize n = strlen(s);

        if (n > max) {
                out = malloc(max + 4);
                memcpy(out, s, max);
                memcpy(out + max, "...", 4);
        } else {
                out = xstrndup(s, n);
        }

        TY_CATCH_END();

        return out;
}

static char const *
DbgTypeName(Ty *ty, Value const *v)
{
        Value x = Deref(v);

        if (x.tags != 0 && x.type != VALUE_TAG) {
                return tags_name(ty, tags_first(ty, x.tags));
        }

        switch (x.type & ~VALUE_TAGGED) {
        case VALUE_INTEGER:          return "Int";
        case VALUE_REAL:             return "Float";
        case VALUE_BOOLEAN:          return "Bool";
        case VALUE_NIL:              return "nil";
        case VALUE_STRING:           return "String";
        case VALUE_BLOB:             return "Blob";
        case VALUE_ARRAY:            return "Array";
        case VALUE_DICT:             return "Dict";
        case VALUE_TUPLE:            return "Tuple";
        case VALUE_OBJECT:           return class_name(ty, x.class);
        case VALUE_CLASS:            return "Class";
        case VALUE_TAG:              return "Tag";
        case VALUE_REGEX:            return "Regex";
        case VALUE_GENERATOR:        return "Generator";
        case VALUE_THREAD:           return "Thread";
        case VALUE_PTR:              return "Ptr";
        case VALUE_UNINITIALIZED:    return "<uninitialized>";
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_BUILTIN_METHOD:
        case VALUE_FOREIGN_FUNCTION:
        case VALUE_NATIVE_FUNCTION:
                return "Function";
        default:
                return "Value";
        }
}

static Value
Untag(Ty *ty, Value const *v)
{
        Value x = Deref(v);

        if (x.type == VALUE_TAG || x.tags == 0) {
                return x;
        }

        x.tags = 0;
        x.type &= ~VALUE_TAGGED;

        return x;
}

static bool
IsStructured(Ty *ty, Value const *v)
{
        Value x = Untag(ty, v);

        switch (x.type) {
        case VALUE_ARRAY:  return vN(*x.array) > 0;
        case VALUE_DICT:   return x.dict->count > 0;
        case VALUE_TUPLE:  return x.count > 0;
        case VALUE_OBJECT: return (x.object->nslot > 0) || (x.object->dynamic != NULL);
        default:           return false;
        }
}

static void
Preview(Ty *ty, byte_vector *out, Value const *v, int depth);

static void
PreviewSep(byte_vector *out, isize i)
{
        if (i > 0) {
                xvPn(*out, ", ", 2);
        }
}

static bool
PreviewFull(byte_vector *out)
{
        if (vN(*out) > 200) {
                xvPn(*out, "...", 3);
                return true;
        }

        return false;
}

static void
PreviewObject(Ty *ty, byte_vector *out, Value const *x, int depth)
{
        TyObject const *obj = x->object;
        Class const *class = obj->class;
        char const *name = class_name(ty, x->class);
        isize n = 0;

        xvPn(*out, name, strlen(name));
        xvP(*out, '{');

        if (depth > 1) {
                xvPn(*out, "...}", 4);
                return;
        }

        for (u32 i = 0; i < obj->nslot && i < vN(class->fields.ids); ++i) {
                if (PreviewFull(out)) {
                        break;
                }
                char const *field = M_NAME(v__(class->fields.ids, i));
                PreviewSep(out, n++);
                xvPn(*out, field, strlen(field));
                xvPn(*out, ": ", 2);
                Preview(ty, out, &obj->slots[i], depth + 1);
        }

        if (obj->dynamic != NULL) {
                for (isize i = 0; i < vN(obj->dynamic->ids); ++i) {
                        if (PreviewFull(out)) {
                                break;
                        }
                        char const *field = M_NAME(v__(obj->dynamic->ids, i));
                        PreviewSep(out, n++);
                        xvPn(*out, field, strlen(field));
                        xvPn(*out, ": ", 2);
                        Preview(ty, out, v_(obj->dynamic->values, i), depth + 1);
                }
        }

        xvP(*out, '}');
}

static void
Preview(Ty *ty, byte_vector *out, Value const *v, int depth)
{
        Value x = Deref(v);
        int ntags = 0;

        if (x.type != VALUE_TAG && x.tags != 0) {
                for (int tags = x.tags; tags != 0; tags = tags_pop(ty, tags)) {
                        char const *name = tags_name(ty, tags_first(ty, tags));
                        xvPn(*out, name, strlen(name));
                        xvP(*out, '(');
                        ntags += 1;
                }
                x = Untag(ty, &x);
        }

        char *s;

        switch (x.type) {
        case VALUE_ARRAY:
                xvP(*out, '[');
                if (depth > 1 && vN(*x.array) > 0) {
                        xvPn(*out, "...", 3);
                } else {
                        for (isize i = 0; i < vN(*x.array); ++i) {
                                if (PreviewFull(out)) {
                                        break;
                                }
                                PreviewSep(out, i);
                                Preview(ty, out, v_(*x.array, i), depth + 1);
                        }
                }
                xvP(*out, ']');
                break;

        case VALUE_TUPLE:
                xvP(*out, '(');
                for (isize i = 0; i < x.count; ++i) {
                        if (PreviewFull(out)) {
                                break;
                        }
                        PreviewSep(out, i);
                        if (x.ids != NULL && x.ids[i] >= 0) {
                                char const *name = M_NAME(x.ids[i]);
                                xvPn(*out, name, strlen(name));
                                xvPn(*out, ": ", 2);
                        }
                        Preview(ty, out, &x.items[i], depth + 1);
                }
                xvP(*out, ')');
                break;

        case VALUE_DICT:
                xvPn(*out, "%{", 2);
                if (depth > 1 && x.dict->count > 0) {
                        xvPn(*out, "...", 3);
                } else {
                        isize i = 0;
                        for (DictItem *it = DictFirst(x.dict); it != NULL; it = it->next) {
                                if (PreviewFull(out)) {
                                        break;
                                }
                                PreviewSep(out, i++);
                                Preview(ty, out, &it->k, depth + 1);
                                xvPn(*out, ": ", 2);
                                Preview(ty, out, &it->v, depth + 1);
                        }
                }
                xvP(*out, '}');
                break;

        case VALUE_OBJECT:
                PreviewObject(ty, out, &x, depth);
                break;

        default:
                s = SafeShow(ty, &x, TY_SHOW_BASIC | TY_SHOW_REPR, 120);
                xvPn(*out, s, strlen(s));
                free(s);
                break;
        }

        while (ntags --> 0) {
                xvP(*out, ')');
        }
}

static char *
PreviewString(Ty *ty, Value const *v)
{
        byte_vector out = {0};
        Preview(ty, &out, v, 0);
        xvP(out, '\0');
        return vv(out);
}

static char *
Describe(Ty *ty, Value const *v, u32 flags)
{
        Value x = Untag(ty, v);

        switch (x.type) {
        case VALUE_OBJECT:
                if (
                        (class_lookup_method_i(ty, x.class, NAMES._str_) != NULL)
                     || (class_lookup_method_i(ty, x.class, NAMES._repr_) != NULL)
                ) {
                        return SafeShow(ty, v, flags, 8192);
                }
                return PreviewString(ty, v);

        case VALUE_ARRAY:
        case VALUE_DICT:
        case VALUE_TUPLE:
                return PreviewString(ty, v);

        default:
                return SafeShow(ty, v, flags, 8192);
        }
}

static TyDebugThread *
ThreadById(u64 id)
{
        for (isize i = 0; i < vN(D.threads); ++i) {
                TyDebugThread *d = v__(D.threads, i);
                if (d->id == id && !d->agent) {
                        return d;
                }
        }

        return NULL;
}

static void
RunJob(Ty *ty, DebugJob *job);

static void
ParkLocked(Ty *ty, TyDebugThread *d, char const *ip)
{
        u64 gen = D.gen;
        char *rearm = d->rearm;

        d->stop_ip = ip;
        d->rearm = NULL;
        ReleaseLock(ty, true);
        d->state = DBG_PARKED;

        pthread_cond_broadcast(&D.cond);

        for (;;) {
                DebugJob *job = d->job;

                if (job != NULL && !job->done) {
                        pthread_mutex_unlock(&D.lock);
                        vm_take_lock_raw(ty);
                        d->suppress += 1;
                        RunJob(ty, job);
                        d->suppress -= 1;
                        pthread_mutex_lock(&D.lock);
                        RearmLocked(d);
                        pthread_mutex_unlock(&D.lock);
                        ReleaseLock(ty, true);
                        pthread_mutex_lock(&D.lock);
                        d->state = DBG_PARKED;
                        d->job = NULL;
                        job->done = true;
                        pthread_cond_broadcast(&D.cond);
                        continue;
                }

                if (!D.stopped || D.gen != gen) {
                        break;
                }

                pthread_cond_wait(&D.cond, &D.lock);
        }

        d->rearm = rearm;

        pthread_mutex_unlock(&D.lock);

        vm_take_lock_raw(ty);
}

static void
StopWorld(
        Ty *ty,
        TyDebugThread *d,
        int reason,
        char const *ip,
        i64 const *ids,
        int nids,
        char *text,
        char *type
)
{
        pthread_mutex_lock(&D.lock);

        while (D.stopped && D.session) {
                ParkLocked(ty, d, ip);
                pthread_mutex_lock(&D.lock);
        }

        if (!D.session) {
                pthread_mutex_unlock(&D.lock);
                free(text);
                free(type);
                return;
        }

        D.stopped  = true;
        D.stopper  = d;
        D.reason   = reason;
        D.text     = text;
        D.exc_type = type;

        v0(D.hits);
        for (int i = 0; i < nids; ++i) {
                xvP(D.hits, ids[i]);
        }

        DebugInterrupt   = 1;
        JitInterruptFlag = 1;

        PostEvent((DebugEvent) { .kind = EV_STOP });

        ParkLocked(ty, d, ip);
}

static char const *
SafeIp(Ty *ty)
{
        return (ty->ip == &JIT) ? ty->ip : ty->ip + 1;
}

static bool
StepShouldStop(Ty *ty, TyDebugThread *d)
{
        if (ty->ip == NULL || ty->ip == &JIT) {
                return false;
        }

        if (d->step == STEP_INSN) {
                return true;
        }

        bool start;
        Expr const *e = LocAt(ty->ip, &start);

        if (!HasLocation(e)) {
                return false;
        }

        if (vN(ty->st->frames) > 0 && is_hidden_fun(&vvL(ty->st->frames)->f)) {
                return false;
        }

        isize depth = LogicalDepth(ty);

        if (depth < d->step_depth) {
                return true;
        }

        switch (d->step) {
        case STEP_IN:
                return start && ((depth != d->step_depth) || !SameLine(e, d->step_expr));

        case STEP_OVER:
                return start && (depth == d->step_depth) && !SameLine(e, d->step_expr);
        }

        return false;
}

void
DebugSafepoint(Ty *ty)
{
        TyDebugThread *d = ty->dbg;

        if (d == NULL) {
                return;
        }

        if (d->rearm != NULL && d->rearm != ty->ip) {
                DebugRearm(ty);
        }

        if (d->agent || d->suppress > 0) {
                return;
        }

        if (D.stopped) {
                pthread_mutex_lock(&D.lock);
                if (D.stopped) {
                        ParkLocked(ty, d, SafeIp(ty));
                } else {
                        pthread_mutex_unlock(&D.lock);
                }
                return;
        }

        if (d->step != STEP_NONE && StepShouldStop(ty, d)) {
                d->step = STEP_NONE;
                d->skip_trap = ty->ip;
                StopWorld(ty, d, REASON_STEP, SafeIp(ty), NULL, 0, NULL, NULL);
        }
}

void
DebugReacquire(Ty *ty)
{
        TyDebugThread *d = ty->dbg;

        if (d->agent || d->suppress > 0 || !D.stopped) {
                return;
        }

        pthread_mutex_lock(&D.lock);

        if (D.stopped) {
                ParkLocked(ty, d, ty->ip);
        } else {
                pthread_mutex_unlock(&D.lock);
        }
}

bool
DebugCanDeopt(Ty *ty)
{
        TyDebugThread *d = ty->dbg;

        if (d == NULL || d->agent || vN(ty->st->frames) == 0) {
                return false;
        }

        if (vN(ty->st->frames) == 1) {
                isize fp = v_(ty->st->frames, 0)->fp;
                if (fp >= 1 && fp <= vN(ty->stack) && v_(ty->stack, fp - 1)->type == VALUE_GENERATOR) {
                        return false;
                }
        }

        return true;
}

static Scope *
ScopeFor(Expr const *ctx)
{
        if (ctx == NULL) {
                return NULL;
        }

        if (ctx->xscope != NULL) {
                return ctx->xscope;
        }

        return (ctx->mod != NULL) ? ctx->mod->scope : NULL;
}

static char *
CompileExpr(Ty *ty, char const *src, Scope *scope, Expr const *ctx, Value *err)
{
        pthread_mutex_lock(&CompileLock);

        for (isize i = 0; i < vN(Compiled); ++i) {
                CompiledExpr const *c = v_(Compiled, i);
                if (c->scope == scope && strcmp(c->src, src) == 0) {
                        char *code = c->code;
                        pthread_mutex_unlock(&CompileLock);
                        return code;
                }
        }

        EvalContext = ctx;
        char *code = compiler_compile_debug_expr(ty, src, scope, err);
        EvalContext = NULL;

        if (code != NULL) {
                xvP(Compiled, ((CompiledExpr) {
                        .src   = xstrdup(src),
                        .scope = scope,
                        .code  = code
                }));
        }

        pthread_mutex_unlock(&CompileLock);

        return code;
}

static bool
EvalHere(Ty *ty, char const *src, Expr const *ctx, Scope *scope, Value *out)
{
        TyDebugThread *d = ty->dbg;

        d->suppress += 1;

        char *code = CompileExpr(ty, src, scope, ctx, out);
        bool ok = false;

        if (code != NULL) {
                Frame const *frame = (vN(ty->st->frames) > 0) ? vvL(ty->st->frames) : NULL;
                isize need = (frame != NULL && scope != NULL && scope->function != NULL)
                           ? vN(scope->function->owned)
                           : 0;
                isize lo = (frame != NULL) ? frame->fp + frame->f.info[FUN_INFO_BOUND] : 0;
                isize hi = (frame != NULL) ? max(lo, frame->fp + need) : 0;
                isize sp = vN(ty->stack);
                isize base = max(sp, hi);
                isize nsave = max(min(hi, sp) - lo, 0);

                while (vN(ty->stack) < base) {
                        xvP(ty->stack, NIL);
                }

                for (isize i = 0; i < nsave; ++i) {
                        xvP(ty->stack, v__(ty->stack, lo + i));
                }

                for (isize i = lo; i < hi; ++i) {
                        v__(ty->stack, i) = NIL;
                }

                char *ip = ty->ip;
                ok = vm_try_exec(ty, code, out);
                ty->ip = ip;

                for (isize i = 0; i < nsave; ++i) {
                        v__(ty->stack, lo + i) = v__(ty->stack, base + i);
                }

                vN(ty->stack) = sp;
        }

        d->suppress -= 1;

        return ok;
}

static Value const *
FindMember(TyObject const *obj, i32 id)
{
        Class const *class = obj->class;

        for (u32 i = 0; i < obj->nslot && i < vN(class->fields.ids); ++i) {
                if (v__(class->fields.ids, i) == id) {
                        return &obj->slots[i];
                }
        }

        if (obj->dynamic != NULL) {
                for (isize i = 0; i < vN(obj->dynamic->ids); ++i) {
                        if (v__(obj->dynamic->ids, i) == id) {
                                return v_(obj->dynamic->values, i);
                        }
                }
        }

        return NULL;
}

static char *
ErrorText(Ty *ty, Value const *err)
{
        Value x = Deref(err);

        if (x.type == VALUE_OBJECT) {
                Value const *what = FindMember(x.object, NAMES._what);
                if (what == NULL || what->type != VALUE_STRING) {
                        return SafeShow(ty, &x, 0, 4096);
                }
                return xstrndup((char const *)ss(*what), sN(*what));
        }

        return SafeShow(ty, &x, 0, 4096);
}

static void
RunJob(Ty *ty, DebugJob *job)
{
        co_state *st0 = ty->st;
        bool swap = (job->st != st0);

        if (swap) {
                st0->stack = ty->stack;
                ty->st = job->st;
                ty->stack = job->st->stack;
        }

        char *ip = ty->ip;
        isize nf = vN(ty->st->frames);
        isize keep = job->index + 1;
        isize nsave = nf - keep;
        Frame *saved = NULL;

        if (nsave > 0) {
                saved = malloc(nsave * sizeof *saved);
                memcpy(saved, v_(ty->st->frames, keep), nsave * sizeof *saved);
        }

        vN(ty->st->frames) = keep;

        Expr const *ctx = ExprAt(ty, job->ip - 1);
        Value v = NIL;

        job->ok = EvalHere(ty, job->src, ctx, ScopeFor(ctx), &v);

        pthread_mutex_lock(&D.lock);
        D.job_result = job->ok ? v : NIL;
        pthread_mutex_unlock(&D.lock);

        xvP(ty->stack, v);

        if (job->ok) {
                job->text = Describe(ty, &v, TY_SHOW_REPR);
                job->type = xstrdup(DbgTypeName(ty, &v));
        } else {
                job->text = ErrorText(ty, &v);
        }

        vN(ty->stack) -= 1;

        vN(ty->st->frames) = keep;

        if (nsave > 0) {
                xvPn(ty->st->frames, saved, nsave);
                free(saved);
        }

        ty->ip = ip;

        if (swap) {
                job->st->stack = ty->stack;
                ty->st = st0;
                ty->stack = st0->stack;
        }
}

static bool
HitConditionMet(char const *hit, i64 count)
{
        if (hit == NULL) {
                return true;
        }

        while (isspace((u8)*hit)) {
                hit += 1;
        }

        char op[3] = {0};
        int n = 0;

        while (n < 2 && strchr("<>=%!", *hit) != NULL) {
                op[n++] = *hit++;
        }

        i64 k = strtoll(hit, NULL, 10);

        if (strcmp(op, ">") == 0) {
                return count > k;
        }

        if (strcmp(op, ">=") == 0) {
                return count >= k;
        }

        if (strcmp(op, "<") == 0) {
                return count < k;
        }

        if (strcmp(op, "<=") == 0) {
                return count <= k;
        }

        if (strcmp(op, "%") == 0) {
                return (k > 0) && (count % k == 0);
        }

        if (strcmp(op, "!=") == 0) {
                return count != k;
        }

        return count == k;
}

static char *
FormatLogMessage(Ty *ty, char const *msg, Expr const *ctx)
{
        byte_vector out = {0};

        while (*msg != '\0') {
                if (*msg != '{') {
                        xvP(out, *msg++);
                        continue;
                }

                char const *end = strchr(msg, '}');

                if (end == NULL) {
                        xvPn(out, msg, strlen(msg));
                        break;
                }

                char *src = xstrndup(msg + 1, end - msg - 1);
                Value v;

                bool ok = EvalHere(ty, src, ctx, ScopeFor(ctx), &v);

                xvP(ty->stack, v);
                ty->dbg->suppress += 1;

                if (ok) {
                        char *s = Describe(ty, &v, 0);
                        xvPn(out, s, strlen(s));
                        free(s);
                } else {
                        char *s = ErrorText(ty, &v);
                        xvPn(out, "<", 1);
                        xvPn(out, s, strlen(s));
                        xvPn(out, ">", 1);
                        free(s);
                }

                ty->dbg->suppress -= 1;
                vN(ty->stack) -= 1;

                free(src);
                msg = end + 1;
        }

        xvP(out, '\n');
        xvP(out, '\0');

        return vv(out);
}

static void
FreeHits(BreakpointHit *hits, int n)
{
        for (int i = 0; i < n; ++i) {
                free(hits[i].cond);
                free(hits[i].hit);
                free(hits[i].log);
        }

        free(hits);
}

void
DebugTrap(Ty *ty, char *ip)
{
        isize ti;

        pthread_mutex_lock(&D.lock);

        if (!TrapFind(ip, &ti)) {
                u8 op = (u8)*ip;
                pthread_mutex_unlock(&D.lock);
                if (op == INSTR_TRAP_TY) {
                        zP("debugger: unknown trap at %p", (void *)ip);
                }
                return;
        }

        TyDebugThread *d = ty->dbg;

        if (d == NULL) {
                TrapDisarm(ip);
                pthread_mutex_unlock(&D.lock);
                return;
        }

        if (d->agent || d->suppress > 0 || !D.session || d->skip_trap == ip) {
                d->skip_trap = NULL;
                DisarmLocked(d, ip);
                pthread_mutex_unlock(&D.lock);
                return;
        }

        d->skip_trap = NULL;

        BreakpointHit *hits = NULL;
        int nhit = 0;

        for (isize i = 0; i < vN(D.bps); ++i) {
                Breakpoint *bp = v__(D.bps, i);
                for (isize j = 0; j < vN(bp->ips); ++j) {
                        if (v__(bp->ips, j) != ip) {
                                continue;
                        }
                        hits = realloc(hits, (nhit + 1) * sizeof *hits);
                        hits[nhit++] = (BreakpointHit) {
                                .id   = bp->id,
                                .cond = xstrdup(bp->cond),
                                .hit  = xstrdup(bp->hit),
                                .log  = xstrdup(bp->log),
                                .kind = bp->kind
                        };
                        break;
                }
        }

        pthread_mutex_unlock(&D.lock);

        Expr const *ctx = ExprAt(ty, ip);
        i64 *ids = calloc(nhit + 1, sizeof *ids);
        int nstop = 0;
        int reason = REASON_BREAKPOINT;

        for (int i = 0; i < nhit; ++i) {
                BreakpointHit *hit = &hits[i];
                Value v;

                if (hit->cond != NULL) {
                        bool ok = EvalHere(ty, hit->cond, ctx, ScopeFor(ctx), &v);
                        if (ok && !value_truthy(ty, &v)) {
                                continue;
                        }
                }

                i64 count = 0;

                pthread_mutex_lock(&D.lock);
                for (isize j = 0; j < vN(D.bps); ++j) {
                        if (v__(D.bps, j)->id == hit->id) {
                                count = ++v__(D.bps, j)->hits;
                        }
                }
                pthread_mutex_unlock(&D.lock);

                if (!HitConditionMet(hit->hit, count)) {
                        continue;
                }

                if (hit->log != NULL) {
                        char *text = FormatLogMessage(ty, hit->log, ctx);
                        pthread_mutex_lock(&D.lock);
                        PostEvent((DebugEvent) {
                                .kind   = EV_OUTPUT,
                                .thread = d->id,
                                .text   = text
                        });
                        pthread_mutex_unlock(&D.lock);
                        continue;
                }

                if (hit->kind == BP_FUNCTION) {
                        reason = REASON_FUNCTION;
                }

                ids[nstop++] = hit->id;
        }

        FreeHits(hits, nhit);

        if (nstop > 0) {
                StopWorld(ty, d, reason, ip + 1, ids, nstop, NULL, NULL);
        }

        free(ids);

        pthread_mutex_lock(&D.lock);
        DisarmLocked(d, ip);
        pthread_mutex_unlock(&D.lock);
}

void
DebugOnThrow(Ty *ty)
{
        TyDebugThread *d = ty->dbg;

        if (
                (d == NULL)
             || d->agent
             || (d->suppress > 0)
             || !D.session
             || (D.exc_filters == 0)
             || (vN(ty->throw_stack) == 0)
        ) {
                return;
        }

        bool uncaught = !HasHandler(ty);

        if (!(D.exc_filters & EXC_RAISED) && !(uncaught && (D.exc_filters & EXC_UNCAUGHT))) {
                return;
        }

        Value exc = v_L(ty->throw_stack)->exc;

        d->suppress += 1;
        char *text = ErrorText(ty, &exc);
        char *type = xstrdup(DbgTypeName(ty, &exc));
        d->suppress -= 1;

        StopWorld(ty, d, REASON_EXCEPTION, ty->ip, NULL, 0, text, type);
}

static void
ClearBreakpoint(Breakpoint *bp)
{
        for (isize i = 0; i < vN(bp->ips); ++i) {
                TrapDel(v__(bp->ips, i));
        }

        v0(bp->ips);
}

static void
FreeBreakpoint(Breakpoint *bp)
{
        ClearBreakpoint(bp);
        xvF(bp->ips);
        free(bp->path);
        free(bp->name);
        free(bp->cond);
        free(bp->hit);
        free(bp->log);
        free(bp);
}

static bool
IsFunctionExpr(Expr const *e)
{
        return (e->type == EXPRESSION_FUNCTION)
            || (e->type == EXPRESSION_MULTI_FUNCTION)
            || (e->type == EXPRESSION_GENERATOR);
}

static bool
PathMatches(Expr const *e, char const *path)
{
        return (e->mod != NULL)
            && (e->mod->path != NULL)
            && (strcmp(e->mod->path, path) == 0);
}

static int
CollectLine(char const *path, int line, vec(char *) *out)
{
        isize nl;
        location_vector const *lists = compiler_location_lists(&nl);
        int found = 0;

        for (isize l = 0; l < nl; ++l) {
                location_vector const *locs = &lists[l];
                vec(struct { Expr const *fn; uptr ip; }) groups = {0};

                for (isize i = 0; i < vN(*locs); ++i) {
                        struct eloc const *loc = v_(*locs, i);

                        if (
                                (loc->e == NULL)
                             || (loc->e->start.line != line)
                             || (loc->p_start >= loc->p_end)
                             || !PathMatches(loc->e, path)
                        ) {
                                continue;
                        }

                        Expr const *fn = NULL;
                        uptr width = UINTPTR_MAX;

                        for (isize j = 0; j < vN(*locs); ++j) {
                                struct eloc const *f = v_(*locs, j);
                                if (
                                        (f->e != loc->e)
                                     && IsFunctionExpr(f->e)
                                     && (f->p_start < loc->p_start)
                                     && (loc->p_start < f->p_end)
                                     && (f->p_end - f->p_start < width)
                                ) {
                                        fn = f->e;
                                        width = f->p_end - f->p_start;
                                }
                        }

                        bool merged = false;

                        for (isize g = 0; g < vN(groups); ++g) {
                                if (v_(groups, g)->fn == fn) {
                                        if (loc->p_start < v_(groups, g)->ip) {
                                                v_(groups, g)->ip = loc->p_start;
                                        }
                                        merged = true;
                                        break;
                                }
                        }

                        if (!merged) {
                                xvP(groups, ((typeof(*vv(groups))) { .fn = fn, .ip = loc->p_start }));
                        }
                }

                for (isize g = 0; g < vN(groups); ++g) {
                        char *ip = (char *)v_(groups, g)->ip;
                        bool dup = false;
                        for (isize k = 0; k < vN(*out); ++k) {
                                dup |= (v__(*out, k) == ip);
                        }
                        if (!dup) {
                                xvP(*out, ip);
                                found += 1;
                        }
                }

                xvF(groups);
        }

        return found;
}

static void
ResolveLine(Breakpoint *bp)
{
        pthread_mutex_lock(&LocLock);

        for (int delta = 0; delta < 64; ++delta) {
                if (CollectLine(bp->path, bp->line + delta, (void *)&bp->ips) > 0) {
                        bp->actual = bp->line + delta;
                        break;
                }
        }

        pthread_mutex_unlock(&LocLock);
}

static Value const *
LookupGlobal(Ty *ty, char const *name)
{
        symbol_vector *globals = compiler_globals(ty);

        for (isize i = vN(*globals) - 1; i >= 0; --i) {
                Symbol const *sym = v__(*globals, i);
                if (
                        (sym != NULL)
                     && (i < vN(Globals))
                     && (strcmp(sym->identifier, name) == 0)
                ) {
                        return v_(Globals, i);
                }
        }

        return NULL;
}

static char *
CodeOfCallable(Ty *ty, Value const *v)
{
        switch (v->type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                return code_of(v);

        case VALUE_METHOD:
                return (v->method->type == VALUE_FUNCTION) ? code_of(v->method) : NULL;

        default:
                return NULL;
        }
}

static void
ResolveFunction(Ty *ty, Breakpoint *bp)
{
        char *name = bp->name;
        char *dot = strrchr(name, '.');
        char *ip = NULL;

        if (dot == NULL) {
                Value const *v = LookupGlobal(ty, name);
                ip = (v != NULL) ? CodeOfCallable(ty, v) : NULL;
        } else {
                *dot = '\0';
                Value const *class = LookupGlobal(ty, name);
                *dot = '.';
                if (class != NULL && class->type == VALUE_CLASS) {
                        Value *m = class_lookup_method_i(ty, class->class, M_ID(dot + 1));
                        if (m == NULL) {
                                m = class_lookup_s_method_i(ty, class->class, M_ID(dot + 1));
                        }
                        ip = (m != NULL) ? CodeOfCallable(ty, m) : NULL;
                }
        }

        if (ip != NULL) {
                xvP(bp->ips, ip);
                Expr const *e = ExprAt(ty, ip);
                bp->actual = (e != NULL) ? e->start.line : -1;
        }
}

static void
Resolve(Ty *ty, Breakpoint *bp)
{
        if (bp->verified) {
                return;
        }

        if (bp->kind == BP_LINE) {
                ResolveLine(bp);
        } else {
                ResolveFunction(ty, bp);
        }

        for (isize i = 0; i < vN(bp->ips); ++i) {
                TrapAdd(v__(bp->ips, i));
        }

        bp->verified = (vN(bp->ips) > 0);
}

void
DebugCodeLoaded(Ty *ty)
{
        if (!D.session) {
                return;
        }

        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.bps); ++i) {
                Breakpoint *bp = v__(D.bps, i);
                if (bp->verified || bp->kind != BP_LINE) {
                        continue;
                }
                Resolve(ty, bp);
                if (bp->verified) {
                        PostEvent((DebugEvent) { .kind = EV_BREAKPOINT, .bp = bp->id });
                }
        }

        pthread_mutex_unlock(&D.lock);
}

void
DebugMarkRoots(Ty *ty)
{
        for (isize i = 0; i < vN(D.handles); ++i) {
                Handle *h = v_(D.handles, i);
                if (h->kind == H_VALUE && h->mark) {
                        value_mark(ty, &h->v);
                }
        }

        value_mark(ty, &D.job_result);
}

void
DebugThreadStart(Ty *ty, TyThread self)
{
        TyDebugThread *d = calloc(1, sizeof *d);

        d->ty     = ty;
        d->id     = ty->id + 1;
        d->thread = self;
        d->agent  = AgentThread;
        d->state  = DBG_RUNNING;

        ty->dbg = d;

        pthread_mutex_lock(&D.lock);
        xvP(D.threads, d);
        d->registered = true;
        if (D.session && !d->agent) {
                PostEvent((DebugEvent) { .kind = EV_THREAD_START, .thread = d->id });
        }
        pthread_mutex_unlock(&D.lock);
}

void
DebugThreadExit(Ty *ty)
{
        TyDebugThread *d = ty->dbg;

        if (d == NULL) {
                return;
        }

        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.threads); ++i) {
                if (v__(D.threads, i) == d) {
                        v__(D.threads, i) = vXx(D.threads);
                        break;
                }
        }

        if (D.session && !d->agent) {
                PostEvent((DebugEvent) { .kind = EV_THREAD_EXIT, .thread = d->id });
        }

        if (D.stopper == d) {
                D.stopper = NULL;
        }

        RearmLocked(d);

        ty->dbg = NULL;

        pthread_cond_broadcast(&D.cond);
        pthread_mutex_unlock(&D.lock);

        free(d);
}

static bool
AnyStepping(void)
{
        for (isize i = 0; i < vN(D.threads); ++i) {
                if (v__(D.threads, i)->step != STEP_NONE) {
                        return true;
                }
        }

        return false;
}

static void
ResumeWorld(void)
{
        D.stopped = false;
        D.stopper = NULL;
        D.gen += 1;

        free(D.text);
        free(D.exc_type);
        D.text = NULL;
        D.exc_type = NULL;

        v0(D.hits);
        v0(D.frames);
        v0(D.handles);
        D.job_result = NIL;

        RecomputeInterrupt();

        pthread_cond_broadcast(&D.cond);
}

static bool
AllQuiet(void)
{
        for (isize i = 0; i < vN(D.threads); ++i) {
                TyDebugThread *d = v__(D.threads, i);
                int state = d->state;
                if (!d->agent && state != DBG_PARKED && state != DBG_BLOCKED) {
                        return false;
                }
        }

        return true;
}

static void
WaitQuiet(void)
{
        struct timespec deadline;

        clock_gettime(CLOCK_REALTIME, &deadline);
        deadline.tv_sec += 3;

        while (D.stopped && !AllQuiet()) {
                if (pthread_cond_timedwait(&D.cond, &D.lock, &deadline) == ETIMEDOUT) {
                        break;
                }
        }
}

static void
AgentUnlock(Ty *ty)
{
        ReleaseLock(ty, true);
}

static void
AgentLock(Ty *ty)
{
        vm_take_lock_raw(ty);
}

static void
Detach(Ty *ty)
{
        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.bps); ++i) {
                FreeBreakpoint(v__(D.bps, i));
        }

        v0(D.bps);

        for (isize i = 0; i < vN(D.threads); ++i) {
                v__(D.threads, i)->step = STEP_NONE;
                v__(D.threads, i)->skip_trap = NULL;
        }

        D.exc_filters = 0;
        D.session = false;

        if (D.stopped) {
                ResumeWorld();
        }

        RecomputeInterrupt();
        DebugJitOff = 0;

        for (isize i = 0; i < vN(D.events); ++i) {
                free(v_(D.events, i)->text);
        }

        v0(D.events);
        v0(D.sources);

        pthread_mutex_unlock(&D.lock);
}

static void
Canonical(char const *path, char *out, usize n)
{
        char buf[PATH_MAX];

        if (realpath(path, buf) != NULL) {
                snprintf(out, n, "%s", buf);
        } else {
                snprintf(out, n, "%s", path);
        }
}

static int
OutLine(int line)
{
        return line + (D.lines1 ? 1 : 0);
}

static int
InLine(i64 line)
{
        return (int)line - (D.lines1 ? 1 : 0);
}

static int
OutCol(int col)
{
        return col + (D.cols1 ? 1 : 0);
}

static i64
SourceRef(Module const *mod)
{
        for (isize i = 0; i < vN(D.sources); ++i) {
                if (v__(D.sources, i) == mod) {
                        return i + 1;
                }
        }

        xvP(D.sources, mod);

        return vN(D.sources);
}

static void
WriteSource(JsonWriter *w, Module const *mod)
{
        jw_open(w, '{');

        char const *slash = (mod->path != NULL) ? strrchr(mod->path, '/') : NULL;
        jw_kstr(w, "name", (slash != NULL) ? slash + 1 : mod->name);

        if (IsSourcePath(mod->path)) {
                jw_kstr(w, "path", mod->path);
        } else {
                jw_kint(w, "sourceReference", SourceRef(mod));
        }

        jw_close(w, '}');
}

static void
WriteBreakpoint(JsonWriter *w, Breakpoint const *bp)
{
        jw_open(w, '{');
        jw_kint(w, "id", bp->id);
        jw_kbool(w, "verified", bp->verified);

        if (bp->verified && bp->actual >= 0) {
                jw_kint(w, "line", OutLine(bp->actual));
        } else if (bp->kind == BP_LINE) {
                jw_kint(w, "line", OutLine(bp->line));
        }

        if (!bp->verified) {
                jw_kstr(w, "message", (bp->kind == BP_LINE) ? "No code at this location (yet)" : "Function not found (yet)");
        }

        jw_close(w, '}');
}

static Breakpoint *
NewBreakpoint(Json const *spec, int kind)
{
        Breakpoint *bp = calloc(1, sizeof *bp);

        bp->id     = ++D.next_bp;
        bp->kind   = kind;
        bp->actual = -1;
        bp->cond   = xstrdup(JStr(spec, "condition"));
        bp->hit    = xstrdup(JStr(spec, "hitCondition"));
        bp->log    = xstrdup(JStr(spec, "logMessage"));

        if (bp->cond != NULL && bp->cond[0] == '\0') {
                free(bp->cond);
                bp->cond = NULL;
        }

        if (bp->hit != NULL && bp->hit[0] == '\0') {
                free(bp->hit);
                bp->hit = NULL;
        }

        return bp;
}

static void
ReqSetBreakpoints(Ty *ty, Json const *req, Json const *args)
{
        Json const *source = JGet(args, "source");
        char const *raw = JStr(source, "path");

        if (raw == NULL) {
                Respond(req, "source.path is required", NULL);
                return;
        }

        char path[PATH_MAX];
        Canonical(raw, path, sizeof path);

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "breakpoints");
        jw_open(&body, '[');

        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.bps); ++i) {
                Breakpoint *bp = v__(D.bps, i);
                if (bp->kind == BP_LINE && strcmp(bp->path, path) == 0) {
                        FreeBreakpoint(bp);
                        v__(D.bps, i--) = vXx(D.bps);
                }
        }

        Json const *list = JGet(args, "breakpoints");

        for (Json const *it = (list != NULL) ? list->child : NULL; it != NULL; it = it->next) {
                Breakpoint *bp = NewBreakpoint(it, BP_LINE);
                bp->path = xstrdup(path);
                bp->line = InLine(JInt(it, "line", 1));
                Resolve(ty, bp);
                xvP(D.bps, bp);
                WriteBreakpoint(&body, bp);
        }

        pthread_mutex_unlock(&D.lock);

        jw_close(&body, ']');
        jw_close(&body, '}');

        Respond(req, NULL, &body);
}

static void
ReqSetFunctionBreakpoints(Ty *ty, Json const *req, Json const *args)
{
        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "breakpoints");
        jw_open(&body, '[');

        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.bps); ++i) {
                Breakpoint *bp = v__(D.bps, i);
                if (bp->kind == BP_FUNCTION) {
                        FreeBreakpoint(bp);
                        v__(D.bps, i--) = vXx(D.bps);
                }
        }

        Json const *list = JGet(args, "breakpoints");

        for (Json const *it = (list != NULL) ? list->child : NULL; it != NULL; it = it->next) {
                char const *name = JStr(it, "name");
                if (name == NULL) {
                        continue;
                }
                Breakpoint *bp = NewBreakpoint(it, BP_FUNCTION);
                bp->name = xstrdup(name);
                Resolve(ty, bp);
                xvP(D.bps, bp);
                WriteBreakpoint(&body, bp);
        }

        pthread_mutex_unlock(&D.lock);

        jw_close(&body, ']');
        jw_close(&body, '}');

        Respond(req, NULL, &body);
}

static void
ReqSetExceptionBreakpoints(Ty *ty, Json const *req, Json const *args)
{
        int filters = 0;
        Json const *list = JGet(args, "filters");

        for (Json const *it = (list != NULL) ? list->child : NULL; it != NULL; it = it->next) {
                if (it->kind != J_STR) {
                        continue;
                }
                if (strcmp(it->s, "raised") == 0) {
                        filters |= EXC_RAISED;
                }
                if (strcmp(it->s, "uncaught") == 0) {
                        filters |= EXC_UNCAUGHT;
                }
        }

        pthread_mutex_lock(&D.lock);
        D.exc_filters = filters;
        pthread_mutex_unlock(&D.lock);

        Respond(req, NULL, NULL);
}

static void
ReqBreakpointLocations(Ty *ty, Json const *req, Json const *args)
{
        char const *raw = JStr(JGet(args, "source"), "path");

        if (raw == NULL) {
                Respond(req, "source.path is required", NULL);
                return;
        }

        char path[PATH_MAX];
        Canonical(raw, path, sizeof path);

        int lo = InLine(JInt(args, "line", 1));
        int hi = InLine(JInt(args, "endLine", JInt(args, "line", 1)));

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "breakpoints");
        jw_open(&body, '[');

        pthread_mutex_lock(&LocLock);

        for (int line = lo; line <= hi && line - lo < 10000; ++line) {
                vec(char *) ips = {0};
                if (CollectLine(path, line, (void *)&ips) > 0) {
                        jw_open(&body, '{');
                        jw_kint(&body, "line", OutLine(line));
                        jw_close(&body, '}');
                }
                xvF(ips);
        }

        pthread_mutex_unlock(&LocLock);

        jw_close(&body, ']');
        jw_close(&body, '}');

        Respond(req, NULL, &body);
}

static void
ThreadName(TyDebugThread const *d, char *buf, usize n)
{
        char name[64] = {0};

        pthread_getname_np(d->thread, name, sizeof name);

        if (name[0] != '\0') {
                snprintf(buf, n, "%s", name);
        } else if (d->id == 1) {
                snprintf(buf, n, "main");
        } else {
                snprintf(buf, n, "Thread %llu", (unsigned long long)d->id);
        }
}

static void
ReqThreads(Ty *ty, Json const *req, Json const *args)
{
        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "threads");
        jw_open(&body, '[');

        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.threads); ++i) {
                TyDebugThread const *d = v__(D.threads, i);
                char name[128];
                if (d->agent) {
                        continue;
                }
                ThreadName(d, name, sizeof name);
                jw_open(&body, '{');
                jw_kint(&body, "id", d->id);
                jw_kstr(&body, "name", name);
                jw_close(&body, '}');
        }

        pthread_mutex_unlock(&D.lock);

        jw_close(&body, ']');
        jw_close(&body, '}');

        Respond(req, NULL, &body);
}

static char const *
FrameName(Ty *ty, DebugFrame const *f, char *buf, usize n)
{
        if (f->has_fun) {
                Expr const *fexp = expr_of(&f->fun);
                char const *name = (fexp != NULL) ? QualifiedName(fexp) : NULL;
                if (name == NULL) {
                        name = name_of(&f->fun);
                }
                snprintf(buf, n, "%s", (name != NULL) ? name : "<anonymous>");
        } else {
                Expr const *e = ExprAt(ty, f->ip - 1);
                snprintf(buf, n, "<module %s>", (e != NULL && e->mod != NULL) ? e->mod->name : "?");
        }

        return buf;
}

static bool
Inspectable(TyDebugThread const *d)
{
        int state = d->state;
        return D.stopped && (state == DBG_PARKED || state == DBG_BLOCKED);
}

static void
ReqStackTrace(Ty *ty, Json const *req, Json const *args)
{
        pthread_mutex_lock(&D.lock);

        TyDebugThread *d = ThreadById(JInt(args, "threadId", 0));

        if (d == NULL || !Inspectable(d)) {
                pthread_mutex_unlock(&D.lock);
                Respond(req, "thread is not stopped", NULL);
                return;
        }

        DebugFrameVector frames = {0};
        WalkFrames(d, &frames);

        isize start = JInt(args, "startFrame", 0);
        isize levels = JInt(args, "levels", 0);
        isize end = (levels > 0) ? min(start + levels, vN(frames)) : vN(frames);

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "stackFrames");
        jw_open(&body, '[');

        for (isize i = start; i < end; ++i) {
                DebugFrame const *f = v_(frames, i);
                Expr const *e = ExprAt(ty, f->ip - 1);
                char name[256];

                xvP(D.frames, ((FrameRef) { .f = *f, .d = d }));

                jw_open(&body, '{');
                jw_kint(&body, "id", vN(D.frames));
                jw_kstr(&body, "name", FrameName(ty, f, name, sizeof name));

                if (e != NULL && e->mod != NULL) {
                        jw_key(&body, "source");
                        WriteSource(&body, e->mod);
                        jw_kint(&body, "line", OutLine(e->start.line));
                        jw_kint(&body, "column", OutCol(e->start.col));
                        jw_kint(&body, "endLine", OutLine(e->end.line));
                        jw_kint(&body, "endColumn", OutCol(e->end.col));
                } else {
                        jw_kint(&body, "line", 0);
                        jw_kint(&body, "column", 0);
                        jw_kstr(&body, "presentationHint", "subtle");
                }

                jw_close(&body, '}');
        }

        jw_close(&body, ']');
        jw_kint(&body, "totalFrames", vN(frames));
        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        xvF(frames);

        Respond(req, NULL, &body);
}

static i64
NewHandle(int kind, isize frame, Module const *mod, Value const *v, bool mark)
{
        for (isize i = 0; i < vN(D.handles); ++i) {
                Handle const *h = v_(D.handles, i);
                if (
                        (h->kind == kind)
                     && (h->frame == frame)
                     && (kind != H_VALUE)
                ) {
                        return i + 1;
                }
        }

        xvP(D.handles, ((Handle) {
                .kind  = kind,
                .frame = frame,
                .mod   = mod,
                .v     = (v != NULL) ? *v : NIL,
                .mark  = mark
        }));

        return vN(D.handles);
}

static FrameRef *
FrameById(i64 id)
{
        return (id >= 1 && id <= vN(D.frames)) ? v_(D.frames, id - 1) : NULL;
}

static bool
FrameMarks(Ty *ty, FrameRef const *fr)
{
        return (fr == NULL) || (fr->f.ty->group == ty->group);
}

static void
ReqScopes(Ty *ty, Json const *req, Json const *args)
{
        pthread_mutex_lock(&D.lock);

        i64 id = JInt(args, "frameId", 0);
        FrameRef *fr = FrameById(id);

        if (fr == NULL) {
                pthread_mutex_unlock(&D.lock);
                Respond(req, "invalid frame", NULL);
                return;
        }

        Expr const *e = ExprAt(ty, fr->f.ip - 1);
        Module const *mod = (e != NULL) ? e->mod : NULL;
        Expr const *fexp = fr->f.has_fun ? expr_of(&fr->f.fun) : NULL;

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "scopes");
        jw_open(&body, '[');

        if (fexp != NULL && fexp->scope != NULL) {
                jw_open(&body, '{');
                jw_kstr(&body, "name", "Locals");
                jw_kstr(&body, "presentationHint", "locals");
                jw_kint(&body, "variablesReference", NewHandle(H_LOCALS, id - 1, mod, NULL, false));
                jw_kbool(&body, "expensive", false);
                jw_close(&body, '}');

                if (vN(fexp->scope->captured) > 0 && fr->f.fun.env != NULL) {
                        jw_open(&body, '{');
                        jw_kstr(&body, "name", "Closure");
                        jw_kint(&body, "variablesReference", NewHandle(H_CLOSURE, id - 1, mod, NULL, false));
                        jw_kbool(&body, "expensive", false);
                        jw_close(&body, '}');
                }
        }

        if (mod != NULL) {
                jw_open(&body, '{');
                jw_kstr(&body, "name", "Globals");
                jw_kint(&body, "variablesReference", NewHandle(H_GLOBALS, id - 1, mod, NULL, false));
                jw_kbool(&body, "expensive", fexp != NULL);
                jw_close(&body, '}');
        }

        jw_close(&body, ']');
        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        Respond(req, NULL, &body);
}

static void
WriteVariable(Ty *ty, JsonWriter *w, char const *name, Value const *v, isize frame, bool mark, char const *eval)
{
        Value x = Deref(v);
        char *preview = PreviewString(ty, &x);

        jw_open(w, '{');
        jw_kstr(w, "name", name);
        jw_kstr(w, "value", preview);
        jw_kstr(w, "type", DbgTypeName(ty, &x));

        if (eval != NULL) {
                jw_kstr(w, "evaluateName", eval);
        }

        if (IsStructured(ty, &x)) {
                jw_kint(w, "variablesReference", NewHandle(H_VALUE, frame, NULL, &x, mark));
                Value u = Untag(ty, &x);
                if (u.type == VALUE_ARRAY) {
                        jw_kint(w, "indexedVariables", vN(*u.array));
                }
        } else {
                jw_kint(w, "variablesReference", 0);
        }

        jw_close(w, '}');

        free(preview);
}

static bool
VisibleName(char const *name)
{
        return (name != NULL)
            && (name[0] != '\0')
            && (strchr("$*@#:(", name[0]) == NULL);
}

static isize
ScopeDistance(Scope const *from, Scope const *target)
{
        isize n = 0;

        for (Scope const *s = from; s != NULL; s = s->parent, ++n) {
                if (s == target) {
                        return n;
                }
        }

        return -1;
}

static void
WriteLocals(Ty *ty, JsonWriter *w, FrameRef const *fr, isize frame, bool mark)
{
        Expr const *fexp = expr_of(&fr->f.fun);
        Scope const *scope = fexp->scope;
        Expr const *ctx = ExprAt(ty, fr->f.ip - 1);
        Scope const *at = (ctx != NULL) ? ctx->xscope : NULL;
        isize n = min(vN(scope->owned), fr->f.nslot);

        for (isize i = 0; i < n; ++i) {
                Symbol const *sym = v__(scope->owned, i);

                if (sym == NULL || !VisibleName(sym->identifier)) {
                        continue;
                }

                isize dist = (at != NULL) ? ScopeDistance(at, sym->scope) : 0;

                if (dist < 0) {
                        continue;
                }

                bool shadowed = false;

                for (isize j = 0; j < n && !shadowed; ++j) {
                        Symbol const *other = v__(scope->owned, j);
                        if (
                                (j != i)
                             && (other != NULL)
                             && (strcmp(other->identifier, sym->identifier) == 0)
                        ) {
                                isize d2 = (at != NULL) ? ScopeDistance(at, other->scope) : 0;
                                shadowed = (d2 >= 0) && ((d2 < dist) || (d2 == dist && j > i));
                        }
                }

                Value *slot = FrameSlot(&fr->f, i);

                if (shadowed || slot == NULL) {
                        continue;
                }

                WriteVariable(ty, w, sym->identifier, slot, frame, mark, sym->identifier);
        }
}

static void
WriteClosure(Ty *ty, JsonWriter *w, FrameRef const *fr, isize frame, bool mark)
{
        Expr const *fexp = expr_of(&fr->f.fun);
        Scope const *scope = fexp->scope;

        for (isize i = 0; i < vN(scope->captured); ++i) {
                Symbol const *sym = v__(scope->captured, i);
                Value *cell = fr->f.fun.env[i];

                if (sym == NULL || cell == NULL || !VisibleName(sym->identifier)) {
                        continue;
                }

                WriteVariable(ty, w, sym->identifier, cell, frame, mark, sym->identifier);
        }
}

static void
WriteGlobals(Ty *ty, JsonWriter *w, Module const *mod, isize frame)
{
        symbol_vector *globals = compiler_globals(ty);
        u32 skip = SYM_FUNCTION
                 | SYM_CLASS
                 | SYM_TAG
                 | SYM_MACRO
                 | SYM_FUN_MACRO
                 | SYM_NAMESPACE
                 | SYM_TYPE_VAR
                 | SYM_TYPE_ALIAS
                 | SYM_BUILTIN
                 | SYM_EXTERNAL
                 | SYM_MEMBER
                 | SYM_OPERATOR;

        for (isize i = 0; i < vN(*globals) && i < vN(Globals); ++i) {
                Symbol const *sym = v__(*globals, i);

                if (
                        (sym == NULL)
                     || (sym->mod != mod)
                     || (sym->flags & skip)
                     || !VisibleName(sym->identifier)
                ) {
                        continue;
                }

                WriteVariable(ty, w, sym->identifier, v_(Globals, i), frame, true, sym->identifier);
        }
}

static void
WriteChildren(Ty *ty, JsonWriter *w, Handle const *h, isize start, isize count)
{
        Value x = Untag(ty, &h->v);
        char name[64];

        switch (x.type) {
        case VALUE_ARRAY:
        {
                isize end = (count > 0) ? min(start + count, vN(*x.array)) : vN(*x.array);
                for (isize i = start; i < end; ++i) {
                        snprintf(name, sizeof name, "[%lld]", (long long)i);
                        WriteVariable(ty, w, name, v_(*x.array, i), h->frame, h->mark, NULL);
                }
                break;
        }

        case VALUE_TUPLE:
                for (isize i = 0; i < x.count; ++i) {
                        if (x.ids != NULL && x.ids[i] >= 0) {
                                snprintf(name, sizeof name, "%s", M_NAME(x.ids[i]));
                        } else {
                                snprintf(name, sizeof name, "[%lld]", (long long)i);
                        }
                        WriteVariable(ty, w, name, &x.items[i], h->frame, h->mark, NULL);
                }
                break;

        case VALUE_DICT:
        {
                isize i = 0;
                for (DictItem *it = DictFirst(x.dict); it != NULL && i < 10000; it = it->next, ++i) {
                        char *key = PreviewString(ty, &it->k);
                        WriteVariable(ty, w, key, &it->v, h->frame, h->mark, NULL);
                        free(key);
                }
                break;
        }

        case VALUE_OBJECT:
        {
                TyObject const *obj = x.object;
                Class const *class = obj->class;
                for (u32 i = 0; i < obj->nslot && i < vN(class->fields.ids); ++i) {
                        WriteVariable(ty, w, M_NAME(v__(class->fields.ids, i)), &obj->slots[i], h->frame, h->mark, NULL);
                }
                if (obj->dynamic != NULL) {
                        for (isize i = 0; i < vN(obj->dynamic->ids); ++i) {
                                WriteVariable(ty, w, M_NAME(v__(obj->dynamic->ids, i)), v_(obj->dynamic->values, i), h->frame, h->mark, NULL);
                        }
                }
                break;
        }
        }
}

static void
ReqVariables(Ty *ty, Json const *req, Json const *args)
{
        pthread_mutex_lock(&D.lock);

        i64 ref = JInt(args, "variablesReference", 0);

        if (ref < 1 || ref > vN(D.handles)) {
                pthread_mutex_unlock(&D.lock);
                Respond(req, "invalid variablesReference", NULL);
                return;
        }

        Handle h = v__(D.handles, ref - 1);
        FrameRef *fr = (h.frame >= 0) ? v_(D.frames, h.frame) : NULL;
        bool mark = FrameMarks(ty, fr);

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_key(&body, "variables");
        jw_open(&body, '[');

        switch (h.kind) {
        case H_LOCALS:
                WriteLocals(ty, &body, fr, h.frame, mark);
                break;

        case H_CLOSURE:
                WriteClosure(ty, &body, fr, h.frame, mark);
                break;

        case H_GLOBALS:
                WriteGlobals(ty, &body, h.mod, h.frame);
                break;

        case H_VALUE:
                WriteChildren(ty, &body, &h, JInt(args, "start", 0), JInt(args, "count", 0));
                break;
        }

        jw_close(&body, ']');
        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        Respond(req, NULL, &body);
}

static Module const *
MainModule(Ty *ty)
{
        pthread_mutex_lock(&D.lock);

        TyDebugThread *main = ThreadById(1);

        if (main == NULL || !Inspectable(main)) {
                pthread_mutex_unlock(&D.lock);
                return NULL;
        }

        DebugFrameVector frames = {0};
        WalkFrames(main, &frames);

        Module const *mod = NULL;

        if (vN(frames) > 0) {
                Expr const *e = ExprAt(ty, vvL(frames)->ip - 1);
                mod = (e != NULL) ? e->mod : NULL;
        }

        pthread_mutex_unlock(&D.lock);

        xvF(frames);

        return mod;
}

static bool
Evaluate(Ty *ty, FrameRef *fr, char const *src, char **text, char **type, Value *result)
{
        TyDebugThread *d = (fr != NULL) ? fr->d : NULL;

        if (d != NULL && d->state == DBG_PARKED) {
                DebugJob job = {
                        .st    = fr->f.st,
                        .index = fr->f.index,
                        .ip    = fr->f.ip,
                        .src   = src
                };

                AgentUnlock(ty);

                pthread_mutex_lock(&D.lock);
                d->job = &job;
                pthread_cond_broadcast(&D.cond);
                while (!job.done) {
                        pthread_cond_wait(&D.cond, &D.lock);
                }
                *result = D.job_result;
                pthread_mutex_unlock(&D.lock);

                AgentLock(ty);

                *text = job.text;
                *type = job.type;

                return job.ok;
        }

        Expr const *ctx = (fr != NULL) ? ExprAt(ty, fr->f.ip - 1) : NULL;
        Module const *mod = (ctx != NULL) ? ctx->mod : MainModule(ty);
        Scope *scope = (mod != NULL) ? mod->scope : NULL;
        Value v;

        bool ok = EvalHere(ty, src, ctx, scope, &v);

        xvP(ty->stack, v);

        if (ok) {
                *text = Describe(ty, &v, TY_SHOW_REPR);
                *type = xstrdup(DbgTypeName(ty, &v));
                *result = v;
        } else {
                *text = ErrorText(ty, &v);
                *type = NULL;
                *result = NIL;
        }

        vN(ty->stack) -= 1;

        return ok;
}

static void
ReqEvaluate(Ty *ty, Json const *req, Json const *args)
{
        char const *expr = JStr(args, "expression");

        if (expr == NULL) {
                Respond(req, "expression is required", NULL);
                return;
        }

        i64 fid = JInt(args, "frameId", 0);

        pthread_mutex_lock(&D.lock);
        FrameRef *fr = FrameById(fid);
        FrameRef copy = (fr != NULL) ? *fr : (FrameRef) {0};
        bool stopped = D.stopped;
        pthread_mutex_unlock(&D.lock);

        if (!stopped && fr != NULL) {
                Respond(req, "the program is running", NULL);
                return;
        }

        char *text = NULL;
        char *type = NULL;
        Value v = NIL;

        bool ok = Evaluate(ty, (fr != NULL) ? &copy : NULL, expr, &text, &type, &v);

        if (!ok) {
                Respond(req, text, NULL);
                free(text);
                free(type);
                return;
        }

        JsonWriter body = {0};

        pthread_mutex_lock(&D.lock);

        jw_open(&body, '{');
        jw_kstr(&body, "result", text);

        if (type != NULL) {
                jw_kstr(&body, "type", type);
        }

        isize frame = (fr != NULL) ? (fid - 1) : -1;

        jw_kint(
                &body,
                "variablesReference",
                (stopped && IsStructured(ty, &v))
                ? NewHandle(H_VALUE, frame, NULL, &v, FrameMarks(ty, (fr != NULL) ? &copy : NULL))
                : 0
        );

        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        free(text);
        free(type);

        Respond(req, NULL, &body);
}

static void
ReqSetVariable(Ty *ty, Json const *req, Json const *args)
{
        char const *name = JStr(args, "name");
        char const *value = JStr(args, "value");

        pthread_mutex_lock(&D.lock);

        i64 ref = JInt(args, "variablesReference", 0);

        if (name == NULL || value == NULL || ref < 1 || ref > vN(D.handles) || !D.stopped) {
                pthread_mutex_unlock(&D.lock);
                Respond(req, "invalid setVariable request", NULL);
                return;
        }

        Handle h = v__(D.handles, ref - 1);
        FrameRef copy = (h.frame >= 0) ? v__(D.frames, h.frame) : (FrameRef) {0};
        FrameRef *fr = (h.frame >= 0) ? &copy : NULL;

        pthread_mutex_unlock(&D.lock);

        byte_vector src = {0};
        char *text = NULL;
        char *type = NULL;
        Value v;
        bool ok;

        if (h.kind != H_VALUE) {
                xvPn(src, name, strlen(name));
                xvPn(src, " = (", 4);
                xvPn(src, value, strlen(value));
                xvP(src, ')');
                xvP(src, '\0');
                ok = Evaluate(ty, fr, vv(src), &text, &type, &v);
        } else {
                ok = Evaluate(ty, fr, value, &text, &type, &v);
                Value x = Untag(ty, &h.v);
                if (ok && x.type == VALUE_ARRAY && name[0] == '[') {
                        isize i = strtoll(name + 1, NULL, 10);
                        ok = (i >= 0 && i < vN(*x.array));
                        if (ok) {
                                *v_(*x.array, i) = v;
                        }
                } else if (ok && x.type == VALUE_OBJECT) {
                        Class const *class = x.object->class;
                        ok = false;
                        for (u32 i = 0; i < x.object->nslot && i < vN(class->fields.ids); ++i) {
                                if (strcmp(M_NAME(v__(class->fields.ids, i)), name) == 0) {
                                        x.object->slots[i] = v;
                                        ok = true;
                                }
                        }
                } else if (ok) {
                        ok = false;
                }
        }

        xvF(src);

        if (!ok) {
                Respond(req, (text != NULL) ? text : "cannot assign to this variable", NULL);
                free(text);
                free(type);
                return;
        }

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kstr(&body, "value", text);
        jw_close(&body, '}');

        free(text);
        free(type);

        Respond(req, NULL, &body);
}

static void
ReqExceptionInfo(Ty *ty, Json const *req, Json const *args)
{
        pthread_mutex_lock(&D.lock);

        if (!D.stopped || D.reason != REASON_EXCEPTION) {
                pthread_mutex_unlock(&D.lock);
                Respond(req, "not stopped on an exception", NULL);
                return;
        }

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kstr(&body, "exceptionId", (D.exc_type != NULL) ? D.exc_type : "Error");
        jw_kstr(&body, "description", D.text);
        jw_kstr(&body, "breakMode", (D.exc_filters & EXC_RAISED) ? "always" : "unhandled");
        jw_key(&body, "details");
        jw_open(&body, '{');
        jw_kstr(&body, "message", D.text);
        jw_kstr(&body, "typeName", D.exc_type);
        jw_close(&body, '}');
        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        Respond(req, NULL, &body);
}

static void
ReqSource(Ty *ty, Json const *req, Json const *args)
{
        i64 ref = JInt(args, "sourceReference", 0);
        char const *path = JStr(JGet(args, "source"), "path");
        char const *text = NULL;

        pthread_mutex_lock(&D.lock);

        if (ref >= 1 && ref <= vN(D.sources)) {
                text = v__(D.sources, ref - 1)->source;
        }

        pthread_mutex_unlock(&D.lock);

        if (text == NULL && path != NULL) {
                isize nl;
                pthread_mutex_lock(&LocLock);
                location_vector const *lists = compiler_location_lists(&nl);
                for (isize l = 0; l < nl && text == NULL; ++l) {
                        if (vN(lists[l]) > 0 && PathMatches(v_(lists[l], 0)->e, path)) {
                                text = v_(lists[l], 0)->e->mod->source;
                        }
                }
                pthread_mutex_unlock(&LocLock);
        }

        if (text == NULL) {
                Respond(req, "source not available", NULL);
                return;
        }

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kstr(&body, "content", text);
        jw_close(&body, '}');

        Respond(req, NULL, &body);
}

static void
ReqLoadedSources(Ty *ty, Json const *req, Json const *args)
{
        vec(Module const *) mods = {0};
        isize nl;

        pthread_mutex_lock(&LocLock);

        location_vector const *lists = compiler_location_lists(&nl);

        for (isize l = 0; l < nl; ++l) {
                if (vN(lists[l]) == 0 || v_(lists[l], 0)->e == NULL) {
                        continue;
                }
                Module const *mod = v_(lists[l], 0)->e->mod;
                bool seen = (mod == NULL) || !IsSourcePath(mod->path);
                for (isize i = 0; i < vN(mods) && !seen; ++i) {
                        seen = (v__(mods, i) == mod);
                }
                if (!seen) {
                        xvP(mods, mod);
                }
        }

        pthread_mutex_unlock(&LocLock);

        JsonWriter body = {0};

        pthread_mutex_lock(&D.lock);

        jw_open(&body, '{');
        jw_key(&body, "sources");
        jw_open(&body, '[');

        for (isize i = 0; i < vN(mods); ++i) {
                WriteSource(&body, v__(mods, i));
        }

        jw_close(&body, ']');
        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        xvF(mods);

        Respond(req, NULL, &body);
}

static void
ReqResume(Ty *ty, Json const *req, Json const *args, int step)
{
        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.threads); ++i) {
                v__(D.threads, i)->step = STEP_NONE;
        }

        if (!D.stopped) {
                pthread_mutex_unlock(&D.lock);
                Respond(req, "the program is not stopped", NULL);
                return;
        }

        if (step != STEP_NONE) {
                TyDebugThread *d = ThreadById(JInt(args, "threadId", 0));
                char const *granularity = JStr(args, "granularity");

                if (d == NULL) {
                        pthread_mutex_unlock(&D.lock);
                        Respond(req, "invalid thread", NULL);
                        return;
                }

                if (granularity != NULL && strcmp(granularity, "instruction") == 0) {
                        step = STEP_INSN;
                }

                char const *ip = (d->state == DBG_PARKED) ? d->stop_ip : d->ty->ip;

                d->step       = step;
                d->step_st    = d->ty->st;
                d->step_depth = LogicalDepth(d->ty);
                d->step_expr  = ExprAt(ty, jit_frame_ip(
                        (vN(d->ty->st->frames) > 0) ? vvL(d->ty->st->frames) : NULL,
                        ip
                ) - 1);
        }

        ResumeWorld();

        pthread_mutex_unlock(&D.lock);

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kbool(&body, "allThreadsContinued", true);
        jw_close(&body, '}');

        Respond(req, NULL, &body);
}

static void
ReqPause(Ty *ty, Json const *req, Json const *args)
{
        pthread_mutex_lock(&D.lock);

        if (!D.stopped) {
                D.stopped      = true;
                D.stopper      = NULL;
                D.reason       = REASON_PAUSE;
                D.pause_thread = JInt(args, "threadId", 1);

                v0(D.hits);

                DebugInterrupt   = 1;
                JitInterruptFlag = 1;

                PostEvent((DebugEvent) { .kind = EV_STOP });
        }

        pthread_mutex_unlock(&D.lock);

        Respond(req, NULL, NULL);
}

static void
ReqInitialize(Ty *ty, Json const *req, Json const *args)
{
        D.lines1 = JBool(args, "linesStartAt1", true);
        D.cols1  = JBool(args, "columnsStartAt1", true);

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kbool(&body, "supportsConfigurationDoneRequest", true);
        jw_kbool(&body, "supportsFunctionBreakpoints", true);
        jw_kbool(&body, "supportsConditionalBreakpoints", true);
        jw_kbool(&body, "supportsHitConditionalBreakpoints", true);
        jw_kbool(&body, "supportsLogPoints", true);
        jw_kbool(&body, "supportsEvaluateForHovers", true);
        jw_kbool(&body, "supportsSetVariable", true);
        jw_kbool(&body, "supportsExceptionInfoRequest", true);
        jw_kbool(&body, "supportsLoadedSourcesRequest", true);
        jw_kbool(&body, "supportsBreakpointLocationsRequest", true);
        jw_kbool(&body, "supportsSteppingGranularity", true);
        jw_kbool(&body, "supportsDelayedStackTraceLoading", true);
        jw_kbool(&body, "supportsTerminateRequest", true);
        jw_key(&body, "exceptionBreakpointFilters");
        jw_open(&body, '[');
        jw_open(&body, '{');
        jw_kstr(&body, "filter", "raised");
        jw_kstr(&body, "label", "Raised Exceptions");
        jw_kbool(&body, "default", false);
        jw_close(&body, '}');
        jw_open(&body, '{');
        jw_kstr(&body, "filter", "uncaught");
        jw_kstr(&body, "label", "Uncaught Exceptions");
        jw_kbool(&body, "default", true);
        jw_close(&body, '}');
        jw_close(&body, ']');
        jw_close(&body, '}');

        Respond(req, NULL, &body);

        SendEvent("initialized", NULL);
}

static void
ReqConfigurationDone(Ty *ty, Json const *req, Json const *args)
{
        pthread_mutex_lock(&D.lock);

        for (isize i = 0; i < vN(D.bps); ++i) {
                Breakpoint *bp = v__(D.bps, i);
                if (!bp->verified) {
                        Resolve(ty, bp);
                }
        }

        pthread_mutex_unlock(&D.lock);

        Respond(req, NULL, NULL);
}

static bool
HandleRequest(Ty *ty, Json const *req)
{
        char const *command = JStr(req, "command");
        Json const *args = JGet(req, "arguments");

        if (command == NULL) {
                return true;
        }

        if (strcmp(command, "initialize") == 0) {
                ReqInitialize(ty, req, args);
        } else if (strcmp(command, "attach") == 0) {
                Respond(req, NULL, NULL);
        } else if (strcmp(command, "launch") == 0) {
                Respond(req, "this debugger can only attach to running programs", NULL);
        } else if (strcmp(command, "setBreakpoints") == 0) {
                ReqSetBreakpoints(ty, req, args);
        } else if (strcmp(command, "setFunctionBreakpoints") == 0) {
                ReqSetFunctionBreakpoints(ty, req, args);
        } else if (strcmp(command, "setExceptionBreakpoints") == 0) {
                ReqSetExceptionBreakpoints(ty, req, args);
        } else if (strcmp(command, "breakpointLocations") == 0) {
                ReqBreakpointLocations(ty, req, args);
        } else if (strcmp(command, "configurationDone") == 0) {
                ReqConfigurationDone(ty, req, args);
        } else if (strcmp(command, "threads") == 0) {
                ReqThreads(ty, req, args);
        } else if (strcmp(command, "stackTrace") == 0) {
                ReqStackTrace(ty, req, args);
        } else if (strcmp(command, "scopes") == 0) {
                ReqScopes(ty, req, args);
        } else if (strcmp(command, "variables") == 0) {
                ReqVariables(ty, req, args);
        } else if (strcmp(command, "evaluate") == 0) {
                ReqEvaluate(ty, req, args);
        } else if (strcmp(command, "setVariable") == 0) {
                ReqSetVariable(ty, req, args);
        } else if (strcmp(command, "exceptionInfo") == 0) {
                ReqExceptionInfo(ty, req, args);
        } else if (strcmp(command, "source") == 0) {
                ReqSource(ty, req, args);
        } else if (strcmp(command, "loadedSources") == 0) {
                ReqLoadedSources(ty, req, args);
        } else if (strcmp(command, "continue") == 0) {
                ReqResume(ty, req, args, STEP_NONE);
        } else if (strcmp(command, "next") == 0) {
                ReqResume(ty, req, args, STEP_OVER);
        } else if (strcmp(command, "stepIn") == 0) {
                ReqResume(ty, req, args, STEP_IN);
        } else if (strcmp(command, "stepOut") == 0) {
                ReqResume(ty, req, args, STEP_OUT);
        } else if (strcmp(command, "pause") == 0) {
                ReqPause(ty, req, args);
        } else if (strcmp(command, "disconnect") == 0 || strcmp(command, "terminate") == 0) {
                bool kill = JBool(args, "terminateDebuggee", strcmp(command, "terminate") == 0);
                Detach(ty);
                Respond(req, NULL, NULL);
                if (kill) {
                        raise(SIGTERM);
                }
                return false;
        } else {
                Respond(req, "unsupported request", NULL);
        }

        return true;
}

static void
SendStopped(Ty *ty, u64 gen)
{
        AgentUnlock(ty);

        pthread_mutex_lock(&D.lock);

        if (!D.stopped || D.gen != gen) {
                pthread_mutex_unlock(&D.lock);
                AgentLock(ty);
                return;
        }

        WaitQuiet();

        u64 thread = (D.stopper != NULL) ? D.stopper->id : D.pause_thread;

        if (ThreadById(thread) == NULL) {
                for (isize i = 0; i < vN(D.threads); ++i) {
                        if (!v__(D.threads, i)->agent) {
                                thread = v__(D.threads, i)->id;
                                break;
                        }
                }
        }

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kstr(&body, "reason", ReasonNames[D.reason]);
        jw_kint(&body, "threadId", thread);
        jw_kbool(&body, "allThreadsStopped", true);
        jw_kbool(&body, "preserveFocusHint", false);

        if (D.text != NULL) {
                jw_kstr(&body, "text", D.text);
                jw_kstr(&body, "description", D.exc_type);
        }

        if (vN(D.hits) > 0) {
                jw_key(&body, "hitBreakpointIds");
                jw_open(&body, '[');
                for (isize i = 0; i < vN(D.hits); ++i) {
                        jw_int(&body, v__(D.hits, i));
                }
                jw_close(&body, ']');
        }

        jw_close(&body, '}');

        pthread_mutex_unlock(&D.lock);

        AgentLock(ty);

        SendEvent("stopped", &body);
}

static void
DrainEvents(Ty *ty)
{
        char buf[256];

        while (read(D.wake[0], buf, sizeof buf) > 0) {
                continue;
        }

        pthread_mutex_lock(&D.lock);
        DebugEvent *events = vv(D.events);
        isize n = vN(D.events);
        v00(D.events);
        pthread_mutex_unlock(&D.lock);

        for (isize i = 0; i < n; ++i) {
                DebugEvent *ev = &events[i];
                JsonWriter body = {0};

                switch (ev->kind) {
                case EV_STOP:
                        SendStopped(ty, ev->gen);
                        break;

                case EV_OUTPUT:
                        jw_open(&body, '{');
                        jw_kstr(&body, "category", "console");
                        jw_kstr(&body, "output", ev->text);
                        jw_close(&body, '}');
                        SendEvent("output", &body);
                        break;

                case EV_THREAD_START:
                case EV_THREAD_EXIT:
                        jw_open(&body, '{');
                        jw_kstr(&body, "reason", (ev->kind == EV_THREAD_START) ? "started" : "exited");
                        jw_kint(&body, "threadId", ev->thread);
                        jw_close(&body, '}');
                        SendEvent("thread", &body);
                        break;

                case EV_BREAKPOINT:
                        pthread_mutex_lock(&D.lock);
                        for (isize j = 0; j < vN(D.bps); ++j) {
                                if (v__(D.bps, j)->id == ev->bp) {
                                        jw_open(&body, '{');
                                        jw_kstr(&body, "reason", "changed");
                                        jw_key(&body, "breakpoint");
                                        WriteBreakpoint(&body, v__(D.bps, j));
                                        jw_close(&body, '}');
                                }
                        }
                        pthread_mutex_unlock(&D.lock);
                        if (vN(body.b) > 0) {
                                SendEvent("breakpoint", &body);
                        }
                        break;
                }

                free(ev->text);
        }

        free(events);
}

static bool
ReadMessages(Ty *ty, byte_vector *buf)
{
        for (;;) {
                char *start = vv(*buf);
                char *end = (vN(*buf) > 0) ? memmem(start, vN(*buf), "\r\n\r\n", 4) : NULL;

                if (end == NULL) {
                        return true;
                }

                usize length = 0;
                char *header = memmem(start, end - start, "Content-Length:", 15);

                if (header == NULL) {
                        return false;
                }

                length = strtoul(header + 15, NULL, 10);

                usize total = (end - start) + 4 + length;

                if (vN(*buf) < total) {
                        return true;
                }

                Json *req = JsonParse(end + 4, length);
                bool keep = true;

                if (req != NULL) {
                        keep = HandleRequest(ty, req);
                        JsonFree(req);
                }

                memmove(vv(*buf), vv(*buf) + total, vN(*buf) - total);
                vN(*buf) -= total;

                if (!keep) {
                        return false;
                }
        }
}

static void
Session(Ty *ty, int fd)
{
        byte_vector buf = {0};

        for (;;) {
                struct pollfd fds[2] = {
                        { .fd = fd,        .events = POLLIN },
                        { .fd = D.wake[0], .events = POLLIN }
                };

                AgentUnlock(ty);
                int r = poll(fds, 2, -1);
                AgentLock(ty);

                if (r < 0 && errno == EINTR) {
                        continue;
                }

                if (r < 0) {
                        break;
                }

                if (fds[1].revents & POLLIN) {
                        DrainEvents(ty);
                }

                if (fds[0].revents & (POLLIN | POLLHUP | POLLERR)) {
                        char chunk[65536];
                        ssize_t n = read(fd, chunk, sizeof chunk);
                        if (n < 0 && errno == EINTR) {
                                continue;
                        }
                        if (n <= 0) {
                                break;
                        }
                        xvPn(buf, chunk, n);
                        if (!ReadMessages(ty, &buf)) {
                                break;
                        }
                }
        }

        xvF(buf);
}

static void
SocketPath(long pid, char *out, usize n)
{
        snprintf(out, n, "/tmp/.ty_dbg_%ld.sock", pid);
}

static void
AttachPath(long pid, char *out, usize n)
{
        snprintf(out, n, "/tmp/.ty_attach_%ld", pid);
}

static bool
PeerIsUs(int fd)
{
        uid_t uid;

#if defined(__APPLE__) || defined(__FreeBSD__)
        gid_t gid;
        if (getpeereid(fd, &uid, &gid) != 0) {
                return false;
        }
#else
        struct ucred cred;
        socklen_t len = sizeof cred;
        if (getsockopt(fd, SOL_SOCKET, SO_PEERCRED, &cred, &len) != 0) {
                return false;
        }
        uid = cred.uid;
#endif

        return (uid == geteuid()) || (uid == 0);
}

static int
Listen(char const *path)
{
        struct sockaddr_un addr = { .sun_family = AF_UNIX };
        int fd = socket(AF_UNIX, SOCK_STREAM, 0);

        if (fd < 0) {
                return -1;
        }

        snprintf(addr.sun_path, sizeof addr.sun_path, "%s", path);
        unlink(path);

        if (
                (bind(fd, (struct sockaddr *)&addr, sizeof addr) != 0)
             || (chmod(path, 0600) != 0)
             || (listen(fd, 1) != 0)
        ) {
                close(fd);
                unlink(path);
                return -1;
        }

        return fd;
}

static int
Accept(int server)
{
        struct pollfd pfd = { .fd = server, .events = POLLIN };

        for (;;) {
                int r = poll(&pfd, 1, 15000);
                if (r < 0 && errno == EINTR) {
                        continue;
                }
                if (r <= 0) {
                        return -1;
                }
                int fd = accept(server, NULL, NULL);
                if (fd < 0 && errno == EINTR) {
                        continue;
                }
                return fd;
        }
}

static void *
AgentMain(void *ctx)
{
        sigset_t all;
        sigfillset(&all);
        pthread_sigmask(SIG_BLOCK, &all, NULL);

#if defined(__APPLE__)
        pthread_setname_np("ty-debugger");
#else
        pthread_setname_np(pthread_self(), "ty-debugger");
#endif

        char path[128];
        SocketPath((long)getpid(), path, sizeof path);

        int server = Listen(path);
        int fd = (server >= 0) ? Accept(server) : -1;

        if (server >= 0) {
                close(server);
                unlink(path);
        }

        if (fd >= 0 && !PeerIsUs(fd)) {
                close(fd);
                fd = -1;
        }

        if (fd < 0) {
                pthread_mutex_lock(&D.lock);
                D.agent = false;
                pthread_mutex_unlock(&D.lock);
                return NULL;
        }

        AgentThread = true;

        Ty *ty = vm_new_debug_ty();

        pthread_mutex_lock(&SendLock);
        D.client = fd;
        pthread_mutex_unlock(&SendLock);

        pthread_mutex_lock(&D.lock);
        D.session        = true;
        D.lines1         = true;
        D.cols1          = true;
        DebugJitOff      = 1;
        JitInterruptFlag = 1;
        pthread_mutex_unlock(&D.lock);

        Session(ty, fd);

        Detach(ty);

        pthread_mutex_lock(&SendLock);
        D.client = -1;
        pthread_mutex_unlock(&SendLock);

        close(fd);

        pthread_mutex_lock(&D.lock);
        D.agent = false;
        pthread_mutex_unlock(&D.lock);

        vm_free_debug_ty(ty);

        return NULL;
}

static bool
AttachRequested(void)
{
        char path[128];
        struct stat st;

        AttachPath((long)getpid(), path, sizeof path);

        if (lstat(path, &st) != 0) {
                return false;
        }

        unlink(path);

        return S_ISREG(st.st_mode) && ((st.st_uid == geteuid()) || (st.st_uid == 0));
}

static void
StartAgent(void)
{
        pthread_mutex_lock(&D.lock);

        if (D.agent) {
                pthread_mutex_unlock(&D.lock);
                return;
        }

        D.agent = true;

        pthread_mutex_unlock(&D.lock);

        pthread_t t;
        pthread_attr_t attr;

        pthread_attr_init(&attr);
        pthread_attr_setstacksize(&attr, 16 << 20);
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

        if (pthread_create(&t, &attr, AgentMain, NULL) != 0) {
                pthread_mutex_lock(&D.lock);
                D.agent = false;
                pthread_mutex_unlock(&D.lock);
        }

        pthread_attr_destroy(&attr);
}

static void *
WatchMain(void *ctx)
{
        sigset_t all;
        sigfillset(&all);
        pthread_sigmask(SIG_BLOCK, &all, NULL);

        int fd = (int)(iptr)ctx;
        char buf[64];

        for (;;) {
                ssize_t n = read(fd, buf, sizeof buf);

                if (n < 0 && errno == EINTR) {
                        continue;
                }

                if (n <= 0) {
                        break;
                }

                if (AttachRequested()) {
                        StartAgent();
                } else if (D.urg == 2) {
                        vm_do_signal(SIGURG, NULL, NULL);
                }
        }

        return NULL;
}

static void
OnSigurg(int sig, siginfo_t *info, void *ctx)
{
        int saved = errno;
        char c = 1;

        (void)!write(WatchPipe[1], &c, 1);

        errno = saved;
}

static bool
MakePipe(int fds[2])
{
        if (pipe(fds) != 0) {
                return false;
        }

        for (int i = 0; i < 2; ++i) {
                fcntl(fds[i], F_SETFD, FD_CLOEXEC);
        }

        fcntl(fds[1], F_SETFL, O_NONBLOCK);

        return true;
}

static void
StartWatcher(void)
{
        if (!MakePipe(WatchPipe)) {
                return;
        }

        pthread_t t;
        pthread_attr_t attr;

        pthread_attr_init(&attr);
        pthread_attr_setstacksize(&attr, 64 << 10);
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);
        pthread_create(&t, &attr, WatchMain, (void *)(iptr)WatchPipe[0]);
        pthread_attr_destroy(&attr);
}

static void
AfterFork(void)
{
        pthread_mutex_init(&D.lock, NULL);
        pthread_cond_init(&D.cond, NULL);
        pthread_mutex_init(&LocLock, NULL);
        pthread_mutex_init(&CacheLock, NULL);
        pthread_mutex_init(&CompileLock, NULL);
        pthread_mutex_init(&SendLock, NULL);

        Ty *self = get_my_ty();

        for (isize i = 0; i < vN(D.threads); ++i) {
                if (v__(D.threads, i)->ty != self) {
                        v__(D.threads, i--) = vXx(D.threads);
                }
        }

        for (isize i = 0; i < vN(D.bps); ++i) {
                FreeBreakpoint(v__(D.bps, i));
        }

        v0(D.bps);

        if (self != NULL && self->dbg != NULL) {
                self->dbg->step = STEP_NONE;
                self->dbg->rearm = NULL;
                self->dbg->state = DBG_RUNNING;
        }

        D.session = false;
        D.agent = false;
        D.stopped = false;
        D.client = -1;
        D.exc_filters = 0;
        D.rearms = 0;
        DebugInterrupt = 0;
        DebugJitOff = 0;

        close(D.wake[0]);
        close(D.wake[1]);
        MakePipe(D.wake);
        fcntl(D.wake[0], F_SETFL, O_NONBLOCK);

        close(WatchPipe[0]);
        close(WatchPipe[1]);
        StartWatcher();
}

void
DebugInit(Ty *ty)
{
#if defined(TY_LS)
        return;
#endif

        char const *off = getenv("TY_NO_ATTACH");

        if (off != NULL && off[0] != '\0' && strcmp(off, "0") != 0) {
                return;
        }

        if (!MakePipe(D.wake)) {
                return;
        }

        fcntl(D.wake[0], F_SETFL, O_NONBLOCK);

        StartWatcher();

        struct sigaction act = {0};
        act.sa_sigaction = OnSigurg;
        act.sa_flags = SA_SIGINFO | SA_RESTART;
        sigemptyset(&act.sa_mask);

        if (sigaction(SIGURG, &act, NULL) != 0) {
                return;
        }

        D.urg = 0;

        pthread_atfork(NULL, NULL, AfterFork);
        atexit(DebugShutdown);
}

void
DebugShutdown(void)
{
        if (!D.session) {
                return;
        }

        JsonWriter body = {0};

        jw_open(&body, '{');
        jw_kint(&body, "exitCode", 0);
        jw_close(&body, '}');

        SendEvent("exited", &body);
        SendEvent("terminated", NULL);
}

bool
DebugHandlesSignal(int sig)
{
        return (sig == SIGURG) && (WatchPipe[1] >= 0);
}

void
DebugSetSignalDisposition(int sig, int disposition)
{
        D.urg = disposition;
}

int
DebugAttachClient(long pid, char *sock, usize n)
{
        char attach[128];
        struct stat st;

        if (kill((pid_t)pid, 0) != 0) {
                fprintf(stderr, "ty: cannot attach to process %ld: %s\n", pid, strerror(errno));
                return -1;
        }

        AttachPath(pid, attach, sizeof attach);
        SocketPath(pid, sock, n);

        int fd = open(attach, O_CREAT | O_WRONLY | O_NOFOLLOW, 0600);

        if (fd < 0) {
                fprintf(stderr, "ty: cannot create %s: %s\n", attach, strerror(errno));
                return -1;
        }

        close(fd);

        if (kill((pid_t)pid, SIGURG) != 0) {
                fprintf(stderr, "ty: cannot signal process %ld: %s\n", pid, strerror(errno));
                unlink(attach);
                return -1;
        }

        for (int i = 0; i < 200; ++i) {
                if (stat(sock, &st) == 0 && S_ISSOCK(st.st_mode)) {
                        unlink(attach);
                        return 0;
                }
                usleep(25000);
        }

        unlink(attach);

        fprintf(
                stderr,
                "ty: process %ld did not respond (is it a ty program? was it started with TY_NO_ATTACH?)\n",
                pid
        );

        return -1;
}

static int
Connect(char const *path)
{
        struct sockaddr_un addr = { .sun_family = AF_UNIX };
        int fd = socket(AF_UNIX, SOCK_STREAM, 0);

        snprintf(addr.sun_path, sizeof addr.sun_path, "%s", path);

        if (fd < 0 || connect(fd, (struct sockaddr *)&addr, sizeof addr) != 0) {
                if (fd >= 0) {
                        close(fd);
                }
                return -1;
        }

        return fd;
}

int
DebugProxy(char const *path)
{
        int fd = Connect(path);

        if (fd < 0) {
                fprintf(stderr, "ty: cannot connect to %s: %s\n", path, strerror(errno));
                return 1;
        }

        char buf[65536];

        for (;;) {
                struct pollfd fds[2] = {
                        { .fd = 0,  .events = POLLIN },
                        { .fd = fd, .events = POLLIN }
                };

                if (poll(fds, 2, -1) < 0) {
                        if (errno == EINTR) {
                                continue;
                        }
                        break;
                }

                for (int i = 0; i < 2; ++i) {
                        if (!(fds[i].revents & (POLLIN | POLLHUP | POLLERR))) {
                                continue;
                        }
                        ssize_t k = read(fds[i].fd, buf, sizeof buf);
                        if (k <= 0 || !WriteAll((i == 0) ? fd : 1, buf, k)) {
                                close(fd);
                                return 0;
                        }
                }
        }

        close(fd);

        return 0;
}

#else

volatile sig_atomic_t DebugInterrupt;
volatile sig_atomic_t DebugJitOff;

void DebugInit(Ty *ty) {}
void DebugShutdown(void) {}
void DebugThreadStart(Ty *ty, TyThread self) {}
void DebugThreadExit(Ty *ty) {}
void DebugSafepoint(Ty *ty) {}
void DebugReacquire(Ty *ty) {}
void DebugTrap(Ty *ty, char *ip) {}
void DebugRearm(Ty *ty) {}
u8 DebugOriginalOp(char const *ip) { return (u8)*ip; }
void DebugSanitizeCode(char const *src, char *dst, usize n) {}
void DebugOnThrow(Ty *ty) {}
void DebugCodeLoaded(Ty *ty) {}
void DebugMarkRoots(Ty *ty) {}
void DebugLockLocations(void) {}
void DebugUnlockLocations(void) {}
bool DebugCanDeopt(Ty *ty) { return false; }
Expr const *DebugEvalContext(Ty *ty) { return NULL; }
bool DebugHandlesSignal(int sig) { return false; }
void DebugSetSignalDisposition(int sig, int disposition) {}
int DebugAttachClient(long pid, char *sock, usize n) { return -1; }
int DebugProxy(char const *sock) { return 1; }

#endif

/* vim: set sts=8 sw=8 expandtab: */
