#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "ty.h"
#include "compiler.h"
#include "lex.h"
#include "token.h"
#include "value.h"
#include "functions.h"
#include "json.h"
#include "itable.h"
#include "types2.h"
#include "vm.h"
#include "diag.h"

#ifdef __APPLE__
#include <mach/mach.h>
#endif

#if 0
  #define LSLOG(fmt, ...) fprintf(        \
        stderr,                           \
        "[tyls] " fmt "\n" __VA_OPT__(,)  \
        __VA_ARGS__                       \
  )
#else
  #define LSLOG(fmt, ...)
#endif

enum {
        ROLE_ROOT,
        ROLE_DEPS,
        ROLE_WORKER
};

enum {
        EXIT_STALE  = 75,
        EXIT_NODEPS = 76
};

typedef struct {
        char *path;
        i64   mtime;
        i64   size;
} DepStamp;

typedef struct {
        byte_vector buf;
        usize       off;
} LineReader;

typedef struct {
        pid_t      pid;
        int        to;
        int        from;
        LineReader rd;
} Kid;

static int               Role  = ROLE_ROOT;
static int               InFd  = 0;
static int               OutFd = 1;
static LineReader        In;
static byte_vector       Line;
static byte_vector       Rsp;
static byte_vector       OutBuffer;

static Kid               Child = { .pid = -1, .to = -1, .from = -1 };
static char             *ChildFile;
static StringVector      NoDepsFiles;

static int               BaseModules;
static char             *DepsFile;
static bool              DepsLoaded;
static bool              NoDeps;
static ConstStringVector PendingDeps;
static vec(DepStamp)     DepStamps;
static char             *LastSource;
static bool              LastOk;

static bool              Compiled;

TY xD;
Ty *ty;
Ty vvv;

int EnableLogging = 0;

usize TotalBytesAllocated = 0;

int  ColorMode = TY_COLOR_NEVER;
bool ColorStdout;
bool ColorStderr;
bool ColorOutput;

char const *COLOR_MODE_NAMES[] = {
        [TY_COLOR_AUTO]   = "auto",
        [TY_COLOR_ALWAYS] = "always",
        [TY_COLOR_NEVER]  = "never"
};

bool RunningTests = false;
bool CheckTypes = true;
bool DetailedExceptions = true;
bool CompileOnly = true;
bool AllowErrors = false;
bool NoJIT = true;
bool InteractiveSession = false;

enum {
        LS_COMPILE,
        LS_DEFINITION,
        LS_COMPLETION,
        LS_SEMANTIC_TOKENS
};

enum {
        SEM_KEYWORD,
        SEM_TYPE,
        SEM_FUNCTION,
        SEM_PROPERTY,
        SEM_VARIABLE,
        SEM_STRING,
        SEM_NUMBER,
        SEM_COMMENT,
        SEM_OPERATOR,
        SEM_REGEXP,
        SEM_NAMESPACE,
        SEM_MACRO,
        SEM_PARAMETER
};

static bool
is_type_name(char const *id)
{
        if (id == NULL || !isupper((unsigned char)id[0])) {
                return false;
        }

        for (char const *p = id + 1; *p != '\0'; ++p) {
                if (*p == '_') {
                        return false;
                }
        }

        return true;
}

static i32
classify_identifier(Token const *t, char const *source)
{
        switch (t->tag) {
        case TT_TYPE:     return SEM_TYPE;
        case TT_FUNC:     return SEM_FUNCTION;
        case TT_CALL:     return SEM_FUNCTION;
        case TT_FIELD:    return SEM_PROPERTY;
        case TT_MEMBER:   return SEM_PROPERTY;
        case TT_MACRO:    return SEM_MACRO;
        case TT_MODULE:   return SEM_NAMESPACE;
        case TT_PARAM:    return SEM_PARAMETER;
        case TT_KEYWORD:  return SEM_KEYWORD;
        case TT_OPERATOR: return SEM_OPERATOR;
        default:          break;
        }

        if (is_type_name(t->identifier))
                return SEM_TYPE;

        if (t->end.s != NULL && source != NULL) {
                char const *p = t->end.s;
                while (*p == ' ' || *p == '\t') {
                        ++p;
                }
                if (*p == '(') {
                        return SEM_FUNCTION;
                }
        }

        return -1;
}

static void
EncodeTokens(Ty *ty, ValueVector *out, TokenVector const *tokens, char const *source)
{
        i32 prev_line = 0;
        i32 prev_col  = 0;

        for (isize i = 0; i < vN(*tokens); ++i) {
                Token const *t = v_(*tokens, i);

                if (t->ctx == LEX_FAKE)
                        continue;
                if (t->type == TOKEN_END)
                        break;
                if (t->type != TOKEN_IDENTIFIER)
                        continue;
                if (t->tag == TT_NONE)
                        continue;

                i32 sem = classify_identifier(t, source);
                if (sem < 0)
                        continue;

                i32 tline = (i32)t->start.line;
                i32 tcol  = (i32)t->start.col;
                i32 len   = (i32)(t->end.byte - t->start.byte);

                if (len <= 0)
                        continue;

                i32 delta_line = tline - prev_line;
                i32 delta_col  = (delta_line == 0) ? (tcol - prev_col) : tcol;

                xvP(*out, INTEGER(delta_line));
                xvP(*out, INTEGER(delta_col));
                xvP(*out, INTEGER(len));
                xvP(*out, INTEGER(sem));
                xvP(*out, INTEGER(0));

                prev_line = tline;
                prev_col  = tcol;
        }
}

static void
AppendDiagnostics(Ty *ty, Array *out)
{
        for (usize i = 0; i < vN(ty->diags); ++i) {
                Value records = TyErrorRecords(ty, v_(ty->diags, i));
                for (usize j = 0; j < vN(*records.array); ++j) {
                        vAp(out, v__(*records.array, j));
                }
        }
}

static Value
ErrorResult(Ty *ty, Value const *exc)
{
        byte_vector buf = {0};

        Value records = TyErrorRecords(ty, exc);
        AppendDiagnostics(ty, records.array);

        json_dump(ty, v_(*records.array, 0), &buf);

        Value result = vTn(
                "error",       vSs(vv(buf), vN(buf)),
                "diagnostics", records
        );

        xvF(buf);

        return result;
}

static Value
BadRequest(Ty *ty, char const *why)
{
        return vTn("error", xSz(why));
}

static Value *
ReqField(Value const *req, char const *name, u32 type)
{
        if (req->type != VALUE_TUPLE) {
                return NULL;
        }

        return tget_t(req, (uptr)name, type);
}

static T2Type
HoverType(Symbol const *sym)
{
        T2Universe *u = t2_global_universe();

        if (
                (QueryCall == NULL)
             || (t2_type_kind(u, sym->type) != T2_TYPE_TYPE_VALUE)
        ) {
                return sym->type;
        }

        T2Type ctor = t2_type_value_constructor(u, sym->type);

        return (ctor == T2_TYPE_INVALID) ? sym->type : ctor;
}

static Value
ShowType(Ty *ty, T2Type type)
{
        T2Universe *u = t2_global_universe();

        if (t2_type_kind(u, type) != T2_TYPE_OVERLOAD) {
                return xSz(t2_show(ty, type));
        }

        Array *overloads = vA();

        for (usize i = 0; i < t2_type_arity(u, type); ++i) {
                vAp(overloads, xSz(t2_show(ty, t2_type_child(u, type, i))));
        }

        return ARRAY(overloads);
}

static DepStamp
StampFile(char const *path)
{
        struct stat st;

        if (stat(path, &st) != 0) {
                return (DepStamp) { .mtime = -1, .size = -1 };
        }

#ifdef __APPLE__
        struct timespec mtime = st.st_mtimespec;
#else
        struct timespec mtime = st.st_mtim;
#endif

        return (DepStamp) {
                .mtime = (i64)mtime.tv_sec * 1000000000 + mtime.tv_nsec,
                .size  = (i64)st.st_size
        };
}

static void
RecordDepStamps(char const *file)
{
        for (int i = 0; i < vN(DepStamps); ++i) {
                xmF(v_(DepStamps, i)->path);
        }
        v0(DepStamps);

        ModuleVector const *mods = TyActiveModules(ty);

        for (int i = BaseModules; i < vN(*mods); ++i) {
                Module const *m = v__(*mods, i);
                if (m->path == NULL || s_eq(m->path, file)) {
                        continue;
                }
                DepStamp stamp = StampFile(m->path);
                stamp.path = S2(m->path);
                xvP(DepStamps, stamp);
        }
}

static bool
DepsStale(void)
{
        for (int i = 0; i < vN(DepStamps); ++i) {
                DepStamp const *old = v_(DepStamps, i);
                DepStamp now = StampFile(old->path);
                if (now.mtime != old->mtime || now.size != old->size) {
                        return true;
                }
        }

        return false;
}

static Value
DiagnosticsResult(Ty *ty)
{
        if (vN(ty->diags) == 0) {
                return NIL;
        }

        Array *records = vA();
        AppendDiagnostics(ty, records);

        return vTn("diagnostics", ARRAY(records));
}

static int
ThreadCount(void)
{
#ifdef __APPLE__
        thread_act_array_t     threads;
        mach_msg_type_number_t n;

        if (task_threads(mach_task_self(), &threads, &n) != KERN_SUCCESS) {
                return -1;
        }

        for (mach_msg_type_number_t i = 0; i < n; ++i) {
                mach_port_deallocate(mach_task_self(), threads[i]);
        }

        vm_deallocate(
                mach_task_self(),
                (vm_address_t)threads,
                n * sizeof *threads
        );

        return (int)n;
#else
        DIR *d = opendir("/proc/self/task");
        if (d == NULL) {
                return -1;
        }

        int n = 0;
        struct dirent *e;

        while ((e = readdir(d)) != NULL) {
                if (e->d_name[0] != '.') {
                        n += 1;
                }
        }

        closedir(d);

        return n;
#endif
}

static char const *
SigName(int sig)
{
        switch (sig) {
        case SIGSEGV: return "SIGSEGV";
        case SIGBUS:  return "SIGBUS";
        case SIGABRT: return "SIGABRT";
        case SIGILL:  return "SIGILL";
        case SIGFPE:  return "SIGFPE";
        case SIGTRAP: return "SIGTRAP";
        case SIGKILL: return "SIGKILL";
        case SIGTERM: return "SIGTERM";
        default:      return "SIGNAL";
        }
}

static void
ReportDeath(char const *who, int status)
{
        if (WIFSIGNALED(status)) {
                fprintf(
                        stderr,
                        "tyls: %s died: %s (%d)\n",
                        who,
                        SigName(WTERMSIG(status)),
                        WTERMSIG(status)
                );
        } else if (WIFEXITED(status) && (WEXITSTATUS(status) != 0)) {
                fprintf(stderr, "tyls: %s exited with status %d\n", who, WEXITSTATUS(status));
        }

        fflush(stderr);
}

static noreturn void
Die(int status)
{
        fflush(stderr);
        _exit(status);
}

static bool
WriteAll(int fd, char const *s, usize n)
{
        while (n > 0) {
                isize w = write(fd, s, n);
                if (w < 0 && errno == EINTR) {
                        continue;
                }
                if (w <= 0) {
                        return false;
                }
                s += w;
                n -= w;
        }

        return true;
}

static bool
ReadLine(int fd, LineReader *r, byte_vector *line)
{
        for (;;) {
                char *start = vv(r->buf) + r->off;
                char *nl = (vN(r->buf) > r->off)
                         ? memchr(start, '\n', vN(r->buf) - r->off)
                         : NULL;

                if (nl != NULL) {
                        usize n = (nl - start) + 1;
                        v0(*line);
                        xvPn(*line, start, n);
                        r->off += n;
                        return true;
                }

                if (r->off > 0) {
                        memmove(vv(r->buf), start, vN(r->buf) - r->off);
                        vN(r->buf) -= r->off;
                        r->off = 0;
                }

                xvR(r->buf, vN(r->buf) + (1 << 16));

                isize n = read(fd, vv(r->buf) + vN(r->buf), vC(r->buf) - vN(r->buf));
                if (n < 0 && errno == EINTR) {
                        continue;
                }
                if (n <= 0) {
                        return false;
                }

                vN(r->buf) += n;
        }
}

static void
Respond(Ty *ty, Value const *result)
{
        v0(OutBuffer);

        if (json_dump(ty, result, &OutBuffer)) {
                xvP(OutBuffer, '\n');
                WriteAll(OutFd, vv(OutBuffer), vN(OutBuffer));
        } else {
                LSLOG("err=%s\n", VSC(result));
                WriteAll(OutFd, "{\"error\": \"json\"}\n", 18);
        }
}

static void
RespondNull(void)
{
        WriteAll(OutFd, "null\n", 5);
}

static Value
ParseLine(Ty *ty, char const *s, usize n)
{
        Value str = vSs(s, n);

        vmP(&str);
        Value v = builtin_json_parse_xD(ty, 1, NULL);
        vmX();

        return v;
}

static int
Reap(Kid *k)
{
        int status = 0;

        if (k->pid <= 0) {
                return 0;
        }

        close(k->to);
        close(k->from);

        kill(k->pid, SIGKILL);

        while ((waitpid(k->pid, &status, 0) < 0) && (errno == EINTR)) {
                continue;
        }

        k->pid    = -1;
        k->to     = -1;
        k->from   = -1;
        k->rd.off = 0;
        v0(k->rd.buf);

        return status;
}

static bool
Spawn(Kid *k, int role)
{
        int to[2];
        int from[2];

        if ((pipe(to) != 0) || (pipe(from) != 0)) {
                fprintf(stderr, "tyls: pipe(): %s\n", strerror(errno));
                Die(1);
        }

        fflush(stdout);
        fflush(stderr);

        pid_t pid = fork();

        if (pid < 0) {
                fprintf(stderr, "tyls: fork(): %s\n", strerror(errno));
                Die(1);
        }

        if (pid == 0) {
                close(to[1]);
                close(from[0]);

                if (Role == ROLE_ROOT) {
                        int null = open("/dev/null", O_RDONLY);
                        dup2(null, 0);
                        close(null);
                        dup2(2, 1);
                } else {
                        close(InFd);
                        close(OutFd);
                }

                InFd   = to[0];
                OutFd  = from[1];
                In     = (LineReader) {0};
                *k     = (Kid) { .pid = -1, .to = -1, .from = -1 };
                Role   = role;

                return true;
        }

        close(to[0]);
        close(from[1]);

        k->pid    = pid;
        k->to     = to[1];
        k->from   = from[0];
        k->rd.off = 0;
        v0(k->rd.buf);

        return false;
}

static bool
IsNoDeps(char const *file)
{
        for (int i = 0; i < vN(NoDepsFiles); ++i) {
                if (s_eq(v__(NoDepsFiles, i), file)) {
                        return true;
                }
        }

        return false;
}

static bool
StartDeps(char const *file)
{
        int n = ThreadCount();

        if (n != 1) {
                fprintf(stderr, "tyls: root process has %d threads; refusing to fork\n", n);
                Die(1);
        }

        if (Spawn(&Child, ROLE_DEPS)) {
                DepsFile   = S2(file);
                NoDeps     = IsNoDeps(file);
                DepsLoaded = false;
                LastSource = NULL;
                LastOk     = false;
                v0(PendingDeps);
                v0(DepStamps);
                return true;
        }

        xmF(ChildFile);
        ChildFile = S2(file);

        return false;
}

static bool
IsCompile(Value *req, Value const *what)
{
        return (what->z == LS_COMPILE)
            && (tget_or(req, "source", NIL).type != VALUE_NIL);
}

static void
RouteRoot(Ty *ty, Value *req)
{
        Value *what = ReqField(req, "what", VALUE_INTEGER);
        Value *file = ReqField(req, "file", VALUE_STRING);

        if (what == NULL || file == NULL) {
                Value err = BadRequest(
                        ty,
                        "request must be an object with an integer `what` and a string `file`"
                );
                Respond(ty, &err);
                return;
        }

        char *path = S2(TY_C_STR(*file));
        bool compile = IsCompile(req, what);

        for (int attempt = 0; attempt < 2; ++attempt) {
                if (
                        compile
                     && (Child.pid > 0)
                     && !s_eq(ChildFile, path)
                ) {
                        Reap(&Child);
                }

                if (compile && (Child.pid <= 0) && StartDeps(path)) {
                        xmF(path);
                        return;
                }

                if (Child.pid <= 0) {
                        break;
                }

                if (
                        WriteAll(Child.to, vv(Line), vN(Line))
                     && ReadLine(Child.from, &Child.rd, &Rsp)
                ) {
                        WriteAll(OutFd, vv(Rsp), vN(Rsp));
                        xmF(path);
                        return;
                }

                int status = Reap(&Child);

                if (WIFEXITED(status) && (WEXITSTATUS(status) == EXIT_STALE)) {
                        continue;
                }

                ReportDeath("dependency process", status);

                if (!IsNoDeps(path)) {
                        fprintf(stderr, "tyls: no longer caching dependencies of %s\n", path);
                        fflush(stderr);
                        xvP(NoDepsFiles, S2(path));
                }

                if (!compile) {
                        break;
                }
        }

        xmF(path);
        RespondNull();
}

static void
TakeMeta(Ty *ty, byte_vector const *line)
{
        Value meta = ParseLine(ty, vv(*line) + 1, vN(*line) - 1);
        Value deps = tget_or(&meta, "deps", NIL);
        Value ok   = tget_or(&meta, "ok", NIL);

        LastOk = value_truthy(ty, &ok);

        if (deps.type != VALUE_ARRAY) {
                return;
        }

        v0(PendingDeps);

        for (int i = 0; i < vN(*deps.array); ++i) {
                Value const *dep = v_(*deps.array, i);
                if (dep->type == VALUE_STRING) {
                        xvP(PendingDeps, S2(TY_C_STR(*dep)));
                }
        }
}

static void
Forward(Ty *ty)
{
        if (Child.pid <= 0) {
                RespondNull();
                return;
        }

        if (!WriteAll(Child.to, vv(Line), vN(Line))) {
                goto Dead;
        }

        for (;;) {
                if (!ReadLine(Child.from, &Child.rd, &Rsp)) {
                        goto Dead;
                }
                if (vv(Rsp)[0] != '@') {
                        break;
                }
                TakeMeta(ty, &Rsp);
        }

        WriteAll(OutFd, vv(Rsp), vN(Rsp));

        return;

Dead:
        ReportDeath("worker", Reap(&Child));
        xmF(LastSource);
        LastSource = NULL;
        LastOk     = false;
        RespondNull();
}

static void
LoadDeps(Ty *ty)
{
        AllowErrors = true;

        if (TY_CATCH_ERROR()) {
                TY_CATCH_FAIL();
                fprintf(
                        stderr,
                        "tyls: failed to load dependencies of %s: %s\n",
                        DepsFile,
                        TyError(ty)
                );
                Die(EXIT_NODEPS);
        }

        for (int i = 0; i < vN(PendingDeps); ++i) {
                CompilerLoadModuleByPath(ty, v__(PendingDeps, i));
        }

        TY_CATCH_END();

        RecordDepStamps(DepsFile);
        DepsLoaded = true;
}

static void
RouteDeps(Ty *ty, Value *req)
{
        Value *what = ReqField(req, "what", VALUE_INTEGER);
        Value *file = ReqField(req, "file", VALUE_STRING);

        if (what == NULL || file == NULL || !IsCompile(req, what)) {
                Forward(ty);
                return;
        }

        if (DepsLoaded && DepsStale()) {
                Die(EXIT_STALE);
        }

        Value source = tget_or(req, "source", NIL);
        bool check = (tget_or(req, "check", NIL).type != VALUE_NIL);
        char const *src = TY_0_C_STR(source);

        if (
                (Child.pid > 0)
             && !check
             && LastOk
             && (LastSource != NULL)
             && s_eq(src, LastSource)
        ) {
                Forward(ty);
                return;
        }

        Reap(&Child);

        if (!DepsLoaded && !NoDeps && (vN(PendingDeps) > 0)) {
                LoadDeps(ty);
        }

        int n = ThreadCount();
        if (n != 1) {
                fprintf(
                        stderr,
                        "tyls: dependencies of %s left %d threads running\n",
                        DepsFile,
                        n
                );
                Die(EXIT_NODEPS);
        }

        xmF(LastSource);
        LastSource = S2(src);
        LastOk     = false;

        if (Spawn(&Child, ROLE_WORKER)) {
                Compiled = false;
                return;
        }

        Forward(ty);
}

static void
SendMeta(Ty *ty, Module const *mod)
{
        Array *deps = vA();

        if ((mod != NULL) && !DepsLoaded && !NoDeps) {
                for (int i = 0; i < vN(mod->imports); ++i) {
                        Module *dep = v__(mod->imports, i).mod;
                        if (dep != NULL && dep->path != NULL) {
                                vAp(deps, vSsz(dep->path));
                        }
                }
        }

        Value meta = vTn(
                "ok",   BOOLEAN(mod != NULL),
                "deps", ARRAY(deps)
        );

        v0(OutBuffer);
        xvP(OutBuffer, '@');

        if (json_dump(ty, &meta, &OutBuffer)) {
                xvP(OutBuffer, '\n');
                WriteAll(OutFd, vv(OutBuffer), vN(OutBuffer));
        }
}

static void
Serve(Ty *ty, Value req)
{
        static ValueVector items;

        Value *what_field = ReqField(&req, "what", VALUE_INTEGER);
        Value *file_field = ReqField(&req, "file", VALUE_STRING);

        Value *line_field;
        Value *col_field;

        i32 line;
        i32 col;

        char const *file;
        char const *source;

        Symbol *sym;
        Module *mod;

        Value v;
        Value result = NIL;

        if (what_field == NULL || file_field == NULL) {
                result = BadRequest(
                        ty,
                        "request must be an object with an integer `what` and a string `file`"
                );
                goto Done;
        }

        i32 what = what_field->z;

        if (TY_CATCH_ERROR()) {
                Value exc = TY_CATCH_FAIL();
                result = ErrorResult(ty, &exc);
                fprintf(stderr, "%s\n", TyError(ty));
                goto Done;
        }

        file = TY_C_STR(*file_field);
        mod  = GetModuleByPath(ty, file);

        switch (what) {
        case LS_COMPILE:
                v = tget_or(&req, "source", NIL);
                AllowErrors = (tget_or(&req, "check", NIL).type == VALUE_NIL);

                if (v.type == VALUE_NIL) {
                        goto EndRequest;
                }

                if (Compiled) {
                        result = DiagnosticsResult(ty);
                        goto EndRequest;
                }

                Compiled = true;
                source   = TY_0_C_STR(v);

                mod = TyCompileModule(ty, source, file, NULL, TYC_DEFAULT_FLAGS);

                SendMeta(ty, mod);

                if (mod == NULL) {
                        LSLOG("compilation failed: %s\n", TyError(ty));
                        result = ErrorResult(ty, &ty->error);
                        goto EndRequest;
                }

                LSLOG("loaded module %s\n", mod->path);
                result = DiagnosticsResult(ty);
                break;

        case LS_DEFINITION:
                line_field = ReqField(&req, "line", VALUE_INTEGER);
                col_field  = ReqField(&req, "col", VALUE_INTEGER);

                if (line_field == NULL || col_field == NULL) {
                        result = BadRequest(ty, "request requires integer `line` and `col`");
                        goto EndRequest;
                }

                line = line_field->z;
                col  = col_field->z;

                if (mod == NULL) {
                        goto EndRequest;
                }

                sym = CompilerFindDefinition(ty, mod, line, col);
                if (sym == NULL || IsUndefinedSymbol(sym)) {
                        goto EndRequest;
                }

                result = vTn(
                        "name",    xSz(sym->identifier),
                        "line",    INTEGER(sym->loc.line),
                        "col",     INTEGER(sym->loc.col),
                        "file",    xSz(sym->mod ? sym->mod->path : "<unknown>"),
                        "type",    ShowType(ty, HoverType(sym)),
                        "doc",     (sym->doc == NULL) ? NIL : xSz(sym->doc),
                        "builtin", BOOLEAN(SymbolIsBuiltin(sym))
                );
                break;

        case LS_COMPLETION:
                line_field = ReqField(&req, "line", VALUE_INTEGER);
                col_field  = ReqField(&req, "col", VALUE_INTEGER);

                if (line_field == NULL || col_field == NULL) {
                        result = BadRequest(ty, "request requires integer `line` and `col`");
                        goto EndRequest;
                }

                line = line_field->z;
                col  = col_field->z;

                if (mod == NULL) {
                        goto EndRequest;
                }

                v0(items);

                if (!CompilerSuggestCompletions(ty, mod, line, col, &items)) {
                        goto EndRequest;
                }

                result = vTn(
                        "source",      xSs(QueryExpr->start.s, QueryExpr->end.s - QueryExpr->start.s),
                        "type",        xSz(t2_show(ty, QueryExpr->_type)),
                        "completions", ARRAY((Array *)&items)
                );
                break;

        case LS_SEMANTIC_TOKENS:
                if (mod == NULL) {
                        goto EndRequest;
                }

                v0(items);
                EncodeTokens(ty, &items, &mod->tokens, mod->source);

                result = ARRAY((Array *)&items);
                break;
        }

EndRequest:
        TY_CATCH_END();

Done:
        Respond(ty, &result);
}

int
main(int argc, char *argv[])
{
        ty = &vvv;

        if (!vm_init(ty, 0, argv)) {
                exit(1);
        }

        signal(SIGPIPE, SIG_IGN);
        setpgid(0, 0);

        BaseModules = vN(*TyActiveModules(ty));

        NewArenaNoGC(ty, 1 << 22);

        TY_BEGIN_LOADING();

        for (;;) {
                if (!ReadLine(InFd, &In, &Line)) {
                        break;
                }

                GC_STOP();

                AllowErrors = true;

                Value req = ParseLine(ty, vv(Line), vN(Line));

                LSLOG("%s", SHOW(&req, ABBREV));

                switch (Role) {
                case ROLE_ROOT:   RouteRoot(ty, &req); break;
                case ROLE_DEPS:   RouteDeps(ty, &req); break;
                case ROLE_WORKER: Serve(ty, req);      break;
                }

                GC_RESUME();
        }

        Reap(&Child);

        if (Role != ROLE_ROOT) {
                Die(0);
        }

        signal(SIGTERM, SIG_IGN);
        kill(0, SIGTERM);

        return 0;
}
