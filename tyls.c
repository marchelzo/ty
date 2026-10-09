#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

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

#if 0
  #define LSLOG(fmt, ...) fprintf(        \
        stderr,                           \
        "[tyls] " fmt "\n" __VA_OPT__(,)  \
        __VA_ARGS__                       \
  )
#else
  #define LSLOG(fmt, ...)
#endif

char *FreedArenaLo;
char *FreedArenaHi;

static Arena             InitArena;
static CompilerBaseline  InitBaseline;

static Arena             DepsArena;
static CompilerBaseline  DepsBaseline;
static ArenaSnapshotVector DepsArenaSnaps;
static bool              HaveDeps;
static char             *DepsFile;

static ConstStringVector PendingDeps;

static char             *LastSource;
static char             *LastFile;

typedef struct {
        char *path;
        i64   mtime;
        i64   size;
} DepStamp;

static vec(DepStamp)     DepStamps;

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

        for (int i = InitBaseline.module_count; i < vN(*mods); ++i) {
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

static void
DropDeps(void)
{
        if (HaveDeps && (DepsArena.base != ty->arena.base)) {
                FreeArena(&DepsArena);
        }

        HaveDeps = false;
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

int
main(int argc, char *argv[])
{
        ty = &vvv;

        if (!vm_init(ty, 0, argv)) {
                exit(1);
        }

        InitBaseline = CompilerSaveBaseline(ty);
        InitArena = ty->arena;
        CompilerSnapshotArena(&InitArena, &InitBaseline.arena_snaps);

        NewArenaNoGC(ty, 1 << 22);

        ValueVector   items     = {0};
        byte_vector   OutBuffer = {0};

        TY_BEGIN_LOADING();

        for (;;) {
                GC_STOP();

                AllowErrors = true;

                Value req = builtin_read(ty, 0, NULL);

                if (req.type == VALUE_NIL) {
                        return 0;
                }

                vmP(&req);
                req = builtin_json_parse_xD(ty, 1, NULL);
                vmX();

                LSLOG("%s", SHOW(&req, ABBREV));

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
                        goto NextRequest;
                }

                i32 what = what_field->z;

                if (TY_CATCH_ERROR()) {
                        Value exc = TY_CATCH_FAIL();
                        result = ErrorResult(ty, &exc);
                        fprintf(stderr, "%s\n", TyError(ty));
                        goto NextRequest;
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

                        source = TY_0_C_STR(v);

                        bool stale = DepsStale();
                        if (stale) {
                                DropDeps();
                        }

                        if (
                                   !stale
                                && AllowErrors
                                && (LastFile != NULL)
                                && (LastSource != NULL)
                                && s_eq(file, LastFile)
                                && s_eq(source, LastSource)
                                && (GetModuleByPath(ty, file) != NULL)
                        ) {
                                result = DiagnosticsResult(ty);
                                goto EndRequest;
                        }

                        {
                                bool same = (DepsFile != NULL) && s_eq(file, DepsFile);

                                if (HaveDeps && same) {
                                        if (ty->arena.base != DepsArena.base) {
                                                FreeArena(&ty->arena);
                                        }
                                        ty->arena = InitArena;
                                        CompilerRestoreArena(&InitBaseline.arena_snaps);
                                        ty->arena = DepsArena;
                                        CompilerRestoreArena(&DepsArenaSnaps);
                                        CompilerRestoreBaseline(ty, &DepsBaseline);
                                        vN(Globals) = DepsBaseline.global_count;
                                } else {
                                        DropDeps();
                                        if (ty->arena.base != InitArena.base) {
                                                FreeArena(&ty->arena);
                                        }
                                        ty->arena = InitArena;
                                        CompilerRestoreArena(&InitBaseline.arena_snaps);
                                        CompilerRestoreBaseline(ty, &InitBaseline);
                                        vN(Globals) = InitBaseline.global_count;

                                        if (same && (vN(PendingDeps) > 0)) {
                                                NewArenaNoGC(ty, 1 << 22);

                                                for (int i = 0; i < vN(PendingDeps); ++i) {
                                                        CompilerLoadModuleByPath(ty, v__(PendingDeps, i));
                                                }

                                                DepsBaseline = CompilerSaveBaseline(ty);
                                                DepsArena = ty->arena;
                                                CompilerSnapshotArena(&DepsArena, &DepsArenaSnaps);
                                                HaveDeps = true;
                                        }
                                }
                        }

                        NewArenaNoGC(ty, 1 << 22);

                        mod = TyCompileModule(ty, source, file, NULL, TYC_DEFAULT_FLAGS);

                        if (mod == NULL) {
                                LSLOG("compilation failed: %s\n", TyError(ty));
                                result = ErrorResult(ty, &ty->error);
                                goto EndRequest;
                        } else {
                                LSLOG("loaded module %s\n", mod->path);
                                result = DiagnosticsResult(ty);
                        }

                        if (!HaveDeps && (mod != NULL)) {

                                for (int i = 0; i < vN(PendingDeps); ++i) {
                                        xmF((char *)v__(PendingDeps, i));
                                }
                                v0(PendingDeps);

                                for (int i = 0; i < vN(mod->imports); ++i) {
                                        Module *dep = v__(mod->imports, i).mod;
                                        if (dep != NULL && dep->path != NULL) {
                                                xvP(PendingDeps, S2(dep->path));
                                        }
                                }

                                if (vN(PendingDeps) > 0) {
                                        xmF(DepsFile);
                                        DepsFile = S2(file);
                                }
                        }

                        RecordDepStamps(file);

                        xmF(LastSource);
                        xmF(LastFile);
                        LastSource = S2(source);
                        LastFile   = S2(file);
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

NextRequest:
                GC_RESUME();
                v0(OutBuffer);

                if (json_dump(ty, &result, &OutBuffer)) {
                        xvP(OutBuffer, '\n');
                        xvP(OutBuffer, '\0');
                        fputs(vv(OutBuffer), stdout);
                        fflush(stdout);
                } else {
                        puts("{\"error\": \"json\"}");
                        fflush(stdout);
                        LSLOG("err=%s\n", VSC(&result));
                }
        }
}
