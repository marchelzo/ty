#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ty.h"
#include "compiler.h"
#include "lex.h"
#include "token.h"
#include "value.h"
#include "functions.h"
#include "json.h"
#include "itable.h"
#include "types.h"
#include "vm.h"

//#define LSLOG(fmt, ...) fprintf(stderr, fmt __VA_OPT__(,) __VA_ARGS__)
#define LSLOG(fmt, ...)

char *FreedArenaLo;
char *FreedArenaHi;

static Arena             BaselineArena;
static CompilerBaseline  LsBaseline;

static char             *LastSource;
static char             *LastFile;

TY xD;
Ty *ty;
Ty vvv;

int EnableLogging = 0;
u64 TypeCheckCounter = 0;
u64 TypeAllocCounter = 0;
u64 TypeCheckTime = 0;

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
bool CheckConstraints = true;
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

int
main(int argc, char *argv[])
{
        ty = &vvv;

        if (!vm_init(ty, 0, argv)) {
                exit(1);
        }

        LsBaseline = CompilerSaveBaseline(ty);
        BaselineArena = ty->arena;
        CompilerSnapshotArena(&BaselineArena, &LsBaseline.arena_snaps);

        NewArenaNoGC(ty, 1 << 22);

        ValueVector   items     = {0};
        byte_vector   OutBuffer = {0};
        ModuleVector  reload    = {0};
        Arena         arena     = {0};

        u64 reqs = 0;

        EnableLogging += 1;

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

                LOGX("%s", SHOW(&req, ABBREV));

                i32 what = tget_nn(&req, "what")->z;

                i32 line;
                i32 col;

                char const *file;
                char const *source;

                Symbol *sym;
                Module *mod;

                Value v;
                Value result = NIL;

                if (TY_CATCH_ERROR()) {
                        char *trace = FormatTrace(ty, NULL, NULL);
                        Value   exc = TY_CATCH();
                        dump(&ErrorBuffer, "%s\n\n%s", VSC(&exc), trace);
                        fputs(vv(ErrorBuffer), stderr);
                        result = vTn("error", vSsz(vv(ErrorBuffer)));
                        goto NextRequest;
                }

                file = TY_C_STR(*tget_nn(&req, "file"));
                mod  = GetModuleByPath(ty, file);

                switch (what) {
                case LS_COMPILE:
                        v = tget_or(&req, "source", NIL);
                        AllowErrors = tget_or(&req, "check", NIL).type == VALUE_NIL;

                        if (v.type == VALUE_NIL) {
                                goto EndRequest;
                        }

                        source = TY_0_C_STR(v);

                        if (
                                   (LastFile != NULL)
                                && (LastSource != NULL)
                                && s_eq(file, LastFile)
                                && s_eq(source, LastSource)
                                && (GetModuleByPath(ty, file) != NULL)
                        ) {
                                goto EndRequest;
                        }

                        if (ty->arena.base != BaselineArena.base) {
                                FreedArenaLo = (char *)(uintptr_t)-1;
                                FreedArenaHi = NULL;
                                for (Arena const *ap = &ty->arena; ap->base != NULL; ap = NextArena(ap)) {
                                        if (ap->base < FreedArenaLo) FreedArenaLo = ap->base;
                                        if (ap->end > FreedArenaHi) FreedArenaHi = ap->end;
                                }
                                FreeArena(&ty->arena);
                        }
                        ty->arena = BaselineArena;
                        CompilerRestoreArena(&LsBaseline.arena_snaps);
                        CompilerRestoreBaseline(ty, &LsBaseline);
                        vN(Globals) = LsBaseline.global_count;
                        LOGX("RESTORED: arena pages=%zu", vN(LsBaseline.arena_snaps));

                        NewArenaNoGC(ty, 1 << 22);

                        mod = compiler_compile_source(ty, source, file);

                        if (mod == NULL) {
                                LOGX("compilation failed: %s\n", TyError(ty));
                                result = vTn(
                                        "error", xSz(TyError(ty))
                                );
                                goto EndRequest;
                        } else {
                                LOGX("loaded module %s\n", mod->path);
                        }

                        xmF(LastSource);
                        xmF(LastFile);
                        LastSource = S2(source);
                        LastFile   = S2(file);
                        break;

                case LS_DEFINITION:
                        line = tget_nn(&req, "line")->z;
                        col  = tget_nn(&req, "col")->z;

                        if (mod == NULL) {
                                goto EndRequest;
                        }

                        sym = CompilerFindDefinition(ty, mod, line, col);
                        if (sym == NULL || IsUndefinedSymbol(sym)) {
                                goto EndRequest;
                        }

                        result = vTn(
                                "name",  xSz(sym->identifier),
                                "line",  INTEGER(sym->loc.line),
                                "col",   INTEGER(sym->loc.col),
                                "file",  xSz(sym->mod ? sym->mod->path : "<unknown>"),
                                "type",  xSz(type_show(ty, sym->type)),
                                "doc",   (sym->doc == NULL) ? NIL : xSz(sym->doc)
                        );
                        break;

                case LS_COMPLETION:
                        line = tget_nn(&req, "line")->z;
                        col  = tget_nn(&req, "col")->z;

                        if (mod == NULL) {
                                goto EndRequest;
                        }

                        v0(items);

                        if (!CompilerSuggestCompletions(ty, mod, line, col, &items)) {
                                goto EndRequest;
                        }

                        result = vTn(
                                "source",      xSs(QueryExpr->start.s, QueryExpr->end.s - QueryExpr->start.s),
                                "type",        xSz(type_show(ty, QueryExpr->_type)),
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
                        puts("{\"error\": \"json\"");
                        fflush(stdout);
                        LSLOG("err=%s\n", VSC(&result));
                }
        }
}
