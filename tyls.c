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
        if (id == NULL || !isupper((unsigned char)id[0]))
                return false;

        for (char const *p = id + 1; *p != '\0'; ++p)
                if (*p == '_')
                        return false;

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
                while (*p == ' ' || *p == '\t') ++p;
                if (*p == '(')
                        return SEM_FUNCTION;
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

        InternSet     names     = {0};
        struct itable files     = {0};
        ValueVector   items     = {0};
        byte_vector   OutBuffer = {0};

        for (;;) {
                xD.ready = false;
                AllowErrors = true;

                Value req = builtin_read(ty, 0, NULL);

                if (req.type == VALUE_NIL) {
                        return 0;
                }

                vmP(&req);
                req = builtin_json_parse_xD(ty, 1, NULL);
                vmX();

                fputs(VSC(&req), stderr);
                fputc('\n', stderr);

                i32 what = tget_nn(&req, "what")->z;

                i32 line;
                i32 col;

                char const *file;
                char const *source;

                i64 name;

                Symbol *sym;
                Module *mod;

                Value  v;
                Value *vp;

                Value result = NIL;

                if (TY_CATCH_ERROR()) {
                        char *trace = FormatTrace(ty, NULL, NULL);
                        Value   exc = TY_CATCH();
                        dump(&ErrorBuffer, "%s\n\n%s", VSC(&exc), trace);
                        fputs(vv(ErrorBuffer), stderr);
                        GC_STOP();
                        result = vTn("error", vSsz(vv(ErrorBuffer)));
                        GC_RESUME();
                        goto NextRequest;
                }

                file = TY_C_STR(*tget_nn(&req, "file"));
                name = intern(&names, file)->id;
                vp   = itable_get(ty, &files, name);

                mod = (vp->type == VALUE_PTR) ? vp->ptr : NULL;

                switch (what) {
                case LS_COMPILE:
                        v = tget_or(&req, "source", NIL);
                        AllowErrors = tget_or(&req, "check", NIL).type == VALUE_NIL;

                        if (v.type == VALUE_NIL) {
                                goto EndRequest;
                        }

                        source = TY_0_C_STR(v);

                        if (mod == NULL) {
                                mod = compiler_compile_source(ty, source, file);
                                if (mod != NULL) {
                                        *vp = PTR(mod);
                                } else {
                                        fputs(TyError(ty), stderr);
                                        result = vTn(
                                                "error", xSz(TyError(ty))
                                        );
                                }
                        } else {
                                if (!CompilerReloadModule(ty, mod, source)) {
                                        fputs(TyError(ty), stderr);
                                        result = vTn(
                                                "error", xSz(TyError(ty))
                                        );
                                        goto EndRequest;
                                }
                        }
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
                                "name",  xSz(QueryResult->identifier),
                                "line",  INTEGER(QueryResult->loc.line),
                                "col",   INTEGER(QueryResult->loc.col),
                                "file",  xSz(QueryResult->mod->path),
                                "type",  xSz(type_show(ty, QueryResult->type)),
                                "doc",   (QueryResult->doc == NULL) ? NIL : xSz(QueryResult->doc)
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
