#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ty.h"
#include "compiler.h"
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

int EnableLogging = 0;
u64 TypeCheckCounter = 0;
u64 TypeAllocCounter = 0;
u64 TypeCheckTime = 0;

usize TotalBytesAllocated = 0;

bool ColorStdout;
bool ColorStderr;

bool CheckTypes = true;
bool CheckConstraints = true;
bool DetailedExceptions = true;
bool CompileOnly = true;
bool AllowErrors = false;
bool InteractiveSession = false;

int
main(int argc, char *argv[])
{
        Ty vvv;
        ty = &vvv;

        if (!vm_init(ty, 0, argv)) {
                exit(1);
        }

        InternSet     names       = {0};
        struct itable files       = {0};
        ValueVector   completions = {0};
        byte_vector   OutBuffer   = {0};

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
                        fputs(TyError(ty), stderr);
                        result = vTn(
                                "error", xSz(TyError(ty))
                        );
                        goto NextRequest;
                }

                file = TY_C_STR(*tget_nn(&req, "file"));
                name = intern(&names, file)->id;
                vp   = itable_get(ty, &files, name);

                mod = (vp->type == VALUE_PTR) ? vp->ptr : NULL;

                switch (what) {
                case 0:
                        v = tget_or(&req, "source", NIL);
                        AllowErrors = tget_or(&req, "check", NIL).type == VALUE_NIL;

                        if (v.type == VALUE_NIL) {
                                goto NextRequest;
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
                                        goto NextRequest;
                                }
                        }
                        break;

                case 1:
                        line = tget_nn(&req, "line")->z;
                        col  = tget_nn(&req, "col")->z;

                        if (mod == NULL) {
                                goto NextRequest;
                        }

                        sym = CompilerFindDefinition(ty, mod, line, col);
                        if (sym == NULL) {
                                goto NextRequest;
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

                case 2:
                        line = tget_nn(&req, "line")->z;
                        col  = tget_nn(&req, "col")->z;

                        if (mod == NULL) {
                                goto NextRequest;
                        }

                        v0(completions);

                        if (!CompilerSuggestCompletions(ty, mod, line, col, &completions)) {
                                goto NextRequest;
                        }

                        result = vTn(
                                "source",      xSs(QueryExpr->start.s, QueryExpr->end.s - QueryExpr->start.s),
                                "type",        xSz(type_show(ty, QueryExpr->_type)),
                                "completions", ARRAY((Array *)&completions)
                        );
                        break;
                }

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
