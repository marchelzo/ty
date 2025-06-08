#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdnoreturn.h>
#include <setjmp.h>
#include <errno.h>

#include "include/parse.h"
#include "polyfill_unistd.h"
#include <fcntl.h>

#include <readline/readline.h>
#include <readline/history.h>

#include "vm.h"
#include "gc.h"
#include "value.h"
#include "sqlite.h"
#include "util.h"
#include "itable.h"
#include "compiler.h"
#include "class.h"
#include "blob.h"
#include "str.h"
#include "json.h"
#include "dict.h"
#include "array.h"
#include "ty.h"
#include "types.h"
#include "polyfill_time.h"

#ifdef TY_HAVE_VERSION_INFO
#include "VersionInfo.h"
#endif

static Ty vvv;

Ty *ty;
TY xD;

#define MAX_COMPLETIONS 512

static int color_mode = TY_COLOR_AUTO;
static bool use_readline;
static bool basic = false;
static char buffer[8192];
static char *completions[MAX_COMPLETIONS + 1];
static char const *print_function = "print";
static char ToolQuery[512];

static char const *SourceFile;
static char const *SourceFileName;
static char SourceFilePath[PATH_MAX];

static bool KindOfEnableLogging = false;
int EnableLogging = 0;
u64 TypeCheckCounter = 0;
u64 TypeAllocCounter = 0;
u64 TypeCheckTime = 0;

bool ColorStdout;
bool ColorStderr;

bool CompileOnly = false;
bool AllowErrors = false;

extern bool ProduceAnnotation;
extern FILE *DisassemblyOut;

#ifdef TY_PROFILER
extern FILE *ProfileOut;
bool ColorProfile;
#endif

static char **
complete(char const *s, int start, int end);

static void
usage(void)
{
        char *u = (char[]) {
                "usage: ty [options] [script [args]]                                                      \0"
                "Available options are:                                                                   \0"
                "    -b            Basic mode: no batteries included. Only has an effect when ty is       \0"
                "                  running as a REPL or when the program was specified using -e           \0"
                "    -c            Exit after compilation without executing the program                   \0"
                "    -d            Run the program under the interactive TDB debugger                     \0"
                "    -e EXPR       Evaluate and print EXPR                                                \0"
                "    -f FILE       Interpret FILE before continuing. This differs from -M in that *all*   \0"
                "                  top-level symbols from FILE will be visible, not just public ones      \0"
                "    -m MODULE     Import module MODULE before continuing                                 \0"
                "    -M MODULE     Like -m, but uses an unqualified import: import MODULE (..)            \0"
                "    -p            Print the value of the last-evaluated expression before exiting        \0"
                "    -q            Ignore constraints on function parameters and return values            \0"
                "    -S FILE       Write the program's annotated disassembly to FILE                      \0"
                "                    (- is interpreted as stdout, and @ is interpreted as stderr)         \0"
                "    -t LINE:COL   Find the definition of the symbol which occurs at LINE:COL             \0"
                "                  in the specified source file                                           \0"
#ifdef TY_PROFILER
                "    -o FILE       Write profile data to FILE instead of stdout                           \0"
                "                    (- is interpreted as stdout, and @ is interpreted as stderr)         \0"
                "    --wall        Profile based on wall time instead of CPU time                         \0"
#endif
                "    --color=WHEN  Explicitly control when to use colored output. WHEN can be set         \0"
                "                  to 'always', 'never', or 'auto' (default: 'auto')                      \0"
                "    --            Stop handling options                                                  \0"
                "    --version     Print ty version information and exit                                  \0"
                "    --help        Print this help message and exit                                       \0"
        };

        do do putchar(*u++); while (u[u[-1] = strspn(u, " ")]); while (putchar('\n'), 1[u += u[-1]] && ++u);
}

static char *
readln(void)
{
        char prompt[64];

        snprintf(prompt, sizeof prompt, ">> ");

        if (use_readline) {
                return readline(prompt);
        } else {
                return fgets(buffer, sizeof buffer, stdin);
        }
}

inline static bool
repl_exec(Ty *ty, char const *code)
{
        return vm_execute(ty, code, "(repl)");
}

static bool
execln(Ty *ty, char *line)
{
        byte_vector buffer = {0};
        bool good = true;

        if (line[strspn(line, " \t\n")] == '\0')
                return true;

        xvP(buffer, '\0');

        /*
         * Very bad.
         */
        if (use_readline) {
                line = realloc(line, strlen(line) + 2);
                add_history(line);
        }

        if (strncmp(line, ":!", 2) == 0) {
                (void)system(line + 2);
                goto End;
        } else if (strncmp(line, ":s ", 3) == 0) {
                dump(&buffer, "%s", line + 3);
                if (vm_execute_file(ty, v_(buffer, 1))) {
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (strncmp(line, ":r ", 3) == 0) {
                if (TyReloadModule(ty, line + 3)) {
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (strncmp(line, "help ", 5) == 0) {
                dump(&buffer, "help(%s);", line + 5);
                if (repl_exec(ty, v_(buffer, 1)))
                        goto End;
                else
                        goto Bad;
        } else if (strncmp(line, "tdb ", 4) == 0) {
                dump(&buffer, "%s", line + 4);

                if (!vm_load_program(ty, v_(buffer, 1), "(repl)")) {
                        goto Bad;
                }

                if (!DEBUGGING) tdb_start(ty);
                tdb_set_break(ty, ty->code);

                if (!vm_execute(ty, NULL, NULL)) {
                        goto Bad;
                }

                goto End;
        } else if (strncmp(line, ":t ", 3) == 0) {
                dump(&buffer, "%s", line + 3);
                Stmt **prog = parse(ty, v_(buffer, 1), "(repl)");
                if (prog == NULL || prog[0] == NULL) {
                        goto Bad;
                }
                Expr expr = { .type = EXPRESSION_STATEMENT, .statement = prog[0] };
                if (compiler_symbolize_expression(ty, &expr, NULL)) {
                        printf("%s\n", type_show(ty, prog[0]->_type));
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (strncmp(line, "b ", 2) == 0) {
                dump(&buffer, "%s", line + 2);

                if (!repl_exec(ty, v_(buffer, 1))) {
                        goto Bad;
                }

                Value *v = vm_get(ty, -1);

                if (v->type != VALUE_FUNCTION) {
                        printf(
                                "Can't break on %s!",
                                VSC(v)
                        );
                        goto End;
                }

                if (!DEBUGGING) tdb_start(ty);
                tdb_set_break(ty, code_of(v));

                puts("Breakpoint set.");

                goto End;
        } else if (strncmp(line, "dis ", 4) == 0) {
                dump(&buffer, "print(ty.disassemble(%s));", line + 4);
                if (repl_exec(ty, v_(buffer, 1)))
                        goto End;
                else
                        goto Bad;
        }

        dump(&buffer, "%s(do (%s));", print_function, line);
        if (repl_exec(ty, v_(buffer, 1)))
                goto End;

        buffer.count = 1;

        dump(&buffer, "%s\n", line);
        if (strstr(TyError(ty), "ParseError") != NULL && repl_exec(ty, v_(buffer, 1)))
                goto End;

Bad:
        good = false;
        fprintf(stderr, "%s\n", TyError(ty));

End:
        fflush(stdout);

        return good;
}


static void
pollute_with_bloat(void)
{
        execln(
                ty,
                "import help (..)          \n"
                "import json               \n"
                "import base64             \n"
                "import math (..)          \n"
                "import ty                 \n"
                "import ty.types as types  \n"
                "import os (..)            \n"
                "import time (..)          \n"
                "import errno              \n"
                "import locale             \n"
                "import io                 \n"
                "import sh (sh)            \n"
        );

        print_function = "prettyPrint";
}


noreturn static void
repl(Ty *ty);

static jmp_buf InterruptJB;

static void
sigint(int signal)
{
        puts("Interrupted.");
        longjmp(InterruptJB, 1);
}

#if defined(TY_PROFILE_TYPES)
static void
xxx(void)
{
        void
        DumpTypeTimingInfo(Ty *ty);

        DumpTypeTimingInfo(ty);

        printf("Allocated %"PRIu64" type objects.\n", TypeAllocCounter);
        printf("Total type checking time: %.4fs\n", TypeCheckTime / 1.0e9);
}
#endif

noreturn static void
repl(Ty *ty)
{
        rl_attempted_completion_function = complete;
        rl_basic_word_break_characters = ".\t\n\r ";

        signal(SIGINT, sigint);

        if (!basic) pollute_with_bloat();

        use_readline = true;

        for (;;) {
                (void)setjmp(InterruptJB);
                for (;;) {
                        char *line = readln();
                        if (line == NULL) {
                                exit(EXIT_SUCCESS);
                        }
                        execln(ty, line);
                        type_reset_names(ty);
                }
        }
}

char *
completion_generator(char const *text, int state)
{
        return completions[state] ? S2(completions[state]) : NULL;
}

static int
AddCompletions(Ty *ty, Value const *v, char const *s)
{
        int n = 0;

        switch (v->type) {
        case VALUE_NAMESPACE:
                n += compiler_get_namespace_completions(ty, v->namespace, s, completions, MAX_COMPLETIONS);
                break;
        case VALUE_CLASS:
                n += class_get_completions(ty, v->class, s, completions, MAX_COMPLETIONS);
                break;
        case VALUE_OBJECT:
                n += class_get_completions(ty, v->class, s, completions, MAX_COMPLETIONS);
                n += itable_get_completions(ty, v->object, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_ARRAY:
                n += array_get_completions(ty, s, completions, MAX_COMPLETIONS);
                n += class_get_completions(ty, CLASS_ARRAY, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_DICT:
                n += dict_get_completions(ty, s, completions, MAX_COMPLETIONS);
                n += class_get_completions(ty, CLASS_DICT, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_STRING:
                n += string_get_completions(ty, s, completions, MAX_COMPLETIONS);
                n += class_get_completions(ty, CLASS_STRING, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_BLOB:
                n += blob_get_completions(ty, s, completions, MAX_COMPLETIONS);
                n += class_get_completions(ty, CLASS_BLOB, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_INTEGER:
                n += class_get_completions(ty, CLASS_INT, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_REAL:
                n += class_get_completions(ty, CLASS_FLOAT, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_GENERATOR:
                n += class_get_completions(ty, CLASS_ITERABLE, s, completions + n, MAX_COMPLETIONS - n);
                break;
        case VALUE_TUPLE:
                n += tuple_get_completions(ty, v, s, completions, MAX_COMPLETIONS);
                break;
        }

        return n;
}

static char **
complete(char const *s, int start, int end)
{
        rl_completion_append_character = '\0';

        if (start == 0 || rl_line_buffer[start - 1] != '.') {
                int n = compiler_get_completions(ty, NULL, s, completions, 99);
                if (n == 0) {
                        return NULL;
                } else {
                        completions[n] = NULL;
                        return rl_completion_matches(s, completion_generator);
                }
        }

        int before_len = start - 1;
        char before[2048] = {0};

        if (before_len + 2 > sizeof before) {
                return NULL;
        }

        memcpy(before + 1, rl_line_buffer, before_len);
        before[1 + before_len] = 0;

        int n = 0;

        Expr *expr;
        Type *t0;
        Value v;
        struct itable o = {0};

        /*
         * First check if it's a module name, otherwise treat it as an expression that
         * will evaluate to an object and then complete its members.
         */
        if (compiler_has_module(ty, before + 1)) {
                n = compiler_get_completions(ty, before + 1, s, completions, MAX_COMPLETIONS);
        } else if (repl_exec(ty, before + 1)) {
                n = AddCompletions(ty, vm_get(ty, -1), s);
        } else if (strstr(TyError(ty), "ParseError") != NULL) {
                strcat(before + 1, " [");
                repl_exec(ty, before + 1);
                expr = LastParsedExpr;
                v = tyeval(ty, expr);
                if (v.type == VALUE_NONE) {
                        compiler_symbolize_expression(ty, expr, NULL);
                        t0 = expr->_type;
                        switch (t0 == NULL ? -1 : t0->type) {
                        case TYPE_OBJECT:
                                v = OBJECT(&o, t0->class->i);
                                break;
                        case TYPE_INTEGER:
                                v = INTEGER(t0->z);
                                break;
                        }
                }
                n = AddCompletions(ty, &v, s);
        }

        if (n == 0) {
                return NULL;
        } else {
                completions[n] = NULL;
                return rl_completion_matches(s, completion_generator);
        }
}

inline static bool
stdin_is_tty(void)
{
#ifdef _WIN32
        return _isatty(0);
#else
        return isatty(0);
#endif
}

static FILE *
OpenOutputFile(char const *path)
{
        if (path[0] == '\0' || strcmp(path, "-") == 0) {
                return stdout;
        }

        if (strcmp(path, "@") == 0) {
                return stderr;
        }

        FILE *file = fopen(path, "w+");

        if (file == NULL) {
                fprintf(
                        stderr,
                        "Failed to open %s for writing: %s",
                        path,
                        strerror(errno)
                );
                exit(EXIT_FAILURE);
        }

        return file;
}

static int
ProcessArgs(char *argv[], bool first)
{
        int argi = 1;
        while (argv[argi] != NULL && argv[argi][0] == '-') {
                if (strcmp(argv[argi], "--") == 0) {
                        argi += 1;
                        break;
                }

                if (strcmp(argv[argi], "--version") == 0) {
#ifdef TY_HAVE_VERSION_INFO
                        printf(
                                "%s version %s (%s)\n"
                                "Compiler: %s %s\n"
                                "Platform: %s-%s\n",
                                VersionInfo_ProjectName,
                                VersionInfo_ProjectVersion,
                                VersionInfo_GitCommitDate,
                                VersionInfo_CompilerId,
                                VersionInfo_CompilerVersion,
                                VersionInfo_Architecture,
                                VersionInfo_BuildType
                        );
#else
                        printf("ty version 0.1\n");
#endif
                        exit(0);
                }

                if (strcmp(argv[argi], "--help") == 0) {
                        usage();
                        exit(0);
                }

                char const prefix[] = "--color=";
                if (strncmp(argv[argi], prefix, countof(prefix) - 1) == 0) {
                        char const *when = strchr(argv[argi], '=') + 1;
                        if      (strcmp(when, "always") == 0) { color_mode = TY_COLOR_ALWAYS; }
                        else if (strcmp(when, "never")  == 0) { color_mode = TY_COLOR_NEVER;  }
                        else if (strcmp(when, "auto")   == 0) { color_mode = TY_COLOR_AUTO;   }
                        else                                  { goto BadOption;               }
                        goto NextOption;
                }

#ifdef TY_PROFILER
                extern bool UseWallTime;
                if (strcmp(argv[argi], "--wall") == 0) {
                        UseWallTime = true;
                } else
#endif

                if (argv[argi][1] != '-') {
                        if (argv[argi][1] == ':') {
                                break;
                        }
                        for (char const *opt = argv[argi] + 1; *opt != '\0'; ++opt) {
                                switch (*opt) {
                                case 'q':
                                        CheckConstraints = false;
                                        break;
                                case 'b':
                                        basic = true;
                                        break;
                                case 'c':
                                        CompileOnly = true;
                                        break;
                                case 'd':
                                        if (!first) tdb_start(ty);
                                        break;
                                case 'L':
                                        EnableLogging |= KindOfEnableLogging;
                                        KindOfEnableLogging = true;
                                        break;
                                case 'p':
                                        PrintResult |= !first;
                                        break;
                                case 't':
                                        ColorStdout = false;
                                        ColorStderr = false;
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -t\n");
                                                        exit(1);
                                                }
                                                snprintf(ToolQuery, sizeof ToolQuery - 1, "%s", argv[++argi]);
                                        } else {
                                                snprintf(ToolQuery, sizeof ToolQuery - 1, "%s", opt + 1);
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        break;
                                case 'e':
                                        if (!first && !basic) pollute_with_bloat();
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -e\n");
                                                        exit(1);
                                                }
                                                if ((++argi, !first)) exit((int)!execln(ty, argv[argi]));
                                        } else {
                                                if (!first) exit((int)!execln(ty, (char *)(opt + 1)));
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        break;
                                case 'f':
                                case 'm':
                                case 'M':
                                {
                                        char const *fmt = (*opt == 'M') ? "import %s (..)\n"
                                                        : (*opt == 'm') ? "import %s\n"
                                                        :                 ":s %s";

                                        char const *module;

                                        if (opt[1] != '\0') {
                                                module = opt + 1;
                                        } else if (argv[argi + 1] != NULL) {
                                                module = argv[++argi];
                                        } else {
                                                fprintf(stderr, "Missing argument for -%c\n", *opt);
                                                exit(1);
                                        }

                                        snprintf(buffer, sizeof buffer, fmt, module);

                                        if (!first && !execln(ty, buffer)) {
                                                exit(1);
                                        }

                                        goto NextOption;
                                }
#ifdef TY_PROFILER
                                case 'o':
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -o\n");
                                                        exit(1);
                                                }
                                                ProfileOut = OpenOutputFile(argv[++argi]);
                                        } else {
                                                ProfileOut = OpenOutputFile(opt + 1);
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        break;
#endif
                                case 'S':
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -S\n");
                                                        exit(1);
                                                }
                                                DisassemblyOut = OpenOutputFile(argv[++argi]);
                                        } else {
                                                DisassemblyOut = OpenOutputFile(opt + 1);
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        break;
                                default:
                                        fprintf(stderr, "ty: unrecognized option `-%c`\n", *opt);
                                        exit(1);
                                }
                        }
                } else {
BadOption:
                        fprintf(stderr, "ty: unrecognized option `%s`\n", argv[argi]);
                        exit(1);
                }
NextOption:
                argi += 1;
        }

        if (first) {
                SourceFile = argv[argi];
                if (SourceFile == NULL) {
                        SourceFile = "-";
                }
                if (SourceFile[0] == '-' && SourceFile[1] == ':') {
                        SourceFileName = realpath(&SourceFile[2], SourceFilePath);
                }
                if (SourceFile[0] == '-') {
                        SourceFile = "/dev/stdin";
                }
                if (SourceFileName == NULL) {
                        SourceFileName = SourceFile;
                }
        }

        return argi;
}

enum {
        TOOL_COMPLETE    = 1,
        TOOL_SIGNATURE   = 2,
        TOOL_DEFINITION  = 4
};

static int
do_tool_opts(char *arg)
{
        int query = 0;

        while (*arg < '0' || *arg > '9') {
                switch (*arg++) {
                case  'd': query |= TOOL_DEFINITION; break;
                case  'c': query |= TOOL_COMPLETE;   break;
                case  's': query |= TOOL_SIGNATURE;  break;
                }
        }

        char *colon = strchr(arg, ':');
        if (colon == NULL) {
                return -1;
        }

        *colon = '\0';

        if (
                SourceFileName == NULL
             && realpath(SourceFile, SourceFilePath) == NULL
        ) {
                return -1;
        }

        SourceFileName = SourceFilePath;
        QueryFile = SourceFilePath;
        QueryLine = atoi(arg) - 1;
        QueryCol  = atoi(colon + 1) - 1;
        CompileOnly = true;
        AllowErrors = (query & TOOL_COMPLETE);

        return query;
}

int
main(int argc, char **argv)
{
        ty = &vvv;

#if defined(TY_PROFILE_TYPES) && 0
        atexit(xxx);
#endif

        int nopt = (argc == 0) ? 0 : ProcessArgs(argv, true);

        switch (color_mode) {
        case TY_COLOR_AUTO:   ColorStdout = isatty(1); ColorStderr = isatty(2); break;
        case TY_COLOR_ALWAYS: ColorStdout = true;      ColorStderr = true;      break;
        case TY_COLOR_NEVER:  ColorStdout = false;     ColorStderr = false;     break;
        }

        int query;
        if (*ToolQuery != '\0') {
                query = do_tool_opts(ToolQuery);
                if (query == -1) {
                        return -1;
                }
                if (query & TOOL_DEFINITION) {
                        FindDefinition = true;
                }
                if (query & TOOL_COMPLETE) {
                        SuggestCompletions = true;
                }
                if (query & TOOL_SIGNATURE) {
                        SuggestCompletions = true;
                }
        } else {
                query = 0;
        }

#ifdef TY_PROFILER
        if (ProfileOut == NULL) {
                ProfileOut = stdout;
        }

        switch (color_mode) {
        case TY_COLOR_AUTO:   ColorProfile = isatty(fileno(ProfileOut)); break;
        case TY_COLOR_ALWAYS: ColorProfile = true;                       break;
        case TY_COLOR_NEVER:  ColorProfile = false;                      break;
        }
#endif


        if (!vm_init(ty, argc - nopt, argv + nopt)) {
                fprintf(stderr, "%s\n", TyError(ty));
                return -1;
        }

        argv += ProcessArgs(argv, false);

        FILE *file = fopen(SourceFile, "r");
        if (file == NULL) {
                fprintf(stderr, "Failed to open source file '%s': %s\n", SourceFile, strerror(errno));
                return 1;
        }

        if (argv[0] == NULL && stdin_is_tty()) {
                repl(ty);
        }

        char *source = fslurp(ty, file);

        if (query & TOOL_DEFINITION) {
                bool ok = (QueryResult != NULL) || vm_execute(ty, source, SourceFileName);

                if (QueryResult == NULL || QueryResult->mod == NULL) {
                        return 2;
                }

                Value result = vTn(
                        "name",  xSz(QueryResult->identifier),
                        "line",  INTEGER(QueryResult->loc.line + 1),
                        "col",   INTEGER(QueryResult->loc.col + 1),
                        "file",  xSz(QueryResult->mod->path),
                        "type",  xSz(type_show(ty, QueryResult->type)),
                        "doc",   (QueryResult->doc == NULL) ? NIL : xSz(QueryResult->doc),
                        "error", ok ? NIL : xSz(TyError(ty))
                );

                byte_vector out = {0};

                if (!json_dump(ty, &result, &out)) {
                        return 3;
                }

                xvP(out, '\n');
                xvP(out, '\0');

                fputs(out.items, stdout);

                return 0;
        }

        if (query & TOOL_COMPLETE) {
                bool ok = (QueryExpr != NULL) || vm_execute(ty, source, SourceFileName);

                if (QueryExpr == NULL) {
                        if (!ok) {
                                fprintf(stderr, "%s\n", TyError(ty));
                                return 4;
                        } else {
                                return 2;
                        }
                }

                ValueVector completions = {0};

                type_completions(ty, QueryExpr->_type, "", &completions);

                Value result = vTn(
                        "source",      xSs(QueryExpr->start.s, QueryExpr->end.s - QueryExpr->start.s),
                        "type",        xSz(type_show(ty, QueryExpr->_type)),
                        "completions", ARRAY((Array *)&completions),
                        "error",       ok ? NIL : xSz(TyError(ty))
                );

                byte_vector out = {0};

                if (!json_dump(ty, &result, &out)) {
                        return 3;
                }

                xvP(out, '\n');
                xvP(out, '\0');

                fputs(out.items, stdout);

                return 0;
        }

        if (query & TOOL_SIGNATURE) {
                bool ok = (QueryExpr != NULL) || vm_execute(ty, source, SourceFileName);

                if (QueryExpr == NULL) {
                        if (!ok) {
                                fprintf(stderr, "%s\n", TyError(ty));
                                return 4;
                        } else {
                                return 2;
                        }
                }

                Expr *fun = NULL;
                Type *t0 = NULL;

                switch (QueryExpr->type) {
                case EXPRESSION_FUNCTION_CALL:
                        t0 = QueryExpr->function->_type;
                        if (QueryExpr->type == EXPRESSION_IDENTIFIER) {
                                fun = QueryExpr->symbol->expr;
                        }
                        break;
                case EXPRESSION_METHOD_CALL:
                        type_find_method(
                                ty,
                                QueryExpr->object->_type,
                                QueryExpr->method->identifier,
                                &t0,
                                &fun
                        );
                        break;
                }

                if (t0 == NULL || t0->type != TYPE_FUNCTION) {
                        return 6;
                }

                ValueVector params = {0};

                for (int i = 0; i < vN(t0->params); ++i) {
                        Param const *p = v_(t0->params, i);
                        xvP(
                                params,
                                vTn(
                                        "name",     (p->name != NULL) ? xSz(p->name) : NIL,
                                        "type",     type_show(ty, p->type),
                                        "required", BOOLEAN(p->required),
                                        "kwargs",   BOOLEAN(p->kws),
                                        "variadic", BOOLEAN(p->rest)
                                )
                        );
                }

                Value doc = (fun != NULL && fun->doc != NULL) ? xSz(fun->doc) : NIL;
                Value name = (fun != NULL && fun->name != NULL) ? xSz(fun->name) : NIL;
                Value proto = (fun != NULL && fun->name != NULL) ? xSz(fun->proto) : NIL;

                ValueVector sigs = {0};
                xvP(
                        sigs,
                        vTn(
                                "name",    name,
                                "proto",   proto,
                                "type",    xSz(type_show(ty, t0)),
                                "doc",     doc,
                                "params",  ARRAY((Array *)&completions)
                        )
                );

                Value result = vTn(
                        "signatures", ARRAY((Array *)&sigs),
                        "error",      ok ? NIL : xSz(TyError(ty))
                );

                byte_vector out = {0};

                if (!json_dump(ty, &result, &out)) {
                        return 3;
                }

                xvP(out, '\n');
                xvP(out, '\0');

                fputs(out.items, stdout);

                return 0;
        }

        if (!vm_execute(ty, source, SourceFileName)) {
                fprintf(stderr, "%s\n", TyError(ty));
                return -1;
        }

        return 0;
}

/* vim: set sts=8 sw=8 expandtab: */
