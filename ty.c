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

#include "vm.h"
#include "gc.h"
#include "value.h"
#include "sqlite.h"
#include "xd.h"
#include "itable.h"
#include "compiler.h"
#include "diag.h"
#include "types2.h"
#include "class.h"
#include "blob.h"
#include "str.h"
#include "json.h"
#include "dict.h"
#include "array.h"
#include "ty.h"
#include "highlight.h"
#include "polyfill_time.h"
#include "title.h"
#include "ty/debug.h"

Ty vvv;
TY xD;

static Ty *ty;

#define MAX_COMPLETIONS 512

static bool basic = false;
static char buffer[8192];

static char const *print_function = "print";

static char const *SourceFile;

static bool KindOfEnableLogging = false;
int EnableLogging = 0;

#if defined(TY_TRACE_GC)
_Thread_local u64 ThisReached;
_Thread_local u64 TotalReached;
#endif

#if defined(TY_GC_STATS)
usize TotalBytesAllocated;
#endif

char const *COLOR_MODE_NAMES[] = {
        [TY_COLOR_AUTO]   = "auto",
        [TY_COLOR_ALWAYS] = "always",
        [TY_COLOR_NEVER]  = "never"
};

int  ColorMode = TY_COLOR_AUTO;
bool ColorStdout;
bool ColorStderr;
bool ColorOutput;

bool RunningTests       = false;
bool CompileOnly        = false;
bool HighlightOnly      = false;
bool AllowErrors        = false;
bool CheckTypes         = true;
bool DetailedExceptions = false;
bool NoJIT              = false;
bool InteractiveSession = false;

static char const *HighlightTheme = NULL;

extern bool ProduceAnnotation;
extern FILE *DisassemblyOut;

#if defined(TY_PROFILER)
extern u64 ProfileSampleInterval;
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
                "    -e EXPR       Evaluate and print EXPR                                                \0"
                "    -f FILE       Interpret FILE before continuing. This differs from -M in that *all*   \0"
                "                  top-level symbols from FILE will be visible, not just public ones      \0"
                "    -j            Disable JIT                                                            \0"
                "    -m MODULE     Import module MODULE before continuing                                 \0"
                "    -M MODULE     Like -m, but uses an unqualified import: import MODULE (..)            \0"
                "    -p            Print the value of the last-evaluated expression before exiting        \0"
                "    -q            Ignore constraints on function parameters and return values            \0"
                "    -S FILE       Write the program's annotated disassembly to FILE                      \0"
                "                    (- is interpreted as stdout, and @ is interpreted as stderr)         \0"
                "    --test        Any top-level functions decorated with @test will be executed after    \0"
                "                  initialization. If all tests pass, ty will exit normally; otherwise, it\0"
                "                  will exit with a non-zero status code                                  \0"
#ifdef TY_PROFILER
                "    -F FREQ       Set profiler sampling frequency in Hz (default: every instruction)     \0"
                "    -o FILE       Write profile data to FILE instead of stdout                           \0"
                "                    (- is interpreted as stdout, and @ is interpreted as stderr)         \0"
                "    --wall        Profile based on wall time instead of CPU time                         \0"
#endif
                "    --color=WHEN  Explicitly control when to use colored output. WHEN can be set         \0"
                "                  to 'always', 'never', or 'auto' (default: 'auto')                      \0"
                "    --highlight[=THEME]                                                                  \0"
                "                  Print syntax-highlighted source and exit. Available themes:            \0"
                "                  gruvbox, gruvbox-material, github-light, github-dark, monokai,         \0"
                "                  one-dark, catppuccin, dracula, nord, solarized, tokyonight, rose-pine  \0"
                "    --            Stop handling options                                                  \0"
                "    --version     Print ty version information and exit                                  \0"
                "    --help        Print this help message and exit                                       \0"
        };

        do do putchar(*u++); while (u[u[-1] = strspn(u, " ")]); while (putchar('\n'), 1[u += u[-1]] && ++u);
}

static bool
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

        if (s_eq_n(line, ":!", 2)) {
                (void)system(line + 2);
                goto End;
        } else if (s_eq_n(line, ":s ", 3)) {
                dump(&buffer, "%s", line + 3);
                if (vm_execute_file(ty, v_(buffer, 1))) {
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (s_eq_n(line, ":r ", 3)) {
                if (TyReloadModule(ty, line + 3)) {
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (s_eq_n(line, "help ", 5)) {
                dump(&buffer, "help(%s);", line + 5);
                if (repl_exec(ty, v_(buffer, 1)))
                        goto End;
                else
                        goto Bad;
        } else if (s_eq_n(line, ":t ", 3)) {
                dump(&buffer, "%s", line + 3);
                Stmt **prog = parse(ty, v_(buffer, 1), "(repl)");
                if (prog == NULL || prog[0] == NULL) {
                        goto Bad;
                }
                Expr expr = { .type = EXPRESSION_STATEMENT, .statement = prog[0] };
                if (compiler_symbolize_expression(ty, &expr, NULL)) {
                        int rows;
                        int columns;
                        bool sized = get_terminal_size(1, &rows, &columns);
                        char *shown = t2_render(ty, t2_infer(ty, &expr), (T2Render) {
                                .color = ColorStdout,
                                .width = sized ? (unsigned)columns : 0
                        });
                        printf("%s\n", shown);
                        ty_free(shown);
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (s_eq(line, ":tt")) {
                CheckTypes = !CheckTypes;
                if (CheckTypes) {
                        puts("Types: \x1b[92;1mON\x1b[0m");
                } else {
                        puts("Types: \x1b[91;1mOFF\x1b[0m");
                }
                goto End;
#if defined(TY_RELEASE)
        } else if (s_eq_n(line, ":u ", 3)) {
                dump(&buffer, "(__type!((%s)))", line + 3);

                if (!repl_exec(ty, v_(buffer, 1))) {
                        goto Bad;
                }

                Expr *pair = TyToCExpr(ty, vm_get(ty, -1));

                T2Type t0 = t2_resolve(ty, v__(pair->es, 0));
                T2Type t1 = t2_resolve(ty, v__(pair->es, 1));

                bool related = (t0 == T2_TYPE_INVALID)
                            || (t1 == T2_TYPE_INVALID)
                            || (t2_subtype(t2_global_universe(), t0, t1) != T2_RELATION_NO);

                puts(related ? "true" : "false");

                goto End;
#endif
        } else if (s_eq_n(line, "dis ", 4)) {
                dump(&buffer, "print(ty.disassemble(%s));", line + 4);
                if (repl_exec(ty, v_(buffer, 1))) {
                        goto End;
                } else {
                        goto Bad;
                }
        }

        dump(&buffer, "%s(do (%s));", print_function, line);
        if (repl_exec(ty, v_(buffer, 1))) {
                goto End;
        }

        vN(buffer) = 1;
        dump(&buffer, "%s\n", line);

        if (
                (ClassOf(&ty->error) == CLASS_PARSE_ERROR)
             && repl_exec(ty, v_(buffer, 1))
        ) {
                goto End;
        }


Bad:
        good = false;
        fprintf(stderr, "%s\n", TyError(ty));

End:
        fflush(stdout);

        return good;
}

static char *
readln(Ty *ty)
{
        Value *_readln;

        if (!InteractiveSession) {
                return fgets(buffer, sizeof buffer, stdin);
        } else if (
                !basic
             && (_readln = vm_global(ty, NAMES._readln))
             && CALLABLE(*_readln)
        ) {
                if (TY_CATCH_ERROR()) {
                        char *trace = FormatTrace(ty, NULL, NULL);
                        Value exc = TY_CATCH();
                        char *msg = VSC(&exc);
                        fprintf(stderr, "\n%s\n%s\n", trace, msg);
                        xmF(trace);
                        xmF(msg);
                        return S2("");
                }

                Value line = vm_call(ty, _readln, 0);

                TY_CATCH_END();

                return (line.type != VALUE_NIL)
                     ? TyNewCString(ty, line, true)
                     : NULL;
        } else {
                fputs(">> ", stdout);
                fflush(stdout);
                return fgets(buffer, sizeof buffer, stdin);
        }
}

static void
pollute_with_bloat(void)
{
        execln(
                ty,
                "import pretty (..)           \n"
                "import json                  \n"
                "import base64                \n"
                "import math (..)             \n"
                "import ty                    \n"
                "import ty.types as types     \n"
                "import os (..)               \n"
                "import time (..)             \n"
                "import errno                 \n"
                "import locale                \n"
                "import ioctls                \n"
                "import termios (..)          \n"
                "import thread                \n"
                "import ptr                   \n"
                "import io                    \n"
                "import path (Path)           \n"
                "import readln                \n"
                "import sh (sh)               \n"
                "import date                  \n"
                "import chalk (chalk as C)    \n"
                "import help (..)             \n"
        );

        print_function = "pp";
}


static jmp_buf InterruptJB;

static void
sigint(int signal)
{
        fputs("Interrupted.\n", stderr);
        longjmp(InterruptJB, 1);
}


noreturn static void
repl(Ty *ty)
{
        InteractiveSession = true;
        v_(Globals, NAMES.interactive)->boolean = true;

        signal(SIGINT, sigint);

        if (!basic) {
                pollute_with_bloat();
                execln(ty, "import ty.repl\n");
#if defined(TY_HAVE_VERSION_INFO) && defined(TY_HAVE_GIT_STATUS)
                printf(
                        "ty %s (%s%.8s%s), built %s\n",
                        TY_VERSION_STRING,
                        VersionInfo_GitUncommittedChanges ? TERM(31) : "",
                        VersionInfo_GitCommitHash,
                        TERM(0),
                        TY_VERSION_DATE
                );
#endif
        }

        for (;;) {
                (void)setjmp(InterruptJB);
                for (;;) {
                        char *line = readln(ty);
                        if (line == NULL) {
                                exit(EXIT_SUCCESS);
                        }
                        execln(ty, line);
                }
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
        if (path[0] == '\0' || s_eq(path, "-")) {
                return stdout;
        }

        if (s_eq(path, "@")) {
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
                if (s_eq(argv[argi], "--")) {
                        argi += 1;
                        break;
                }

                if (s_eq(argv[argi], "--version")) {
#ifdef TY_HAVE_VERSION_INFO
                        printf(
                                "%s version %s (%s)\n"
                                "Compiler: %s %s\n"
                                "Platform: %s-%s\n",
                                VersionInfo_ProjectName,
                                VersionInfo_ProjectVersion,
#if defined(TY_HAVE_GIT_STATUS)
                                VersionInfo_GitCommitDate,
#else
                                TY_BUILD_DATE,
#endif
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

                if (s_eq(argv[argi], "--help")) {
                        usage();
                        exit(0);
                }

                if (s_eq(argv[argi], "--test")) {
                        RunningTests = true;
                        goto NextOption;
                }

                if (s_eq(argv[argi], "--highlight") || s_eq_n(argv[argi], "--highlight=", 12)) {
                        HighlightOnly = true;
                        CheckTypes = false;
                        char const *eq = strchr(argv[argi], '=');
                        if (eq != NULL && eq[1] != '\0') {
                                HighlightTheme = eq + 1;
                        }
                        goto NextOption;
                }

                char const prefix[] = "--color=";
                if (s_eq_n(argv[argi], prefix, countof(prefix) - 1)) {
                        char const *when = strchr(argv[argi], '=') + 1;
                        if      (s_eq(when, "always")) { ColorMode = TY_COLOR_ALWAYS; }
                        else if (s_eq(when, "never"))  { ColorMode = TY_COLOR_NEVER;  }
                        else if (s_eq(when, "auto"))   { ColorMode = TY_COLOR_AUTO;   }
                        else                           { goto BadOption;              }
                        goto NextOption;
                }

#ifdef TY_PROFILER
                extern bool UseWallTime;
                if (s_eq(argv[argi], "--wall")) {
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
                                        CheckTypes = false;
                                        DetailedExceptions = false;
                                        break;

                                case 'b':
                                        basic = true;
                                        break;

                                case 'c':
                                        CompileOnly = true;
                                        break;

                                case 'L':
                                        EnableLogging |= KindOfEnableLogging;
                                        KindOfEnableLogging = true;
                                        break;

                                case 'p':
                                        PrintResult |= !first;
                                        break;

                                case 'x':
                                        DetailedExceptions = true;
                                        break;

                                case 'j':
                                        NoJIT = true;
                                        break;

                                case 'e':
                                        ForgiveDuplicateImports = true;
                                        if (!first && !basic) pollute_with_bloat();
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -e\n");
                                                        exit(1);
                                                }
                                                if (++argi, !first) {
                                                        exit((int)!execln(ty, argv[argi]));
                                                }
                                        } else {
                                                if (!first) {
                                                        exit((int)!execln(ty, (char *)(opt + 1)));
                                                }
                                                while (opt[1] != '\0') {
                                                        ++opt;
                                                }
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

                                        ty_snprintf(buffer, sizeof buffer, fmt, module);

                                        if (!first && !execln(ty, buffer)) {
                                                exit(1);
                                        }

                                        goto NextOption;
                                }
#if defined(TY_PROFILER)
                                case 'F':
                                {
                                        char const *arg;
                                        if (opt[1] != '\0') {
                                                arg = opt + 1;
                                                while (opt[1] != '\0') {
                                                        ++opt;
                                                }
                                        } else if (argv[argi + 1] != NULL) {
                                                arg = argv[++argi];
                                        } else {
                                                fprintf(stderr, "Missing argument for -F\n");
                                                exit(1);
                                        }
                                        char *end;
                                        long freq = strtol(arg, &end, 10);
                                        if (*end != '\0' || freq < 0) {
                                                fprintf(stderr, "Invalid frequency for -F: %s\n", arg);
                                                exit(1);
                                        }
                                        if (freq > 0) {
                                                ProfileSampleInterval = 1000000000ULL / (u64)freq;
                                        }
                                        goto NextOption;
                                }

                                case 'o':
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -o\n");
                                                        exit(1);
                                                }
                                                ProfileOut = OpenOutputFile(argv[++argi]);
                                        } else {
                                                ProfileOut = OpenOutputFile(opt + 1);
                                                while (opt[1] != '\0') {
                                                        ++opt;
                                                }
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
                                                while (opt[1] != '\0') {
                                                        ++opt;
                                                }
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
                if (SourceFile == NULL || s_eq(SourceFile, "-"))  {
                        SourceFile = "/dev/stdin";
                }
        }

        return argi;
}

int
main(int argc, char **argv)
{
        ty = &vvv;

        TyArgc = argc;
        TyArgv = argv;

#if defined(TY_PROFILE_TYPES) && 1
        atexit(xxx);
#endif

        int nopt = (argc == 0) ? 0 : ProcessArgs(argv, true);

        switch (ColorMode) {
        case TY_COLOR_AUTO:   ColorStdout = isatty(1); ColorStderr = isatty(2); break;
        case TY_COLOR_ALWAYS: ColorStdout = true;      ColorStderr = true;      break;
        case TY_COLOR_NEVER:  ColorStdout = false;     ColorStderr = false;     break;
        }

#if defined(TY_PROFILER)
        if (ProfileOut == NULL) {
                ProfileOut = stdout;
        }

        switch (ColorMode) {
        case TY_COLOR_AUTO:   ColorProfile = isatty(fileno(ProfileOut)); break;
        case TY_COLOR_ALWAYS: ColorProfile = true;                       break;
        case TY_COLOR_NEVER:  ColorProfile = false;                      break;
        }

        ColorOutput = ColorProfile;
#else
        ColorOutput = ColorStderr;
#endif

        if (!vm_init(ty, argc - nopt, argv + nopt)) {
                DyingOfError = true;
                fprintf(stderr, "%s\n", TyError(ty));
                return -1;
        }

        argv += ProcessArgs(argv, false);

        if (argv[0] == NULL && stdin_is_tty()) {
                repl(ty);
        }

        char *source = slurp(SourceFile, NULL);
        if (source == NULL) {
                fprintf(stderr, "ty: %s: %s\n", SourceFile, strerror(errno));
                return 1;
        }

        if (UNLIKELY(HighlightOnly)) {
                if (!vm_load_program(ty, source, SourceFile)) {
                        DyingOfError = true;
                        fprintf(stderr, "%s\n", TyError(ty));
                        return 1;
                }

                Module *mod = CompilerCurrentModule(ty);
                byte_vector out = {0};

                syntax_highlight(
                        ty,
                        &out,
                        mod->source,
                        &mod->tokens,
                        0,
                        strlen(source),
                        NULL,
                        HighlightTheme
                );
                fputs(vv(out), stdout);

                return 0;
        }

        DebugWaitForClient(ty);

        if (!vm_execute(ty, source, SourceFile)) {
                DyingOfError = true;
                fprintf(stderr, "%s\n", TyError(ty));
                exit(67);
        }

        if (UNLIKELY(RunningTests)) {
                exit(RunTests(ty));
        }

        return 0;
}

/* vim: set sts=8 sw=8 expandtab: */
