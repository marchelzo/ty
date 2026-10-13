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
#include <sys/stat.h>

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

#if defined(TY_EMBED_LIB) && !defined(TY_TEST) && !defined(TY_PROFILER)
#define TY_BUNDLER
#include "bundle.h"
#endif

Ty vvv;
TY xD;

static Ty *ty;

#define MAX_COMPLETIONS 512

static bool basic = false;
static char buffer[8192];

static char const *print_function = "print";
static bool help_imported = false;

static char const *SourceFile;

static int    TestArgIndex = -1;
static bool   TestSuite;
static bool   SawEvalOption;
static char **TestRunnerArgs;
static int    TestRunnerArgc;
static char **TestProgramArgs;
static int    TestProgramArgc;

static char const TestSuiteSource[] = "import os\nimport ty.test.cli as cli\nos.exit(cli.main(argv[1;]))\n";

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

#ifdef TY_BUNDLER
static char const *BundleOut = NULL;
static bool BundleRunning = false;
#endif

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
                "    --test [FILE | TARGET...] [OPTS]   Run tests: top-level pub functions in test files. \0"
                "                                       `ty --test --help` lists runner options.          \0"
#ifdef TY_BUNDLER
                "    --bundle[=OUT] SCRIPT                                                                \0"
                "                  Write a standalone executable OUT (default: SCRIPT without .ty) that   \0"
                "                  runs SCRIPT; ty options given alongside --bundle are kept              \0"
#endif
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

static void
dump_quoted(byte_vector *out, char const *s)
{
        dump(out, "'");

        for (; *s != '\0' && *s != '\n'; ++s) {
                if (*s == '\'' || *s == '\\') {
                        dump(out, "\\");
                }
                dump(out, "%c", *s);
        }

        dump(out, "'");
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
        } else if (s_eq_n(line, "help ", 5) || s_eq(line, "help")) {
                dump(&buffer, "%shelp(query: ", help_imported ? "" : "import help (help, grep)\n");
                dump_quoted(&buffer, line + 4);
                dump(&buffer, ");");
                if (repl_exec(ty, v_(buffer, 1))) {
                        help_imported = true;
                        goto End;
                } else {
                        goto Bad;
                }
        } else if (s_eq_n(line, "grep ", 5)) {
                dump(&buffer, "%sgrep(", help_imported ? "" : "import help (help, grep)\n");
                dump_quoted(&buffer, line + 5);
                dump(&buffer, ");");
                if (repl_exec(ty, v_(buffer, 1))) {
                        help_imported = true;
                        goto End;
                } else {
                        goto Bad;
                }
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
                help_imported = execln(ty, "import help (help, grep)\n");
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
                        if (first) {
                                TestArgIndex = argi;
                        }
                        break;
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

#ifdef TY_BUNDLER
                if (s_eq(argv[argi], "--bundle") || s_eq_n(argv[argi], "--bundle=", 9)) {
                        char const *eq = strchr(argv[argi], '=');
                        BundleOut = (eq != NULL) ? eq + 1 : "";
                        goto NextOption;
                }
#endif

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
                                        SawEvalOption = true;
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

        if (first && !RunningTests) {
                SourceFile = argv[argi];
                if (SourceFile == NULL || s_eq(SourceFile, "-"))  {
                        SourceFile = "/dev/stdin";
                }
        }

        return argi;
}

static bool
IsRegularFile(char const *path)
{
        struct stat st;
        return (stat(path, &st) == 0) && S_ISREG(st.st_mode);
}

static bool
IsLegacyTestFlag(char const *arg)
{
        if (arg[0] != '-' || arg[1] == '\0') {
                return false;
        }

        for (char const *p = arg + 1; *p != '\0'; ++p) {
                if (*p != 'j' && *p != 'q') {
                        return false;
                }
        }

        return true;
}

static char *
CloneSlice(char const *s, usize n)
{
        char *clone = xmA(n + 1);

        memcpy(clone, s, n);
        clone[n] = '\0';

        return clone;
}

static bool
SplitTestTarget(char const *arg, char **file, char **id, char **line)
{
        char const *sep;

        *id   = NULL;
        *line = NULL;

        if (IsRegularFile(arg)) {
                *file = (char *)arg;
                return true;
        }

        if ((sep = strstr(arg, "::")) != NULL) {
                *file = CloneSlice(arg, sep - arg);
                if (IsRegularFile(*file)) {
                        *id = (char *)(sep + 2);
                        return true;
                }
        }

        if (
                ((sep = strrchr(arg, ':')) != NULL)
             && (sep[1] != '\0')
             && (strspn(sep + 1, "0123456789") == strlen(sep + 1))
        ) {
                *file = CloneSlice(arg, sep - arg);
                if (IsRegularFile(*file)) {
                        *line = (char *)(sep + 1);
                        return true;
                }
        }

        return false;
}

static void
ClassifyTestArgs(int argc, char **argv)
{
        int k = TestArgIndex + 1;
        char *file;
        char *id;
        char *line;

        while (argv[k] != NULL && IsLegacyTestFlag(argv[k])) {
                for (char const *p = argv[k] + 1; *p != '\0'; ++p) {
                        if (*p == 'j') {
                                NoJIT = true;
                        } else {
                                CheckTypes = false;
                                DetailedExceptions = false;
                        }
                }
                k += 1;
        }

        if (
                SawEvalOption
             || ((argv[k] != NULL) && s_eq_n(argv[k], "-e", 2))
        ) {
                fprintf(stderr, "ty: --test needs a file or directory, not -e\n");
                exit(2);
        }

        if (
                (argv[k] != NULL)
             && (argv[k][0] != '-')
             && ((argv[k + 1] == NULL) || (argv[k + 1][0] == '-'))
             && SplitTestTarget(argv[k], &file, &id, &line)
        ) {
                int end = k + 1;

                while (argv[end] != NULL && !s_eq(argv[end], "--")) {
                        end += 1;
                }

                TestRunnerArgs = xmA((end - k + 4) * sizeof (char *));
                TestRunnerArgc = 0;

                for (int i = k + 1; i < end; ++i) {
                        TestRunnerArgs[TestRunnerArgc++] = argv[i];
                }

                if (id != NULL) {
                        TestRunnerArgs[TestRunnerArgc++] = "--id";
                        TestRunnerArgs[TestRunnerArgc++] = id;
                }

                if (line != NULL) {
                        TestRunnerArgs[TestRunnerArgc++] = "--line";
                        TestRunnerArgs[TestRunnerArgc++] = line;
                }

                TestRunnerArgs[TestRunnerArgc] = NULL;

                int rest = (argv[end] == NULL) ? end : end + 1;

                TestProgramArgs = xmA((argc - rest + 2) * sizeof (char *));
                TestProgramArgc = 0;
                TestProgramArgs[TestProgramArgc++] = file;

                for (int i = rest; i < argc; ++i) {
                        TestProgramArgs[TestProgramArgc++] = argv[i];
                }

                TestProgramArgs[TestProgramArgc] = NULL;

                SourceFile = file;
                TestSuite  = false;

                return;
        }

        if (CompileOnly) {
                fprintf(stderr, "ty: -c --test needs a single test file\n");
                exit(2);
        }

        TestProgramArgs = xmA((argc - k + 2) * sizeof (char *));
        TestProgramArgc = 0;
        TestProgramArgs[TestProgramArgc++] = argv[TestArgIndex];

        for (int i = k; i < argc; ++i) {
                TestProgramArgs[TestProgramArgc++] = argv[i];
        }

        TestProgramArgs[TestProgramArgc] = NULL;

        SourceFile = "(ty --test)";
        TestSuite  = true;
}

#if !defined(TY_TEST) && !defined(TY_PROFILER)
#if defined(TY_MULTICALL)
int
tytest_main(int argc, char **argv);
#endif

static noreturn void
ExecTestBinary(int argc, char **argv)
{
        char path[4096];
        char const *env = getenv("TY_TEST_BINARY");

#if defined(TY_MULTICALL)
        if (env == NULL || *env == '\0') {
                argv[0] = "tytest";
                exit(tytest_main(argc, argv));
        }
#endif

        if (env != NULL && *env != '\0') {
                snprintf(path, sizeof path, "%s", env);
        } else if (executable_path(path, sizeof path)) {
                char *slash = strrchr(path, '/');
                usize dir = (slash == NULL) ? 0 : (usize)(slash - path + 1);
                snprintf(path + dir, sizeof path - dir, "tytest");
        } else {
                snprintf(path, sizeof path, "tytest");
        }

        argv[0] = path;
        execv(path, argv);

        fprintf(
                stderr,
                "ty --test: cannot run %s: %s (build it with `make tytest`)\n",
                path,
                strerror(errno)
        );

        exit(2);
}
#endif

#ifdef TY_BUNDLER
static char **
BundleArgv(int *argc, char **argv)
{
        char const *const *flags;
        char const *entry;
        int nflags;
        int k = 0;

        if (*argc == 0) {
                return argv;
        }

        switch (bundle_state()) {
        case BUNDLE_NONE:
                return argv;

        case BUNDLE_BROKEN:
                fprintf(stderr, "%s: failed to unpack bundle: %s\n", argv[0], bundle_error());
                exit(1);

        case BUNDLE_READY:
                break;
        }

        entry = bundle_entry();
        if (entry == NULL) {
                return argv;
        }

        nflags = bundle_flags(&flags);

        char **out = xmA((*argc + nflags + 3) * sizeof *out);

        out[k++] = argv[0];
        for (int i = 0; i < nflags; ++i) {
                out[k++] = (char *)flags[i];
        }
        out[k++] = "--";
        out[k++] = (char *)entry;
        for (int i = 1; i < *argc; ++i) {
                out[k++] = argv[i];
        }
        out[k] = NULL;

        *argc = k;

        BundleRunning = true;
        bundle_preload();

        return out;
}

static noreturn void
RunBundler(int argc, char **argv, int nopt)
{
        char **flags = xmA((nopt + 1) * sizeof *flags);
        int nflags = 0;

        if (SourceFile == NULL || s_eq(SourceFile, "/dev/stdin")) {
                fprintf(stderr, "ty --bundle: missing script\n");
                exit(1);
        }

        for (int i = 1; i < nopt; ++i) {
                if (
                        !s_eq(argv[i], "--")
                     && !s_eq(argv[i], "--bundle")
                     && !s_eq_n(argv[i], "--bundle=", 9)
                ) {
                        flags[nflags++] = argv[i];
                }
        }

        bundle_snapshot();

        if (!vm_init(ty, argc - nopt, argv + nopt)) {
                DyingOfError = true;
                fprintf(stderr, "%s\n", TyError(ty));
                exit(1);
        }

        exit(bundle_create(ty, SourceFile, BundleOut, flags, nflags));
}
#endif

static noreturn void
RunTestMode(void)
{
        if (TestSuite) {
                if (!compiler_module_exists(ty, "ty/test/cli")) {
                        fprintf(stderr, "ty --test: suite runner unavailable\n");
                        exit(70);
                }

                if (!vm_execute(ty, TestSuiteSource, SourceFile)) {
                        DyingOfError = true;
                        fprintf(stderr, "%s\n", TyError(ty));
                        exit(70);
                }

                exit(0);
        }

        char *source = slurp(SourceFile, NULL);
        if (source == NULL) {
                fprintf(stderr, "ty: %s: %s\n", SourceFile, strerror(errno));
                exit(1);
        }

        TestFilePath = realpath(SourceFile, NULL);

        DebugWaitForClient(ty);

        if (!vm_execute(ty, source, SourceFile)) {
                DyingOfError = true;
                fprintf(stderr, "%s\n", TyError(ty));
                exit(67);
        }

        if (CompileOnly) {
                char **args = xmA((TestRunnerArgc + 3) * sizeof (char *));
                args[0] = "--list";
                args[1] = "--static";
                for (int i = 0; i < TestRunnerArgc; ++i) {
                        args[i + 2] = TestRunnerArgs[i];
                }
                args[TestRunnerArgc + 2] = NULL;
                exit(RunTestHarness(ty, args, TestRunnerArgc + 2));
        }

        exit(RunTestHarness(ty, TestRunnerArgs, TestRunnerArgc));
}

int
main(int argc, char **argv)
{
        ty = &vvv;

#ifdef TY_BUNDLER
        argv = BundleArgv(&argc, argv);
#endif

        TyArgc = argc;
        TyArgv = argv;

#if defined(TY_PROFILE_TYPES) && 1
        atexit(xxx);
#endif

        int nopt = (argc == 0) ? 0 : ProcessArgs(argv, true);

#if !defined(TY_TEST) && !defined(TY_PROFILER)
        if (RunningTests) {
                ExecTestBinary(argc, argv);
        }
#endif

        if (RunningTests) {
                ClassifyTestArgs(argc, argv);
        }

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

#ifdef TY_BUNDLER
        if (BundleRunning && nopt < argc) {
                argv[nopt] = argv[0];
        }

        if (BundleOut != NULL && !RunningTests) {
                RunBundler(argc, argv, nopt);
        }
#endif

        bool ok = RunningTests ? vm_init(ty, TestProgramArgc, TestProgramArgs)
                               : vm_init(ty, argc - nopt, argv + nopt);

        if (!ok) {
                DyingOfError = true;
                fprintf(stderr, "%s\n", TyError(ty));
                return -1;
        }

        argv += ProcessArgs(argv, false);

        if (RunningTests) {
                RunTestMode();
        }

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

        return 0;
}

/* vim: set sts=8 sw=8 expandtab: */
