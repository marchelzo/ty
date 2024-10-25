#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdnoreturn.h>
#include <setjmp.h>
#include <errno.h>

#include "polyfill_unistd.h"
#include <fcntl.h>

#include <readline/readline.h>
#include <readline/history.h>

#include <pcre.h>

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
#include "dict.h"
#include "array.h"
#include "ty.h"
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
static char SymbolLocation[512];

static bool KindOfEnableLogging = false;
bool EnableLogging = false;

bool ColorStdout;
bool ColorStderr;

extern bool ProduceAnnotation;
extern FILE *DisassemblyOut;

#ifdef TY_ENABLE_PROFILING
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
#ifdef TY_ENABLE_PROFILING
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
        if (use_readline) {
                return readline("> ");
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

        if (line[0] == ':') {
                if (line[1] == '!') {
                        system(line + 2) || 0;
                } else if (!vm_execute_file(ty, line + 1)) {
                        fprintf(stderr, "%s\n", vm_error(ty));
                        good = false;
                }
                goto End;
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
        if (strstr(vm_error(ty), "ParseError") != NULL && repl_exec(ty, v_(buffer, 1)))
                goto End;

Bad:
        good = false;
        fprintf(stderr, "%s\n", vm_error(ty));

End:
        fflush(stdout);

        return good;
}


static void
pollute_with_bloat(void)
{
        execln(
                ty,
                "import help (..)\n"
                "import json     \n"
                "import base64   \n"
                "import math     \n"
                "import ty       \n"
                "import os       \n"
                "import time     \n"
                "import errno    \n"
                "import locale   \n"
                "import io       \n"
                "import sh       \n"
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
                }
        }
}

static char *
strclone(char const *s)
{
        char *new = malloc(strlen(s) + 1);
        strcpy(new, s);
        return new;
}

char *
completion_generator(char const *text, int state)
{
        return completions[state] ? strclone(completions[state]) : NULL;
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

        char before[500] = {0};
        memcpy(before + 1, rl_line_buffer, before_len);
        before[1 + before_len] = 0;

        int n = 0;

        /*
         * First check if it's a module name, otherwise treat it as an expression that
         * will evaluate to an object and then complete its members.
         */
        if (compiler_has_module(ty, before + 1)) {
                n = compiler_get_completions(ty, before + 1, s, completions, MAX_COMPLETIONS);
        } else {
                repl_exec(ty, before + 1);

                struct value *v = vm_get(ty, -1);

                switch (v->type) {
                case VALUE_NAMESPACE:
                        n += compiler_get_namespace_completions(ty, v->namespace, s, completions, MAX_COMPLETIONS);
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
                case VALUE_TUPLE:
                        n += tuple_get_completions(ty, v, s, completions, MAX_COMPLETIONS);
                        break;
                }
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

#ifdef TY_ENABLE_PROFILING
                extern bool UseWallTime;
                if (strcmp(argv[argi], "--wall") == 0) {
                        UseWallTime = true;
                } else
#endif

                if (argv[argi][1] != '-') {
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
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -t\n");
                                                        return 1;
                                                }
                                                snprintf(SymbolLocation, sizeof SymbolLocation - 1, "%s", argv[++argi]);
                                        } else {
                                                snprintf(SymbolLocation, sizeof SymbolLocation - 1, "%s", opt + 1);
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        break;
                                case 'e':
                                        if (!first && !basic) pollute_with_bloat();
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -e\n");
                                                        return 1;
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
                                                        :                 ":%s";

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
#ifdef TY_ENABLE_PROFILING
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
                                        fprintf(stderr, "Unrecognized option -%c\n", *opt);
                                        exit(1);
                                }
                        }
                } else {
BadOption:
                        fprintf(stderr, "Unrecognized option %s\n", argv[argi]);
                        exit(1);
                }
NextOption:
                argi += 1;
        }

        return argi;
}

int
main(int argc, char **argv)
{
        ty = &vvv;

        int nopt = (argc == 0) ? 0 : ProcessArgs(argv, true);

        switch (color_mode) {
        case TY_COLOR_AUTO:   ColorStdout = isatty(1); ColorStderr = isatty(2); break;
        case TY_COLOR_ALWAYS: ColorStdout = true;      ColorStderr = true;      break;
        case TY_COLOR_NEVER:  ColorStdout = false;     ColorStderr = false;     break;
        }

#ifdef TY_ENABLE_PROFILING
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
                fprintf(stderr, "%s\n", vm_error(ty));
                return -1;
        }

        argv += ProcessArgs(argv, false);

        if (argv[0] == NULL && stdin_is_tty()) {
                repl(ty);
        }

        FILE *file;
        char const *filename;
        if (argv[0] == NULL || strcmp(argv[0], "-") == 0) {
                file = stdin;
                filename = "<stdin>";
        } else {
                file = fopen(argv[0], "r");
                filename = argv[0];
        }

        if (file == NULL) {
                fprintf(stderr, "Failed to open source file '%s': %s\n", argv[0], strerror(errno));
                return 1;
        }

        char *source = fslurp(ty, file);

        if (*SymbolLocation != '\0') {
                char *colon = strchr(SymbolLocation, ':');
                if (colon == NULL)
                        return -1;
                *colon = '\0';
                int line = atoi(SymbolLocation);
                int col = atoi(colon + 1);

                CompileOnly = true;
                if (!vm_execute(ty, source, filename)) {
                        return 1;
                }

                Location loc = compiler_find_definition(ty, filename, line - 1, col - 1);

                if (loc.s == NULL) {
                        return -1;
                } else {
                        printf("%s:%d:%d\n", loc.s, loc.line + 1, loc.col + 1);
                        return 0;
                }
        }

        if (!vm_execute(ty, source, filename)) {
                fprintf(stderr, "%s\n", vm_error(ty));
                return -1;
        }

        return 0;
}

/* vim: set sts=8 sw=8 expandtab: */
