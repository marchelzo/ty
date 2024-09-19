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
#include "table.h"
#include "compiler.h"
#include "class.h"
#include "blob.h"
#include "str.h"
#include "dict.h"
#include "array.h"
#include "polyfill_time.h"

#ifdef TY_HAVE_VERSION_INFO
#include "VersionInfo.h"
#endif

Ty MainTy;

static char const usage_string[] =
        "usage: ty [options] [script [args]]\n"
        "Available options are:\n"
        "  -c            Exit after compilation without executing the program\n"
        "  -e EXPR       Evaluate and print EXPR\n"
        "  -m MODULE     Import module MODULE\n"
        "  -p            Print the value of the last-evaluated expression before exiting\n"
        "  -q            Ignore constraints on function parameters and return values\n"
        "  -t LINE:COL   Find the definition of the symbol which occurs at LINE:COL\n"
        "                in the specified source file\n"
#ifdef TY_ENABLE_PROFILING
        "  -o FILE       Write profile data to FILE instead of stdout\n"
        "                 (if FILE is @ then stderr will be used)\n"
        "  --wall        Profile based on wall time instead of CPU time\n"
#endif
        "  --            Stop handling options\n"
        "  --version     Print ty version information and exit\n"
        "  --help        Print this help message and exit\n"
;

#define MAX_COMPLETIONS 240

static bool use_readline;
static char buffer[8192];
static char *completions[MAX_COMPLETIONS + 1];
static char const *print_function = "print";

bool EnableLogging = false;

static char **
complete(char const *s, int start, int end);

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
        return vm_execute(&MainTy, code, "(repl)");
}

static bool
execln(Ty *ty, char *line)
{
        static char buffer[8192];
        bool good = true;

        if (line[strspn(line, " \t\n")] == '\0')
                return true;

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
                } else if (!vm_execute_file(&MainTy, line + 1)) {
                        fprintf(stderr, "%s\n", vm_error(&MainTy));
                        good = false;
                }
                goto End;

        } else if (strncmp(line, "help ", 5) == 0) {
                snprintf(buffer + 1, sizeof buffer - 2, "help(%s);", line + 5);
                if (repl_exec(&MainTy, buffer + 1))
                        goto End;
                else
                        goto Bad;
        }

        snprintf(buffer + 1, sizeof buffer - 2, "%s(%s);", print_function, line);
        if (repl_exec(&MainTy, buffer + 1))
                goto End;
        snprintf(buffer + 1, sizeof buffer - 2, "%s\n", line);
        if (strstr(vm_error(&MainTy), "ParseError") != NULL && repl_exec(&MainTy, buffer + 1))
                goto End;
Bad:
        good = false;
        fprintf(stderr, "%s\n", vm_error(&MainTy));
End:

        fflush(stdout);

        return good;
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

        execln(&MainTy, "import help (..)");
        print_function = "prettyPrint";

        use_readline = true;

        for (;;) {
                (void)setjmp(InterruptJB);
                for (;;) {
                        char *line = readln();
                        if (line == NULL) {
                                exit(EXIT_SUCCESS);
                        }
                        execln(&MainTy, line);
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
                int n = compiler_get_completions(&MainTy, NULL, s, completions, 99);
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
        if (compiler_has_module(&MainTy, before + 1)) {
                n = compiler_get_completions(&MainTy, before + 1, s, completions, MAX_COMPLETIONS);
        } else {
                repl_exec(&MainTy, before + 1);

                struct value *v = vm_get(&MainTy, -1);

                switch (v->type) {
                case VALUE_OBJECT:
                        n += class_get_completions(&MainTy, v->class, s, completions, MAX_COMPLETIONS);
                        n += table_get_completions(&MainTy, v->object, s, completions + n, MAX_COMPLETIONS - n);
                        break;
                case VALUE_ARRAY:
                        n += array_get_completions(&MainTy, s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(&MainTy, CLASS_ARRAY, s, completions + n, MAX_COMPLETIONS - n);
                        break;
                case VALUE_DICT:
                        n += dict_get_completions(&MainTy, s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(&MainTy, CLASS_DICT, s, completions + n, MAX_COMPLETIONS - n);
                        break;
                case VALUE_STRING:
                        n += string_get_completions(&MainTy, s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(&MainTy, CLASS_STRING, s, completions + n, MAX_COMPLETIONS - n);
                        break;
                case VALUE_BLOB:
                        n += blob_get_completions(&MainTy, s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(&MainTy, CLASS_BLOB, s, completions + n, MAX_COMPLETIONS - n);
                        break;
                case VALUE_TUPLE:
                        n += tuple_get_completions(&MainTy, v, s, completions, MAX_COMPLETIONS);
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


#ifdef TY_ENABLE_PROFILING
static void
set_profile_out(char const *path)
{
        extern FILE *ProfileOut;

        if (strcmp(path, "@") == 0) {
                ProfileOut = stderr;
        } else {
                ProfileOut = fopen(path, "w+");
        }

        if (ProfileOut == NULL) {
                fprintf(
                        stderr,
                        "Failed to open %s for writing: %s",
                        path,
                        strerror(errno)
                );
                exit(EXIT_FAILURE);
        }
}
#endif

int
main(int argc, char **argv)
{
        if (!vm_init(&MainTy, argc, argv)) {
                fprintf(stderr, "%s\n", vm_error(&MainTy));
                return -1;
        }

        if (argc <= 1 && stdin_is_tty())
                repl(&MainTy);

        char SymbolLocation[512] = {0};

        int argi = 1;
        while (argv[argi] != NULL && argv[argi][0] == '-') {
                if (strcmp(argv[argi], "--") == 0) {
                        argi += 1;
                        break;
                }

                if (strcmp(argv[argi], "--version") == 0) {
#ifdef TY_HAVE_VERSION_INFO
                        printf(
                                "%s version %s\n"
                                "Compiler: %s %s\n"
                                "Platform: %s-%s\n",
                                VersionInfo_ProjectName,
                                VersionInfo_ProjectVersion,
                                VersionInfo_CompilerId,
                                VersionInfo_CompilerVersion,
                                VersionInfo_Architecture,
                                VersionInfo_BuildType
                        );
#else
                        printf("ty version 0.1\n");
#endif
                        return 0;
                }

                if (strcmp(argv[argi], "--help") == 0) {
                        fputs(usage_string, stdout);
                        return 0;
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
                                case 'c':
                                        CompileOnly = true;
                                        break;
                                case 'L':
                                        EnableLogging = true;
                                        break;
                                case 'p':
                                        PrintResult = true;
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
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -e\n");
                                                        return 1;
                                                }
                                                return (int)!execln(&MainTy, argv[++argi]);
                                        } else {
                                                return (int)!execln(&MainTy, (char *)(opt + 1));
                                        }
                                        break;
                                case 'm':
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -m\n");
                                                        return 1;
                                                }
                                                snprintf(buffer, sizeof buffer - 1, "import %s\n", argv[++argi]);
                                        } else {
                                                snprintf(buffer, sizeof buffer - 1, "import %s\n", opt + 1);
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        if (!execln(&MainTy, buffer)) {
                                                return 1;
                                        }
                                        break;
#ifdef TY_ENABLE_PROFILING
                                case 'o':
                                        if (opt[1] == '\0') {
                                                if (argv[argi + 1] == NULL) {
                                                        fprintf(stderr, "Missing argument for -o\n");
                                                        return 1;
                                                }
                                                set_profile_out(argv[++argi]);
                                        } else {
                                                set_profile_out(opt + 1);
                                                while (opt[1] != '\0') ++opt;
                                        }
                                        break;
#endif
                                default:
                                        fprintf(stderr, "Unrecognized option -%c\n", *opt);
                                        return 1;
                                }
                        }
                } else {
                        fprintf(stderr, "Unrecognized option %s\n", argv[argi]);
                        return 1;
                }

                argi += 1;
        }

        argc -= argi;
        argv += argi;

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

        char *source = fslurp(&MainTy, file);

        if (*SymbolLocation != '\0') {
                char *colon = strchr(SymbolLocation, ':');
                if (colon == NULL)
                        return -1;
                *colon = '\0';
                int line = atoi(SymbolLocation);
                int col = atoi(colon + 1);

                CompileOnly = true;
                if (!vm_execute(&MainTy, source, filename)) {
                        return 1;
                }

                struct location loc = compiler_find_definition(&MainTy, filename, line - 1, col - 1);

                if (loc.s == NULL) {
                        return -1;
                } else {
                        printf("%s:%d:%d\n", loc.s, loc.line + 1, loc.col + 1);
                        return 0;
                }
        }

        if (!vm_execute(&MainTy, source, filename)) {
                fprintf(stderr, "%s\n", vm_error(&MainTy));
                return -1;
        }

        return 0;
}

/* vim: set sts=8 sw=8 expandtab: */
