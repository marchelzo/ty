#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdnoreturn.h>
#include <setjmp.h>

#include <unistd.h>
#include <fcntl.h>
#include <dlfcn.h>
#include <getopt.h>

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

#define MAX_COMPLETIONS 200

static bool use_readline;
static char buffer[8192];
static char *completions[MAX_COMPLETIONS + 1];

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

static bool
execln(char *line)
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
                } else if (!vm_execute_file(line + 1)) {
                        fprintf(stderr, "%s\n", vm_error());
                        good = false;
                }
                goto End;

        } else if (strncmp(line, "help ", 5) == 0) {
                snprintf(buffer + 1, sizeof buffer - 2, "help(%s);", line + 5);
                if (vm_execute(buffer + 1))
                        goto End;
                else
                        goto Bad;
        }

        snprintf(buffer + 1, sizeof buffer - 2, "print(%s);", line);
        if (vm_execute(buffer + 1))
                goto End;
        snprintf(buffer + 1, sizeof buffer - 2, "%s\n", line);
        if (strstr(vm_error(), "ParseError") != NULL && vm_execute(buffer + 1))
                goto End;
Bad:
        good = false;
        fprintf(stderr, "%s\n", vm_error());
End:

        fflush(stdout);

        return good;
}

noreturn static void
repl(void);

static jmp_buf InterruptJB;

static void
sigint(int signal)
{
        puts("Interrupted.");
        longjmp(InterruptJB, 1);
}

noreturn static void
repl(void)
{
        rl_attempted_completion_function = complete;
        rl_basic_word_break_characters = ".\t\n\r ";

        signal(SIGINT, sigint);

        execln("import help (..)");

        use_readline = true;

        for (;;) {
                (void)setjmp(InterruptJB);
                for (;;) {
                        char *line = readln();
                        if (line == NULL) {
                                exit(EXIT_SUCCESS);
                        }
                        execln(line);
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
                int n = compiler_get_completions(NULL, s, completions, 99);
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
        if (compiler_has_module(before + 1)) {
                n = compiler_get_completions(before + 1, s, completions, MAX_COMPLETIONS);
        } else {
                vm_execute(before + 1);

                struct value *v = vm_get(-1);

                switch (v->type) {
                case VALUE_OBJECT:
                        n += class_get_completions(v->class, s, completions, MAX_COMPLETIONS);
                        n += table_get_completions(v->object, s, completions + n, MAX_COMPLETIONS - n);
                        break;
                case VALUE_ARRAY:
                        n += array_get_completions(s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(CLASS_ARRAY, s, completions, MAX_COMPLETIONS - n);
                        break;
                case VALUE_DICT:
                        n += dict_get_completions(s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(CLASS_DICT, s, completions, MAX_COMPLETIONS - n);
                        break;
                case VALUE_STRING:
                        n += string_get_completions(s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(CLASS_STRING, s, completions, MAX_COMPLETIONS - n);
                        break;
                case VALUE_BLOB:
                        n += blob_get_completions(s, completions, MAX_COMPLETIONS);
                        n += class_get_completions(CLASS_BLOB, s, completions, MAX_COMPLETIONS - n);
                        break;
                case VALUE_TUPLE:
                        n += tuple_get_completions(v, s, completions, MAX_COMPLETIONS);
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

int
main(int argc, char **argv)
{
        vm_init(argc, argv);

        if (argc <= 1)
                repl();

        char SymbolLocation[512] = {0};

        for (int ch; (ch = getopt_long(argc, argv, "+qcpLm:t:e:", NULL, NULL)) != -1;) {
                switch (ch) {
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
                case 'm':
                        snprintf(buffer, sizeof buffer, "import %s\n", optarg);
                        if (!execln(buffer))
                                return -1;
                        break;
                case 't':
                        strcpy(SymbolLocation, optarg);
                        break;
                case 'e':
                        return (int)execln(optarg);
                }
        }

        argc -= optind;
        argv += optind;

        char const *file = (argv[0] != NULL && strcmp(argv[0], "-") != 0) ? argv[0] : "/dev/stdin";

        if (*SymbolLocation != '\0') {
                char *colon = strchr(SymbolLocation, ':');
                if (colon == NULL)
                        return -1;
                *colon = '\0';
                int line = atoi(SymbolLocation);
                int col = atoi(colon + 1);
                struct location loc = compiler_find_definition(file, line, col);
                if (loc.s == NULL) {
                        return -1;
                } else {
                        printf("%s:%d:%d\n", loc.s, loc.line + 1, loc.col + 1);
                        return 0;
                }
        }

        if (!vm_execute_file(file)) {
                fprintf(stderr, "%s\n", vm_error());
                return -1;
        }

        return 0;
}

/* vim: set sts=8 sw=8 expandtab: */
