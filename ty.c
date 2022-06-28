#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdnoreturn.h>

#include <unistd.h>
#include <fcntl.h>
#include <dlfcn.h>

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

static bool use_readline = true;
static char buffer[8192];
static char *completions[MAX_COMPLETIONS + 1];

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
        if (use_readline)
                line = realloc(line, strlen(line) + 2);

        if (line[0] == ':') {
                if (line[1] == '!') {
                        system(line + 2) || 0;
				} else if (!vm_execute_file(line + 1)) {
                        fprintf(stderr, "%s\n", vm_error());
						good = false;
				}
                goto Add;

        }

        snprintf(buffer + 1, sizeof buffer - 2, "print(%s);", line);
        if (vm_execute(buffer + 1))
                goto Add;
        snprintf(buffer + 1, sizeof buffer - 2, "%s\n", line);
        if (strstr(vm_error(), "ParseError") != NULL && vm_execute(buffer + 1))
                goto Add;

        good = false;
        fprintf(stderr, "%s\n", vm_error());
Add:
        if (use_readline) {
                add_history(line);
        }

        fflush(stdout);

        return good;
}

noreturn static void
repl(void)
{

        for (char *line; line = readln(), line != NULL;) {
                execln(line);
        }

        exit(EXIT_SUCCESS);
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

        use_readline = isatty(0) && argc < 2;

        sqlite_load();

        if (use_readline) {
                rl_attempted_completion_function = complete;
                rl_basic_word_break_characters = ".\t\n\r ";
        }

        if (argc <= 1)
                repl();

        int i = 1;

        if (i < argc && strcmp(argv[i], "-q") == 0) {
                CheckConstraints = false;
                i += 1;
        }

        if (i < argc && strcmp(argv[i], "-e") == 0) {
                if (argc < 3) {
                        fputs("error: -e with no program specified", stderr);
                        return -1;
                }
                char buffer[8192] = {0};
                strncpy(buffer, argv[2], sizeof buffer - 1);

                if (!execln(buffer)) {
                        return -1;
                }
        } else {
                char const *file = (i < argc && strcmp(argv[i], "-") != 0) ? argv[i] : "/dev/stdin";
                if (!vm_execute_file(file)) {
                        fprintf(stderr, "%s\n", vm_error());
                        return -1;
                }
        }

        return 0;
}
