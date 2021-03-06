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

#include "vm.h"
#include "gc.h"
#include "value.h"
#include "sqlite.h"
#include "util.h"

static bool use_readline = true;
static char buffer[8192];

static char *
readln(void)
{
        if (use_readline) {
                return readline("> ");
        } else {
                return fgets(buffer, sizeof buffer, stdin);
        }
}

static void
execln(char *line)
{
        static char buffer[8192];

        if (line[strspn(line, " \t\n")] == '\0')
                return;

        /*
         * Very bad.
         */
        if (use_readline)
                line = realloc(line, strlen(line) + 2);

        if (line[0] == ':') {
                if (line[1] == '!')
                        system(line + 2) || 0;
                else if (!vm_execute_file(line + 1))
                        fprintf(stderr, "%s\n", vm_error());
                goto Add;

        }

        snprintf(buffer + 1, sizeof buffer - 2, "print(%s);", line);
        if (vm_execute(buffer + 1))
                goto Add;
        snprintf(buffer + 1, sizeof buffer - 2, "%s\n", line);
        if (strstr(vm_error(), "ParseError") != NULL && vm_execute(buffer + 1))
                goto Add;

        fprintf(stderr, "%s\n", vm_error());
Add:
        if (use_readline) {
                add_history(line);
        }

        fflush(stdout);
}

noreturn static void
repl(void)
{

        for (char *line; line = readln(), line != NULL;) {
                execln(line);
        }

        exit(EXIT_SUCCESS);
}

int
main(int argc, char **argv)
{

        vm_init(argc, argv);

        use_readline = isatty(0) && argc < 2;

        sqlite_load();

        if (argc <= 1)
                repl();

        if (strcmp(argv[1], "-e") == 0) {
                if (argc < 3) {
                        fputs("error: -e with no program specified", stderr);
                }
                char buffer[8192] = {0};
                strncpy(buffer, argv[2], sizeof buffer - 1);
                execln(buffer);
        } else {
                char const *file = (argc > 1 && strcmp(argv[1], "-") != 0) ? argv[1] : "/dev/stdin";
                if (!vm_execute_file(file)) {
                        fprintf(stderr, "%s\n", vm_error());
                        return -1;
                }
        }

        return 0;
}
