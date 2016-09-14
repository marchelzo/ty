#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdnoreturn.h>

#include <unistd.h>

#include <readline/readline.h>
#include <readline/history.h>

#include "vm.h"

noreturn static void
repl(void)
{
        static char buffer[8192];

        vm_init();

        for (char *line; line = readline("> "), line != NULL;) {

                /*
                 * Very bad.
                 */
                line = realloc(line, strlen(line) + 2);
                strcat(line, "\n");

                sprintf(buffer, "print(%s);", line);
                if (vm_execute(buffer))
                        goto add;
                if (strstr(vm_error(), "ParseError") != NULL && vm_execute(line))
                        goto add;

                fprintf(stderr, "%s\n", vm_error());

                continue;
        add:
                add_history(line);
        }

        exit(EXIT_SUCCESS);
}

int
main(int argc, char **argv)
{

        if (argc <= 1 && isatty(0))
                repl();
          
        char const *file = (argc > 1 && strcmp(argv[1], "-") != 0) ? argv[1] : "/dev/stdin";

        vm_init();

        if (!vm_execute_file(file)) {
                fprintf(stderr, "%s\n", vm_error());
                return -1;
        }

        return 0;
}
