#include <stdio.h>
#include <time.h>

#include "vm.h"
#include "util.h"

int
main(int argc, char **argv)
{

        char const *file = (argc > 1) ? argv[1] : "/dev/stdin";

        vm_init();

        if (!vm_execute_file(file)) {
                fprintf(stderr, "%s\n", vm_error());
                return -1;
        }

        return 0;
}
