#include <stddef.h>
#include <string.h>

typedef int MainFn(int argc, char **argv);

MainFn ty_main;
MainFn tyls_main;
MainFn tytest_main;
MainFn typrof_main;

static struct {
        char const *name;
        char const *flag;
        MainFn     *main;
} const Tools[] = {
        { "tyls",   "--ls",   tyls_main   },
        { "tytest", NULL,     tytest_main },
        { "typrof", "--prof", typrof_main },
};

#define NTOOLS (sizeof Tools / sizeof Tools[0])

static char const *
base(char const *path)
{
        char const *slash = strrchr(path, '/');
        return (slash == NULL) ? path : slash + 1;
}

int
main(int argc, char **argv)
{
        char const *name = (argc > 0) ? base(argv[0]) : "ty";

        for (size_t i = 0; i < NTOOLS; ++i) {
                if (strcmp(name, Tools[i].name) == 0) {
                        return Tools[i].main(argc, argv);
                }
        }

        if (argc < 2) {
                return ty_main(argc, argv);
        }

        for (size_t i = 0; i < NTOOLS; ++i) {
                if (
                        (Tools[i].flag != NULL)
                     && (strcmp(argv[1], Tools[i].flag) == 0)
                ) {
                        argv[1] = (char *)Tools[i].name;
                        return Tools[i].main(argc - 1, argv + 1);
                }
        }

        return ty_main(argc, argv);
}
