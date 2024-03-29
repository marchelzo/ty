#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>

#include "panic.h"
#include "alloc.h"
#include "util.h"
#include "vec.h"

_Thread_local char ERR[ERR_SIZE];

char *
sclone_malloc(char const *s)
{
        size_t n = strlen(s);
        char *new = malloc(n + 1);

        if (new == NULL) {
                panic("out of memory");
        }

        memcpy(new, s, n + 1);

        return new;
}

char *
sclone(char const *s)
{
        size_t n = strlen(s);
        char *new = gc_alloc(n + 1);
        memcpy(new, s, n + 1);
        return new;
}

char *
sclonea(char const *s)
{
        size_t n = strlen(s);
        char *new = Allocate(n + 1);
        memcpy(new, s, n + 1);
        return new;
}

bool
contains(char const *s, char c)
{
        return (c != '\0') && (strchr(s, c) != NULL);
}

char *
slurp(char const *path)
{
        int fd = open(path, O_RDONLY);
        if (fd == -1) {
                return NULL;
        }

        struct stat st;
        fstat(fd, &st);

        if (S_ISREG(st.st_mode) || S_ISLNK(st.st_mode)) {
                int n = st.st_size;

                void *p = mmap(NULL, n, PROT_READ, MAP_SHARED, fd, 0);
                if (p == NULL) {
                        return NULL;
                }

                char *s = gc_alloc(n + 2);
                memcpy(s + 1, p, n);
                s[0] = s[n + 1] = '\0';

                munmap(p, n);
                close(fd);

                return s + 1;
        } else {
                vec(char) s;
                vec_init(s);

                vec_push(s, '\0');

                char b[1UL << 14];
                int r;

                while ((r = read(fd, b, sizeof b)) > 0) {
                        for (int i = 0; i < r; ++i) {
                                vec_push(s, b[i]);
                        }
                }

                vec_push(s, '\0');

                return s.items + 1;
        }
}
