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
#include "vec.h"

uintmax_t
umax(uintmax_t a, uintmax_t b)
{
        return (a > b) ? a : b;
}

uintmax_t
umin(uintmax_t a, uintmax_t b)
{
        return (a < b) ? a : b;
}

intmax_t
max(intmax_t a, intmax_t b)
{
        return (a > b) ? a : b;
}

intmax_t
min(intmax_t a, intmax_t b)
{
        return (a < b) ? a : b;
}

char *
sclone(char const *s)
{
        size_t n = strlen(s);
        char *new = alloc(n + 1);
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

                char *s = alloc(n + 1);
                memcpy(s, p, n);
                s[n] = '\0';

                munmap(p, n);
                close(fd);

                return s;
        } else {
                vec(char) s;
                char b[1UL << 14];
                int r;

                vec_init(s);
                
                while ((r = read(fd, b, sizeof b)) > 0) {
                        for (int i = 0; i < r; ++i) {
                                vec_push(s, b[i]);
                        }
                }

                vec_push(s, '\0');
                return s.items;
        }

}
