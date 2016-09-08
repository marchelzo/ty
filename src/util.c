#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

#include "panic.h"
#include "alloc.h"

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
        FILE *f = fopen(path, "r");
        if (f == NULL) {
                return NULL;
        }

        char *contents = NULL;
        int capacity = 0;
        int used = 0;

        int n;
        static char buffer[4096];
        while ((n = fread(buffer, 1, sizeof buffer, f)) != 0) {
                if (n + used >= capacity) {
                        capacity += n;
                        capacity *= 2;
                        resize(contents, capacity);
                }

                memcpy(contents + used, buffer, n);
                used += n;
        }

        fclose(f);

        contents[used] = '\0';
        return contents;
}
