#ifndef _POLYFILL_MEMMEM_H
#define _POLYFILL_MEMMEM_H

#include <stdlib.h>

#ifdef _WIN32

inline static void *
memmem(const void *haystack, size_t hs_len, const void *needle, size_t ne_len)
{
    const char *hs = (char const *)haystack;
    const char *ne = (char const *)needle;

    if (ne_len == 0)
        return (void *)hs;
    int i;
    int c = ne[0];
    const char *end = hs + hs_len - ne_len;

    for (; hs <= end; hs++)
    {
        if (hs[0] != c)
            continue;
        for (i = ne_len - 1; i != 0; i--)
            if (hs[i] != ne[i])
                break;
        if (i == 0)
            return (void *)hs;
    }

    return NULL;
}

#endif
#endif
