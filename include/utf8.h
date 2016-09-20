#ifndef UTF8_H_INCLUDED
#define UTF8_H_INCLUDED

#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#include "unicode.h"

struct stringpos {
        int bytes;
        int graphemes;
};

inline static int
next_utf8(const char *str, int len, uint32_t *cp)
{
        unsigned char b0 = (str++)[0];
        int nbytes;

        if (!len)
                return -1;

        if (!b0)
                return -1;
        else if (b0 < 0x80) { // ASCII
                *cp = b0; return 1;
        }
        else if (b0 < 0xc0) // C1 or continuation
                return -1;
        else if (b0 < 0xe0) {
                nbytes = 2; *cp = b0 & 0x1f;
        }
        else if (b0 < 0xf0) {
                nbytes = 3; *cp = b0 & 0x0f;
        }
        else if (b0 < 0xf8) {
                nbytes = 4; *cp = b0 & 0x07;
        }
        else
                return -1;

        if (len < nbytes)
                return -1;

        for (int i = 1; i < nbytes; i++) {
                b0 = (str++)[0];
                if (!b0)
                        return -1;

                *cp <<= 6;
                *cp |= b0 & 0x3f;
        }

        return nbytes;
}

inline static bool
utf8_valid(char const *str, int len)
{
        uint32_t cp;

        while (len != 0) {
                int n = next_utf8(str, len, &cp);
                if (n == -1)
                        return false;
                len -= n;
                str += n;
        }

        return true;
}

inline static int
utf8_count(char const *str, int len, struct stringpos *pos)
{
        pos->bytes = 0;
        pos->graphemes = 0;

        while (len != 0) {

                if (*str == '\n' || *str == '\r') {
                        str += 1;
                        len -= 1;
                        pos->graphemes += 1;
                        pos->bytes += 1;
                        continue;
                }

                uint32_t cp;
                int bytes = next_utf8(str, len, &cp);
                if (bytes == -1)
                        return -1;

                /* Abort on C0 or C1 controls */
                if (cp < 0x20 || (cp >= 0x80 && cp < 0xa0))
                        return -1;

                int width = mk_wcwidth(cp);
                if (width == -1)
                        return -1;

                int is_grapheme = (width > 0) ? 1 : 0;

                str += bytes;
                len -= bytes;

                pos->bytes += bytes;
                pos->graphemes += is_grapheme;
        }

        return 0;
}

inline static int
utf8_stringcount(char const *str, int len, struct stringpos * restrict pos, struct stringpos const * restrict limit)
{
        pos->bytes = 0;
        pos->graphemes = 0;

        while (len != 0) {

                if (*str == '\n' || *str == '\r') {

                        if (pos->graphemes == limit->graphemes)
                                break;

                        str += 1;
                        len -= 1;

                        pos->graphemes += 1;
                        pos->bytes += 1;

                        continue;
                }

                uint32_t cp;
                int bytes = next_utf8(str, len, &cp);
                if (bytes == -1)
                        return -1;

                /* Abort on C0 or C1 controls */
                if (cp < 0x20 || (cp >= 0x80 && cp < 0xa0))
                        return -1;

                int width = mk_wcwidth(cp);
                if (width == -1)
                        return -1;

                int is_grapheme = (width > 0) ? 1 : 0;

                if (limit->bytes != -1 && pos->bytes + bytes > limit->bytes)
                        break;
                if (limit->graphemes != -1 && pos->graphemes + is_grapheme > limit->graphemes)
                        break;

                str += bytes;
                len -= bytes;

                pos->bytes += bytes;
                pos->graphemes += is_grapheme;
        }

        return 0;
}

inline static char *
utf8_copy_cols(char const * restrict str, int len, char * restrict out, int skip, int copy)
{
        char *bp = out;
        out += sizeof (int);

        int skipped = 0;
        int cols = 0;
        int n = 0;

        while (len != 0 && *str != '\n' && cols < copy) {

                uint32_t cp;
                int bytes = next_utf8(str, len, &cp);
                int width = mk_wcwidth(cp);

                if (skipped >= skip) {
                        n += bytes;
                        cols += width;
                        memcpy(out, str, bytes);
                        out += bytes;
                } else {
                        skipped += width;
                }

                str += bytes;
                len -= bytes;
        }

        memcpy(bp, &n, sizeof (int));

        return out;
}

inline static int
utf8_charcount(char const * restrict str, int len)
{
        int chars = 0;

        while (len != 0) {

                if (*str == '\n' || *str == '\r') {
                        ++str;
                        --len;
                        ++chars;
                        continue;
                }

                uint32_t cp;
                int bytes = next_utf8(str, len, &cp);
                int width = mk_wcwidth(cp);

                chars += (width > 0);
                str += bytes;
                len -= bytes;
        }

        return chars;
}

inline static char const *
utf8_nth_char(char const *str, int n, int *nb)
{
        while (n > 0) {

                if (*str == '\n' || *str == '\r') {
                        str += 1;
                        --n;
                        continue;
                }

                uint32_t cp;
                int bytes = next_utf8(str, 64, &cp); // bad
                int width = mk_wcwidth(cp);
                int is_grapheme = (width > 0) ? 1 : 0;

                str += bytes;
                n -= is_grapheme;
        }

        char const *result = str;
        *nb = 0;

        for (;;) {

                if (*str == '\n' || *str == '\r') {
                        *nb = 1;
                        break;
                }

                uint32_t cp;
                int bytes = next_utf8(str, 64, &cp); // bad
                int width = mk_wcwidth(cp);
                int is_grapheme = (width > 0) ? 1 : 0;

                str += bytes;
                *nb += bytes;

                if (is_grapheme)
                        break;
        }

        return result;
}

inline static char *
utf8_next_char(char const *s, int n)
{
	if (n == 0)
		return NULL;

	if (*s == '\n')
		return ((char *)s) + 1;

	uint32_t cp;
	int bytes = next_utf8(s, 64, &cp);

	return ((char *)s) + bytes;
}

#endif
