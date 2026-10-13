#include <ctype.h>
#include <stdbool.h>
#include <string.h>

#include <utf8proc.h>

#include "defs.h"
#include "vec.h"
#include "xd.h"

static struct {
        i32 lo;
        i32 hi;
} const EmojiRanges[] = {
        { 0x00023, 0x00023 }, { 0x0002A, 0x0002A }, { 0x00030, 0x00039 },
        { 0x000A9, 0x000A9 }, { 0x000AE, 0x000AE }, { 0x0203C, 0x0203C },
        { 0x02049, 0x02049 }, { 0x02122, 0x02122 }, { 0x02139, 0x02139 },
        { 0x02194, 0x02199 }, { 0x021A9, 0x021AA }, { 0x0231A, 0x0231B },
        { 0x02328, 0x02328 }, { 0x023CF, 0x023CF }, { 0x023E9, 0x023F3 },
        { 0x023F8, 0x023FA }, { 0x024C2, 0x024C2 }, { 0x025AA, 0x025AB },
        { 0x025B6, 0x025B6 }, { 0x025C0, 0x025C0 }, { 0x025FB, 0x025FE },
        { 0x02600, 0x02604 }, { 0x0260E, 0x0260E }, { 0x02611, 0x02611 },
        { 0x02614, 0x02615 }, { 0x02618, 0x02618 }, { 0x0261D, 0x0261D },
        { 0x02620, 0x02620 }, { 0x02622, 0x02623 }, { 0x02626, 0x02626 },
        { 0x0262A, 0x0262A }, { 0x0262E, 0x0262F }, { 0x02638, 0x0263A },
        { 0x02640, 0x02640 }, { 0x02642, 0x02642 }, { 0x02648, 0x02653 },
        { 0x0265F, 0x02660 }, { 0x02663, 0x02663 }, { 0x02665, 0x02666 },
        { 0x02668, 0x02668 }, { 0x0267B, 0x0267B }, { 0x0267E, 0x0267F },
        { 0x02692, 0x02697 }, { 0x02699, 0x02699 }, { 0x0269B, 0x0269C },
        { 0x026A0, 0x026A1 }, { 0x026A7, 0x026A7 }, { 0x026AA, 0x026AB },
        { 0x026B0, 0x026B1 }, { 0x026BD, 0x026BE }, { 0x026C4, 0x026C5 },
        { 0x026C8, 0x026C8 }, { 0x026CE, 0x026CF }, { 0x026D1, 0x026D1 },
        { 0x026D3, 0x026D4 }, { 0x026E9, 0x026EA }, { 0x026F0, 0x026F5 },
        { 0x026F7, 0x026FA }, { 0x026FD, 0x026FD }, { 0x02702, 0x02702 },
        { 0x02705, 0x02705 }, { 0x02708, 0x0270D }, { 0x0270F, 0x0270F },
        { 0x02712, 0x02712 }, { 0x02714, 0x02714 }, { 0x02716, 0x02716 },
        { 0x0271D, 0x0271D }, { 0x02721, 0x02721 }, { 0x02728, 0x02728 },
        { 0x02733, 0x02734 }, { 0x02744, 0x02744 }, { 0x02747, 0x02747 },
        { 0x0274C, 0x0274C }, { 0x0274E, 0x0274E }, { 0x02753, 0x02755 },
        { 0x02757, 0x02757 }, { 0x02763, 0x02764 }, { 0x02795, 0x02797 },
        { 0x027A1, 0x027A1 }, { 0x027B0, 0x027B0 }, { 0x027BF, 0x027BF },
        { 0x02934, 0x02935 }, { 0x02B05, 0x02B07 }, { 0x02B1B, 0x02B1C },
        { 0x02B50, 0x02B50 }, { 0x02B55, 0x02B55 }, { 0x03030, 0x03030 },
        { 0x0303D, 0x0303D }, { 0x03297, 0x03297 }, { 0x03299, 0x03299 },
        { 0x1F004, 0x1F004 }, { 0x1F0CF, 0x1F0CF }, { 0x1F170, 0x1F171 },
        { 0x1F17E, 0x1F17F }, { 0x1F18E, 0x1F18E }, { 0x1F191, 0x1F19A },
        { 0x1F1E6, 0x1F1FF }, { 0x1F201, 0x1F202 }, { 0x1F21A, 0x1F21A },
        { 0x1F22F, 0x1F22F }, { 0x1F232, 0x1F23A }, { 0x1F250, 0x1F251 },
        { 0x1F300, 0x1F321 }, { 0x1F324, 0x1F393 }, { 0x1F396, 0x1F397 },
        { 0x1F399, 0x1F39B }, { 0x1F39E, 0x1F3F0 }, { 0x1F3F3, 0x1F3F5 },
        { 0x1F3F7, 0x1F4FD }, { 0x1F4FF, 0x1F53D }, { 0x1F549, 0x1F54E },
        { 0x1F550, 0x1F567 }, { 0x1F56F, 0x1F570 }, { 0x1F573, 0x1F57A },
        { 0x1F587, 0x1F587 }, { 0x1F58A, 0x1F58D }, { 0x1F590, 0x1F590 },
        { 0x1F595, 0x1F596 }, { 0x1F5A4, 0x1F5A5 }, { 0x1F5A8, 0x1F5A8 },
        { 0x1F5B1, 0x1F5B2 }, { 0x1F5BC, 0x1F5BC }, { 0x1F5C2, 0x1F5C4 },
        { 0x1F5D1, 0x1F5D3 }, { 0x1F5DC, 0x1F5DE }, { 0x1F5E1, 0x1F5E1 },
        { 0x1F5E3, 0x1F5E3 }, { 0x1F5E8, 0x1F5E8 }, { 0x1F5EF, 0x1F5EF },
        { 0x1F5F3, 0x1F5F3 }, { 0x1F5FA, 0x1F64F }, { 0x1F680, 0x1F6C5 },
        { 0x1F6CB, 0x1F6D2 }, { 0x1F6D5, 0x1F6D7 }, { 0x1F6DC, 0x1F6E5 },
        { 0x1F6E9, 0x1F6E9 }, { 0x1F6EB, 0x1F6EC }, { 0x1F6F0, 0x1F6F0 },
        { 0x1F6F3, 0x1F6FC }, { 0x1F7E0, 0x1F7EB }, { 0x1F7F0, 0x1F7F0 },
        { 0x1F90C, 0x1F93A }, { 0x1F93C, 0x1F945 }, { 0x1F947, 0x1F9FF },
        { 0x1FA70, 0x1FA7C }, { 0x1FA80, 0x1FA89 }, { 0x1FA8F, 0x1FAC6 },
        { 0x1FACE, 0x1FADC }, { 0x1FADF, 0x1FAE9 }, { 0x1FAF0, 0x1FAF8 },
};

static bool
IsEmoji(i32 cp)
{
        isize lo = 0;
        isize hi = sizeof EmojiRanges / sizeof EmojiRanges[0];

        if (cp < EmojiRanges[0].lo) {
                return false;
        }

        while (lo < hi) {
                isize mid = lo + (hi - lo) / 2;
                if (cp < EmojiRanges[mid].lo) {
                        hi = mid;
                } else if (cp > EmojiRanges[mid].hi) {
                        lo = mid + 1;
                } else {
                        return true;
                }
        }

        return false;
}

inline static bool
IsRegional(i32 cp)
{
        return (cp >= 0x1F1E6) && (cp <= 0x1F1FF);
}

inline static bool
IsModifier(i32 cp)
{
        return (cp >= 0x1F3FB) && (cp <= 0x1F3FF);
}

static int
Presentation(i32 base, i32 next, int width)
{
        bool vs = (next == 0xFE0E) || (next == 0xFE0F);

        if (!(vs || IsModifier(next)) || !IsEmoji(base)) {
                return width;
        }

        return (next == 0xFE0E) ? 1 : 2;
}

isize
term_esc_len(u8 const *s, isize n, isize i)
{
        isize j;

        if (s[i] != 0x1B) {
                return 0;
        }

        if (i + 1 >= n) {
                return 1;
        }

        switch (s[i + 1]) {
        case '[':
                for (j = i + 2; j < n; ++j) {
                        if (s[j] >= 0x40 && s[j] <= 0x7E) {
                                return j + 1 - i;
                        }
                        if (s[j] < 0x20 || s[j] > 0x3F) {
                                return j - i;
                        }
                }
                return n - i;

        case ']':
        case 'P':
        case '_':
        case '^':
        case 'X':
                for (j = i + 2; j < n; ++j) {
                        switch (s[j]) {
                        case 0x07:
                        case 0x18:
                        case 0x1A:
                                return j + 1 - i;

                        case 0x1B:
                                if (j + 1 < n && s[j + 1] == '\\') {
                                        return j + 2 - i;
                                }
                                return j - i;
                        }
                }
                return n - i;
        }

        for (j = i + 1; j < n && s[j] >= 0x20 && s[j] <= 0x2F; ++j) {
                ;
        }

        if (j < n && s[j] >= 0x30 && s[j] <= 0x7E) {
                return j + 1 - i;
        }

        return j - i;
}

inline static i32
Decode(u8 const *s, isize n, isize *len)
{
        if (s[0] < 0x80) {
                *len = 1;
                return s[0];
        }

        if (s[0] >= 0xC2 && s[0] <= 0xDF && n >= 2 && (s[1] & 0xC0) == 0x80) {
                *len = 2;
                return ((s[0] & 0x1F) << 6) | (s[1] & 0x3F);
        }

        if (
                (s[0] & 0xF0) == 0xE0
             && (n >= 3)
             && ((s[1] & 0xC0) == 0x80)
             && ((s[2] & 0xC0) == 0x80)
        ) {
                i32 cp = ((s[0] & 0x0F) << 12) | ((s[1] & 0x3F) << 6) | (s[2] & 0x3F);
                if (cp >= 0x800 && (cp < 0xD800 || cp > 0xDFFF)) {
                        *len = 3;
                        return cp;
                }
        }

        return -1;
}

inline static int
SimpleWidth(i32 cp)
{
        u32 c = (u32)cp;

        if (c < 0x300) {
                return (c >= 0x20 && c != 0x7F && (c < 0x80 || c >= 0xA0)) ? 1 : -1;
        }

        if (c < 0x3000) {
                if (c >= 0x2500) {
                        return (c <= 0x25FC || (c >= 0x2800 && c <= 0x28FF)) ? 1 : -1;
                }
                if (c >= 0x2010) {
                        return (c <= 0x2027) ? 1 : -1;
                }
                return ((c >= 0x370 && c <= 0x482) || (c >= 0x48A && c <= 0x52F)) ? 1 : -1;
        }

        if (c >= 0x4E00) {
                if (
                        (c <= 0x9FFF)
                     || (c >= 0xAC00 && c <= 0xD7A3)
                     || (c >= 0xFF01 && c <= 0xFF60)
                ) {
                        return 2;
                }
                return -1;
        }

        if (
                (c <= 0x3029)
             || (c >= 0x3041 && c <= 0x3096)
             || (c >= 0x30A1 && c <= 0x30FA)
             || (c >= 0x3400 && c <= 0x4DBF)
        ) {
                return 2;
        }

        return -1;
}

static isize
Cluster(u8 const *s, isize n, isize i, int *w)
{
        i32 cp;
        i32 next;
        i32 state = 0;
        isize len = utf8proc_iterate(s + i, n - i, &cp);

        if (len <= 0) {
                *w = 0;
                return 1;
        }

        int width = IsRegional(cp) ? 2 : utf8proc_charwidth(cp);
        i32 prev  = cp;
        isize end = i + len;

        while (end < n) {
                isize m = utf8proc_iterate(s + end, n - end, &next);

                if (m <= 0 || utf8proc_grapheme_break_stateful(prev, next, &state)) {
                        break;
                }

                if (end == i + len) {
                        width = Presentation(cp, next, width);
                }

                prev = next;
                end += m;
        }

        *w = width;

        return end - i;
}

isize
term_cluster(u8 const *s, isize n, isize i, int *w)
{
        isize m;
        isize m2;
        i32 cp = Decode(s + i, n - i, &m);

        if (cp == '\r' && i + 1 < n && s[i + 1] == '\n') {
                *w = 0;
                return 2;
        }

        if (cp >= 0 && (cp < 0x20 || cp == 0x7F)) {
                *w = 0;
                return 1;
        }

        int sw = (cp >= 0) ? SimpleWidth(cp) : -1;

        if (sw > 0) {
                if (i + m >= n) {
                        *w = sw;
                        return m;
                }

                i32 nx = Decode(s + i + m, n - i - m, &m2);

                if (nx >= 0 && (nx < 0x20 || nx == 0x7F || SimpleWidth(nx) > 0)) {
                        *w = sw;
                        return m;
                }
        }

        return Cluster(s, n, i, w);
}

static isize
Run(u8 const *s, isize n, isize i, isize cols, isize *width)
{
        isize acc = *width;
        isize m;
        i32 cp = Decode(s + i, n - i, &m);
        int sw = (cp >= 0) ? SimpleWidth(cp) : -1;

        while (sw > 0 && acc + sw <= cols) {
                isize j  = i + m;
                isize m2 = 0;
                int nsw  = 0;

                if (j < n && s[j] >= 0x80) {
                        i32 nx = Decode(s + j, n - j, &m2);
                        nsw = (nx >= 0) ? SimpleWidth(nx) : -1;
                        if (nsw < 0) {
                                break;
                        }
                }

                acc += sw;
                i  = j;
                m  = m2;
                sw = nsw;
        }

        *width = acc;

        return i;
}

static isize
Fit(u8 const *s, isize n, isize cols, isize *out)
{
        isize width = 0;
        isize i = 0;

        while (i < n) {
                u8 c = s[i];
                isize m;
                int w;

                if (c == 0x1B) {
                        i += term_esc_len(s, n, i);
                        continue;
                }

                if (c >= 0x20 && c < 0x7F && (i + 1 >= n || s[i + 1] < 0x80)) {
                        m = 1;
                        w = 1;
                } else if (c >= 0x80) {
                        isize j = Run(s, n, i, cols, &width);
                        if (j > i) {
                                i = j;
                                continue;
                        }
                        m = Cluster(s, n, i, &w);
                } else {
                        m = term_cluster(s, n, i, &w);
                }

                if (width + w > cols) {
                        break;
                }

                width += w;
                i += m;
        }

        *out = width;

        return i;
}

isize
term_width(void const *s, isize n)
{
        isize width;

        if (n == -1) {
                n = strlen(s);
        }

        Fit(s, n, INT64_MAX, &width);

        return width;
}

isize
term_fit_cols(void const *s, isize n, int cols)
{
        isize width;

        if (n == -1) {
                n = strlen(s);
        }

        return Fit(s, n, cols, &width);
}

bool
term_esc_is_sgr(u8 const *e, isize k)
{
        if (k < 3 || e[1] != '[' || e[k - 1] != 'm') {
                return false;
        }

        for (isize j = 2; j < k - 1; ++j) {
                if (!(isdigit(e[j]) || e[j] == ';' || e[j] == ':')) {
                        return false;
                }
        }

        return true;
}

int
term_sgr_reset(u8 const *e, isize k)
{
        isize j = 2;

        while (j < k - 1 && e[j] == '0') {
                j += 1;
        }

        if (j == k - 1) {
                return 1;
        }

        return (e[j] == ';') ? 2 : 0;
}

bool
term_esc_is_osc8(u8 const *e, isize k)
{
        return (k >= 4)
            && (e[1] == ']')
            && (e[2] == '8')
            && (e[3] == ';');
}

bool
term_osc8_opens(u8 const *e, isize k)
{
        isize end = k;

        if (e[k - 1] == 0x07) {
                end = k - 1;
        } else if (k >= 2 && e[k - 2] == 0x1B && e[k - 1] == '\\') {
                end = k - 2;
        }

        u8 const *uri = memchr(e + 4, ';', max(end - 4, 0));

        return (uri != NULL) && (uri + 1 < e + end);
}

void
term_clip(byte_vector *out, u8 const *s, isize n, int cols)
{
        isize width;
        isize keep  = Fit(s, n, cols, &width);
        isize reset = keep;
        isize link  = -1;
        u8 const *e;

        xvPn(*out, (char const *)s, keep);

        if (keep >= n) {
                return;
        }

        for (isize pad = cols - width; pad > 0; --pad) {
                xvP(*out, ' ');
        }

        for (isize i = keep; (e = memchr(s + i, 0x1B, n - i)) != NULL;) {
                i = e - s;
                isize k = term_esc_len(s, n, i);
                if (term_esc_is_sgr(e, k) && term_sgr_reset(e, k) != 0) {
                        reset = i;
                } else if (term_esc_is_osc8(e, k)) {
                        link = i;
                }
                i += k;
        }

        for (isize i = keep; (e = memchr(s + i, 0x1B, n - i)) != NULL;) {
                i = e - s;
                isize k = term_esc_len(s, n, i);
                if (
                        (term_esc_is_sgr(e, k) && i >= reset)
                     || (i == link)
                     || (k > 2 && e[1] >= 0x20 && e[1] <= 0x2F)
                ) {
                        xvPn(*out, (char const *)e, k);
                }
                i += k;
        }
}
