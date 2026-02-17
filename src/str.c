#include <string.h>

#include <utf8proc.h>
#include <pcre2.h>

#include "functions.h"
#include "gc.h"
#include "mmmm.h"
#include "ty.h"
#include "xd.h"
#include "value.h"
#include "vm.h"

#define ty_re_match(...) pcre2_match(__VA_ARGS__, ty->pcre2.match, ty->pcre2.ctx)
#define ty_re_ovec()     pcre2_get_ovector_pointer(ty->pcre2.match)

#define ty_re_panic(e) do {                     \
        void *msg = smA(4096);                  \
        pcre2_get_error_message(e, msg, 4096);  \
        bP("PCRE2: %s", msg);                   \
} while (0)


inline static isize
rune_count(u8 const *s, isize n)
{
        isize count = 0;

        while (n != 0) {
                i32 rune;
                isize bytes = utf8proc_iterate(s, n, &rune);
                if (bytes <= 0) {
                        n -= 1;
                        s += 1;
                } else {
                        count += 1;
                        n -= bytes;
                        s += bytes;
                }
        }

        return count;
}

inline static isize
TyStrLen(Value const *str)
{
        return rune_count(ss(*str), sN(*str));
}

inline static isize
x_x_x(u8 const *s, isize sz, isize ncp)
{
        isize off = 0;
        isize count = 0;


        while (off < sz && count < ncp) {
                i32 rune;
                isize bytes = utf8proc_iterate(s + off, sz - off, &rune);
                if (bytes <= 0) {
                        off += 1;
                } else {
                        off += bytes;
                }
                count += 1;
        }

        return off;
}

inline static bool
is_prefix(void const *big, isize blen, void const *little, isize slen)
{
        return (blen >= slen) && (memcmp(big, little, slen) == 0);
}

inline static Value
mkmatch(Ty *ty, Value *s, usize *ovec, isize n, bool detailed)
{
        if (detailed) {
                Value groups = ARRAY(vAn(n));

                for (isize i = 0; i < n; ++i) {
                        isize off = ovec[2*i];
                        isize len = ovec[2*i + 1] - ovec[2*i];
                        vPx(*groups.array, (off == -1) ? NIL : STRING_VIEW(*s, off, len));
                }

                GC_STOP();
                Value match = RawObject(CLASS_RE_MATCH);
                PutMember(match, NAMES.str, *s);
                PutMember(match, NAMES.groups, groups);
                GC_RESUME();

                return match;
        } else if (n == 1) {
                return STRING_VIEW(*s, ovec[0], ovec[1] - ovec[0]);
        } else {
                Value match = ARRAY(vA());
                NOGC(match.array);

                for (isize i = 0, j = 0; i < n; ++i, j += 2) {
                        vvP(*match.array, STRING_VIEW(*s, ovec[j], ovec[j + 1] - ovec[j]));
                }

                OKGC(match.array);

                return match;
        }
}

Value
string_length(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.len()", 0);
        return INTEGER(rune_count((u8 const *)ss(*string), sN(*string)));
}

static Value
string_width(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.width()", 0);
        return INTEGER(term_width((u8 const *)ss(*string), sN(*string)));
}

static Value
string_grapheme_count(Ty *ty, Value *string, int argc, Value *kwargs)
{
        u8 const *s = (u8 const *)ss(*string);
        isize size = sN(*string);
        isize offset = 0;
        isize length = 0;
        i32 state = 0;

        while (size > 0) {
                i32 rune;
                isize n = utf8proc_iterate(s + offset, size, &rune);
                if (n <= 0) {
                        size -= 1;
                        offset += 1;
                        continue;
                } else while (n < size) {
                        i32 next;
                        isize m = utf8proc_iterate(s + offset + n, size - n, &next);
                        if (m < 0)
                                break;
                        if (utf8proc_grapheme_break_stateful(rune, next, &state))
                                break;
                        n += m;
                }
                length += 1;
                size -= n;
                offset += n;
        }

        return INTEGER(length);
}

static Value
string_chars(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.chars()", 0);

        u8 const *s = (u8 *)ss(*string);
        isize size = sN(*string);
        isize offset = 0;
        i32 state = 0;

        Array *r = vA();
        NOGC(r);

        while (size > 0) {
                i32 rune;
                isize n = utf8proc_iterate(s + offset, size, &rune);
                if (n < 0) {
                        size -= 1;
                        offset += 1;
                        continue;
                } else if (rune & 0xC0) while (n < size) {
                        i32 next;
                        isize m = utf8proc_iterate(s + offset + n, size - n, &next);
                        if (m < 0)
                                break;
                        if (utf8proc_grapheme_break_stateful(rune, next, &state))
                                break;
                        n += m;
                }
                vAp(r, STRING_VIEW(*string, offset, n));
                size -= n;
                offset += n;
        }

        OKGC(r);

        return ARRAY(r);
}

static Value
string_size(Ty *ty, Value *string, int argc, Value *kwargs)
{
        return INTEGER(sN(*string));
}

static Value
string_bslice(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc == 0 || argc > 2) {
                zP("String.bslice(): expected 1 or 2 arguments but got %d", argc);
        }

        Value start = ARG(0);

        if (start.type != VALUE_INTEGER) {
                zP("String.bslice(): expected Int but got: %s", VSC(&start));
        }

        isize i = start.z;
        isize n;

        if (i < 0) {
                i += sN(*string);
        }

        if (argc == 2) {
                Value len = ARG(1);
                if (len.type != VALUE_INTEGER) {
                        zP("String.bslice(): expected Int but got: %s", VSC(&len));
                }
                n = len.z;
        } else {
                n = (isize)sN(*string) - i;
        }

        i = min(max(i, 0), sN(*string));
        n = min(max(n, 0), sN(*string) - i);

        return STRING_VIEW(*string, i, n);
}

Value
string_slice(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.slice()", 1, 2);

        u8 const *str = (u8 const *)ss(*string);
        isize sz = sN(*string);

        isize i = INT_ARG(0);
        isize n = (argc == 2) ? INT_ARG(1) : sz;

        if ((i < 0) | (n < 0)) {
                isize ncp = rune_count(str, sz);
                if (i < 0) {
                        i += ncp;
                }
                if (n < 0) {
                        n += ncp;
                }
        }

        i = min(max(0, i), sz);
        n = min(max(0, n), sz);

        isize drop = x_x_x(str, sz, i);
        isize take = x_x_x(str + drop, sz - drop, n);

        return STRING_VIEW(*string, drop, take);
}

static Value
string_search_all(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.searchAll()", 1, 2);

        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);

        isize offset;
        if (argc == 1) {
                offset = 0;
        } else {
                offset = INT_ARG(1);
        }

        if (offset < 0) {
                offset += TyStrLen(string);
        }

        isize off = x_x_x(ss(*string), sN(*string), offset);

        Value result = ARRAY(vA());

        if (off < 0 || off > sN(*string)) {
                return result;
        }

        u8 const *s = ss(*string);
        isize bytes = sN(*string);

        isize dist;
        isize plen;
        isize n;

        gP(&result);

        if (pattern.type == VALUE_STRING) {
                plen = TyStrLen(&pattern);
                while (off < bytes) {
                        u8 const *match = mmmm(s + off, bytes - off, ss(pattern), sN(pattern));

                        if (match == NULL) {
                                break;
                        }

                        n = match - (s + off);
                        dist = rune_count(match, n);

                        vAp(result.array, INTEGER(offset + dist));

                        offset += dist + plen;
                        off += n + sN(pattern);
                }
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                usize *ovec = ty_re_ovec();
                isize rc;
                for (;;) {
                        if ((rc = ty_re_match(re, s, bytes, off, 0)) <= 0) {
                                break;
                        }

                        n = ovec[1] - ovec[0];
                        dist = rune_count(s + off, ovec[0] - off);
                        plen = rune_count(s + ovec[0], n);

                        vAp(result.array, INTEGER(offset + dist));

                        if (n <= 0) {
                                i32 cp;
                                n = max(1, utf8proc_iterate(s + ovec[1], bytes - ovec[1], &cp));
                                plen = 1;
                        }

                        off = ovec[0] + n;
                        offset += dist + plen;
                }

                switch (rc) {
                case PCRE2_ERROR_NOMATCH:
                case PCRE2_ERROR_BADOFFSET:
                        break;
                default:
                        ty_re_panic(rc);
                }
        }


        gX();

        return result;
}

static Value
string_bsearch(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.bsearch()", 1, 2);

        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);
        isize offset = (argc == 1) ? 0 : INT_ARG(1);

        if (offset < 0) {
                offset += sN(*string);
        }

        if (offset < 0) {
                zP("String.search(): invalid offset: %"PRIi64, offset);
        }

        if (offset >= sN(*string)) {
                return NIL;
        }

        u8 const *s = ss(*string) + offset;
        isize bytes = (int64_t)sN(*string) - offset;

        isize n;

        if (pattern.type == VALUE_STRING) {
                u8 const *match = mmmm(s, bytes, ss(pattern), sN(pattern));

                if (match == NULL)
                        return NIL;

                n = match - s;
        } else if (pattern.type == VALUE_REGEX) {
                usize *ovec = ty_re_ovec();
                isize rc = ty_re_match(pattern.regex->pcre2, s, bytes, 0, 0);

                if (rc == PCRE2_ERROR_NOMATCH) {
                        return NIL;
                }

                if (rc < 0) {
                        ty_re_panic(rc);
                }

                n = ovec[0];
        } else {
                ARGx(0, VALUE_STRING, VALUE_REGEX);
                UNREACHABLE();
        }

        return INTEGER(offset + n);
}

static Value
string_search(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.search()", 1, 2);

        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);

        isize offset = (argc == 1) ? 0 : INT_ARG(1);

        if (offset < 0) {
                offset += TyStrLen(string);
        }

        if (offset < 0) {
                return NIL;
        }

        isize off = x_x_x(ss(*string), sN(*string), offset);

        if (off >= sN(*string)) {
                return NIL;
        }

        u8 const *s = ss(*string) + off;
        isize bytes = sN(*string) - off;

        isize n;

        if (pattern.type == VALUE_STRING) {
                u8 const *match = mmmm(s, bytes, ss(pattern), sN(pattern));
                n = (match != NULL) ? (match - s) : -1;
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                usize *ovec = ty_re_ovec();

                isize rc = ty_re_match(re, (PCRE2_SPTR)s, bytes, 0, 0);

                if (rc < -1) {
                        ty_re_panic(rc);
                }

                n = (rc != PCRE2_ERROR_NOMATCH) ? ovec[0] : -1;
        }

        return (n != -1) ? INTEGER(offset + rune_count(s, n)) : NIL;
}

static Value
string_searchr(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.searchr()", 1, 2);
        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);
        isize offset = (argc == 1) ? TyStrLen(string) - 1 : INT_ARG(1);

        if (offset < 0) {
                offset += TyStrLen(string);
        }
        if (offset < 0) {
                return NIL;
        }

        isize off = x_x_x(ss(*string), sN(*string), offset);
        if (off > sN(*string)) {
                off = sN(*string);
        }

        u8 const *s = ss(*string);
        isize bytes = off;
        isize n;

        if (pattern.type == VALUE_STRING) {
                u8 const *match = mmmmr(s, bytes, ss(pattern), sN(pattern));
                n = (match != NULL) ? (match - s) : -1;
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                usize *ovec = ty_re_ovec();
                isize last_match = -1;
                isize pos = 0;

                while (pos <= bytes) {
                        isize rc = ty_re_match(re, (PCRE2_SPTR)(s + pos), bytes - pos, 0, 0);
                        if (rc == PCRE2_ERROR_NOMATCH) {
                                break;
                        }
                        if (rc < 0) {
                                ty_re_panic(rc);
                        }
                        last_match = pos + ovec[0];
                        pos = last_match + 1;
                }
                n = last_match;
        }

        return (n != -1) ? INTEGER(rune_count(s, n)) : NIL;
}

static Value
string_bsearchr(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.bsearchr()", 1, 2);
        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);
        isize offset = (argc == 1) ? sN(*string) - 1 : INT_ARG(1);

        if (offset < 0) {
                offset += sN(*string);
        }
        if (offset < 0) {
                zP("String.bsearchr(): invalid offset: %"PRIi64, offset);
        }
        if (offset >= sN(*string)) {
                offset = sN(*string) - 1;
        }

        u8 const *s = ss(*string);
        isize bytes = offset + 1;
        isize n;

        if (pattern.type == VALUE_STRING) {
                u8 const *match = mmmmr(s, bytes, ss(pattern), sN(pattern));
                if (match == NULL) {
                        return NIL;
                }
                n = match - s;
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                usize *ovec = ty_re_ovec();
                isize last_match = -1;
                isize pos = 0;

                while (pos <= bytes) {
                        isize rc = ty_re_match(re, (PCRE2_SPTR)(s + pos), bytes - pos, 0, 0);
                        if (rc == PCRE2_ERROR_NOMATCH) {
                                break;
                        }
                        if (rc < 0) {
                                ty_re_panic(rc);
                        }
                        last_match = pos + ovec[0];
                        pos = last_match + 1;
                }

                if (last_match == -1) {
                        return NIL;
                }

                n = last_match;
        }

        return INTEGER(n);
}

static Value
string_contains(Ty *ty, Value *string, int argc, Value *kwargs)
{
        Value i = string_search(ty, string, argc, kwargs);
        return BOOLEAN(i.type != VALUE_NIL);
}

static Value
string_words(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.words()", 0);

        struct array *a = vA();
        NOGC(a);

        isize i = 0;
        isize len = sN(*string);
        isize n = 0;
        u8 const *s = ss(*string);

        if (len == 0) {
                goto End;
        }

        utf8proc_int32_t cp;


        while (i < len) {
                utf8proc_iterate(s + i, len - i, &cp);
                utf8proc_category_t c = utf8proc_category(cp);
                while (
                        (i < len) && (
                                (cp == '\r')
                             || (cp == '\n')
                             || (c == UTF8PROC_CATEGORY_ZS)
                             || (c == UTF8PROC_CATEGORY_ZL)
                             || (c == UTF8PROC_CATEGORY_ZP)
                        )
                ) {
                        i += n;
                        n = max(utf8proc_iterate(s + i, len - i, &cp), 1);
                        c = utf8proc_category(cp);
                }

                if (i >= len)
                        break;

                Value str = STRING_VIEW(*string, i, 0);

                do {
                        sN(str) += n;
                        i += n;
                        n = max(utf8proc_iterate(s + i, len - i, &cp), 1);
                        c = utf8proc_category(cp);
                } while (
                        (i < len)
                     && (cp != '\r')
                     && (cp != '\n')
                     && (c != UTF8PROC_CATEGORY_ZS)
                     && (c != UTF8PROC_CATEGORY_ZL)
                     && (c != UTF8PROC_CATEGORY_ZP)
                );

                vAp(a, str);
        }
End:
        OKGC(a);

        return ARRAY(a);
}

static Value
string_lines(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.lines()", 0);

        gP(string);

        struct array *a = vA();
        NOGC(a);

        isize i = 0;
        isize len = sN(*string);
        u8 const *s = ss(*string);

        if (len == 0) {
                vAp(a, *string);
                goto End;
        }

        while (i < len) {
                Value str = STRING_VIEW(*string, i, 0);

                while (
                        (i < len)
                     && (s[i] != '\n')
                     && ((s[i] != '\r') || (s[i + 1] != '\n'))
                ) {
                        sN(str) += 1;
                        i += 1;
                }

                vAp(a, str);

                if (i < len) {
                        i += 1 + (s[i] == '\r');
                }
        }
End:
        gX();
        OKGC(a);

        return ARRAY(a);
}

static Value
string_split(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.split()", 1, 2);

        u8 const *s = (u8 const *)ss(*string);
        isize len = sN(*string);

        Value pattern = ARGx(0, VALUE_INTEGER, VALUE_STRING, VALUE_REGEX);

        if (pattern.type == VALUE_INTEGER) {
                isize i = pattern.z;
                isize n = rune_count(s, len);

                if (i < 0)
                        i += n;
                if (i < 0)
                        i = 0;
                if (i > n)
                        i = n;

                isize off = 0;
                while (i --> 0) {
                        i32 cp;
                        isize bytes = utf8proc_iterate((u8 const *)(s + off), len - off, &cp);
                        off += max(bytes, 1);
                }
                Value left = STRING_VIEW(*string, 0, off);
                Value right = STRING_VIEW(*string, off, len - off);

                return PAIR(left, right);
        }

        usize limit = (argc == 2) ? INT_ARG(1) : SIZE_MAX;

        Value result = ARRAY(vA());
        gP(&result);

        if (pattern.type == VALUE_STRING) {
                u8 const *p = ss(pattern);
                isize n = sN(pattern);

                if (n == 0)
                        goto End;

                isize i = 0;
                while (i < len) {
                        Value str = STRING_VIEW(*string, i, 0);

                        if (argc == 2 && result.array->count == ARG(1).z) {
                                sN(str) = len - i;
                                i = len;
                        } else {
                                while (i < len && !is_prefix(s + i, len - i, p, n)) {
                                        sN(str) += 1;
                                        i += 1;
                                }
                        }

                        vAp(result.array, str);

                        i += n;
                }

                if (i == len) {
                        vAp(result.array, STRING_EMPTY);
                }
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                isize len = sN(*string);
                isize start = 0;
                isize pstart = 0;
                usize *ovec = ty_re_ovec();

                while (start < len) {
                        isize n = 0;
                        if (
                                (vN(*result.array) == limit)
                             || ((n = ty_re_match(re, s, len, pstart, 0)) <= 0)
                        ) {
                                ovec[0] = len;
                                ovec[1] = len + 1;
                        }

                        vAp(result.array, STRING_VIEW(*string, start, ovec[0] - start));

                        if (pattern.regex->detailed && n >= 1) {
                                vAp(result.array, mkmatch(ty, string, ovec, n, true));
                        } else {
                                for (isize i = 1; i < n; ++i) {
                                        isize s = ovec[2 * i];
                                        isize e = ovec[2 * i + 1];
                                        vAp(result.array, STRING_VIEW(*string, s, e - s));
                                }
                        }

                        pstart = ovec[1] + (ovec[0] == ovec[1]);
                        start = ovec[1];
                }

                if (start == len) {
                        vAp(result.array, STRING_EMPTY);
                }
        }

End:
        gX();
        return result;
}

static Value
string_count(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.count()", 1);

        Value pattern = ARG(0);
        isize count = 0;

        u8 const *s = ss(*string);
        isize len = sN(*string);

        if (s == NULL) {
                return STRING_EMPTY;
        }

        if (pattern.type == VALUE_STRING) {
                u8 const *m;
                u8 const *p = ss(pattern);
                isize plen = sN(pattern);

                if (plen > 0) while ((m = mmmm(s, len, p, plen)) != NULL) {
                        len -= (m - s + plen);
                        s = m + plen;
                        count += 1;
                }
        } else if (pattern.type == VALUE_REGEX) {
                pcre2_code *re = pattern.regex->pcre2;
                usize *ovec = ty_re_ovec();
                isize off = 0;
                isize rc;

                for (;;) {
                        if ((rc = ty_re_match(re, s, len, off, 0)) <= 0) {
                                break;
                        }

                        if (rc <= 0) { break; }

                        count += 1;
                        off = ovec[1];
                }
        } else {
                ARGx(0, VALUE_STRING, VALUE_REGEX);
        }

        return INTEGER(count);
}

static Value
string_comb(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.comb()", 1);

        Value pattern = ARG(0);
        u8 const *str = ss(*string);

        if (str == NULL) {
                return STRING_EMPTY;
        }

        vec(u8) scratch = {0};
        bool any = false;

        SCRATCH_SAVE();

        switch (pattern.type) {
        case VALUE_STRING:
        {
                u8 const *p = (u8 const *)ss(pattern);

                isize len = sN(*string);
                isize plen = sN(pattern);
                u8 const *match;

                if (plen == 0) {
                        break;
                }

                while ((match = mmmm(str, len, p, plen)) != NULL) {
                        svPn(scratch, str, match - str);
                        len -= (match - str + plen);
                        str = match + plen;
                        any = true;
                }

                if (any) {
                        svPn(scratch, str, len);
                }

                break;
        }

        case VALUE_REGEX:
        {
                pcre2_code *re = pattern.regex->pcre2;
                isize len = sN(*string);
                isize start = 0;
                usize *ovec = ty_re_ovec();
                i32 sz;
                i32 rc;

                while ((rc = ty_re_match(re, str, len, start, 0)) > 0) {
                        svPn(scratch, str + start, ovec[0] - start);
                        if (ovec[0] == ovec[1]) {
                                if (ovec[0] >= len) {
                                        rc = PCRE2_ERROR_NOMATCH;
                                        break;
                                }
                                sz = u8_rune_sz(str + ovec[0]);
                                svPn(scratch, str + ovec[0], sz);
                                start = ovec[0] + sz;
                        } else {
                                start = ovec[1];
                        }
                        any = true;
                }

                if (rc != PCRE2_ERROR_NOMATCH) {
                        SCRATCH_RESTORE();
                        ty_re_panic(rc);
                }

                if (any) {
                        svPn(scratch, str + start, len - start);
                }

                break;
        }

        default:
                ARGx(0, VALUE_STRING, VALUE_REGEX);
        }

        Value ret = !any               ? *string
                  : (vN(scratch) == 0) ? STRING_EMPTY
                  :                      vSs(vv(scratch), vN(scratch))
                  ;

        SCRATCH_RESTORE();

        return ret;
}

static Value
string_try_comb(Ty *ty, Value *string, int argc, Value *kwargs)
{
        Value str = string_comb(ty, string, argc, kwargs);
        return (ss(str) != ss(*string)) ? str : NIL;
}

static Value
string_repeat(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("String.repeat(): expected 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER || ARG(0).z < 0) {
                zP(
                        "String.repeat(): argument is not a non-negative integer: %s",
                        VSC(&ARG(0))
                );
        }

        char *s = value_string_alloc(ty, sN(*string) * ARG(0).z);
        isize off = 0;

        for (isize i = 0; i < ARG(0).z; ++i) {
                memcpy(s + off, ss(*string), sN(*string));
                off += sN(*string);
        }

        return STRING(s, off);
}

static Value
string_replace(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.replace()", 2);

        vec(u8) chars = {0};
        Value pattern = ARGx(0, VALUE_REGEX, VALUE_STRING);
        Value replacement = ARG(1);

        u8 const *s = ss(*string);

        if (pattern.type == VALUE_STRING) {
                vmP(&replacement);
                replacement = builtin_str(ty, 1, NULL);
                vmX();

                if (replacement.type != VALUE_STRING) {
                        zP(
                                "String.replace(): non-string replacement passed "
                                "with a string pattern: %s",
                                VSC(&replacement)
                        );
                }

                u8 const *p = ss(pattern);
                u8 const *r = ss(replacement);

                isize len = sN(*string);
                isize plen = sN(pattern);
                u8 const *m;

                while ((m = mmmm(s, len, p, plen)) != NULL) {
                        vvPn(chars, s, m - s);

                        vvPn(chars, r, sN(replacement));

                        len -= (m - s + plen);
                        s = m + plen;
                }

                vvPn(chars, s, len);
        } else if (replacement.type == VALUE_STRING) {
                pcre2_code *re = pattern.regex->pcre2;
                isize len = sN(*string);
                usize *ovec = ty_re_ovec();
                isize start = 0;

                for (;;) {
                        isize n = pcre2_match(
                                re,
                                (PCRE2_SPTR)s,
                                len,
                                start,
                                0,
                                ty->pcre2.match,
                                ty->pcre2.ctx
                        );
                        if (n <= 0) {
                                break;
                        }
                        if (ovec[1] == start) {
                                vvPn(chars, ss(replacement), sN(replacement));
                                vvP(chars, s[start]);
                                start = ovec[1] + 1;
                        } else {
                                vvPn(chars, s + start, ovec[0] - start);
                                vvPn(chars, ss(replacement), sN(replacement));
                                start = ovec[1];
                        }
                }

                if (start < len) {
                        vvPn(chars, s + start, len - start);
                }
        } else if (CALLABLE(replacement)) {
                pcre2_code *re = pattern.regex->pcre2;
                isize len = sN(*string);
                usize *ovec = ty_re_ovec();
                isize start = 0;
                isize rc;

                while ((rc = ty_re_match(re, s, len, start, 0)) > 0) {
                        vvPn(chars, s + start, ovec[0] - start);

                        Value match = {0};

                        gP(&match);

                        if (rc == 1) {
                                match = STRING_VIEW(*string, ovec[0], ovec[1] - ovec[0]);
                        } else {
                                match = ARRAY(vA());
                                for (isize i = 0, j = 0; i < rc; ++i, j += 2) {
                                        vvP(
                                                *match.array,
                                                STRING_VIEW(
                                                        *string,
                                                        ovec[j],
                                                        ovec[j + 1] - ovec[j]
                                                )
                                        );
                                }
                        }

                        start = ovec[1];

                        Value substitute = vm_eval_function(ty, &replacement, &match, NULL);
                        vmP(&substitute);
                        substitute = builtin_str(ty, 1, NULL);
                        vmX();

                        gX();

                        uvPn(chars, ss(substitute), sN(substitute));
                }

                vvPn(chars, s + start, len - start);
        } else {
                zP("String.replace(): invalid replacement: %s", VSC(&replacement));
        }

        Value r = vSs(chars.items, chars.count);

        mF(chars.items);

        return r;
}

static Value
string_is_match(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.match?()", 1);

        Value pattern = ARGx(0, VALUE_REGEX);

        isize rc = pcre2_match(
                pattern.regex->pcre2,
                (PCRE2_SPTR)ss(*string),
                sN(*string),
                0,
                0,
                ty->pcre2.match,
                ty->pcre2.ctx
        );

        if (rc < -2) {
                ty_re_panic(rc);
        }

        return BOOLEAN(rc > -1);
}

Value
string_match(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.match()", 1);

        Value pattern = ARGx(0, VALUE_REGEX);
        usize *ovec = ty_re_ovec();

        isize rc = pcre2_match(
                pattern.regex->pcre2,
                (PCRE2_SPTR)ss(*string),
                sN(*string),
                0,
                0,
                ty->pcre2.match,
                ty->pcre2.ctx
        );

        if (rc < -2) {
                ty_re_panic(rc);
        }

        if (rc < 0) {
                return NIL;
        }

        return mkmatch(ty, string, ovec, rc, pattern.regex->detailed);
}

static Value
string_matches(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.matches()", 1);

        Value pattern = ARGx(0, VALUE_REGEX);

        Value result = ARRAY(vA());
        gP(&result);

        usize *ovec = ty_re_ovec();
        isize offset = 0;
        isize rc;

        for (;;) {
                rc = pcre2_match(
                        pattern.regex->pcre2,
                        (PCRE2_SPTR)ss(*string),
                        sN(*string),
                        offset,
                        0,
                        ty->pcre2.match,
                        ty->pcre2.ctx
                );

                if (rc <= 0) { break; }

                vAp(result.array, NIL);
                *vvL(*result.array) = mkmatch(ty, string, ovec, rc, pattern.regex->detailed);

                offset = ovec[1];
        }

        switch (rc) {
        case PCRE2_ERROR_NOMATCH:
        case PCRE2_ERROR_BADOFFSET:
                break;
        default:
                ty_re_panic(rc);
        }

        gX();

        return result;
}

static Value
string_byte(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.byte()", 1);

        imax i = INT_ARG(0);

        if (i < 0) {
                i += sN(*string);
        }

        if (i < 0 || i >= sN(*string)) {
                return NIL; /* TODO: maybe panic */
        }

        return INTEGER((unsigned char)ss(*string)[i]);
}

Value
string_char(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.char()", 1);

        imax i = INT_ARG(0);

        if (i < 0) {
                i += string_length(ty, string, 0, NULL).z;
        }

        i32 cp;
        isize j = i;
        isize offset = 0;
        isize n = utf8proc_iterate((u8 const *)ss(*string), sN(*string), &cp);

        while (offset < sN(*string) && n > 0 && j --> 0) {
                offset += max(1, n);
                n = utf8proc_iterate((u8 const *)ss(*string) + offset, sN(*string), &cp);
        }

        if (offset == sN(*string))
                return NIL;

        return STRING_VIEW(*string, offset, n);
}

static Value
string_bytes(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("sN(*String)()", 0);

        Value result = ARRAY(vA());
        NOGC(result.array);

        for (isize i = 0; i < sN(*string); ++i) {
                vAp(result.array, INTEGER((unsigned char)ss(*string)[i]));
        }

        OKGC(result.array);

        return result;
}

static Value
string_lower(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.lower()", 0);

        utf8proc_int32_t c;
        u8 *s = (u8 *) ss(*string);
        isize len = sN(*string);

        isize outlen = 0;
        char *result = value_string_alloc(ty, 4 * sN(*string));

        while (len > 0) {
                isize n = max(1, utf8proc_iterate(s, len, &c));
                s += n;
                len -= n;
                c = utf8proc_tolower(c);
                outlen += utf8proc_encode_char(c, (u8 *)result + outlen);
        }

        return STRING(result, outlen);
}

static Value
string_upper(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.upper()", 0);

        utf8proc_int32_t c;
        u8 *s = (u8 *) ss(*string);
        isize len = sN(*string);

        isize outlen = 0;
        u8 *result = value_string_alloc(ty, 4 * sN(*string));

        while (len > 0) {
                isize n = max(1, utf8proc_iterate(s, len, &c));
                s += n;
                len -= n;
                c = utf8proc_toupper(c);
                outlen += utf8proc_encode_char(c, (u8 *)result + outlen);
        }

        return STRING(result, outlen);
}

static Value
string_pad_left(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.lpad()", 1, 2);

        isize width = INT_ARG(0);

        isize string_len = TyStrLen(string);
        if (string_len >= width) {
                return *string;
        }

        u8 const *pad;
        isize pad_bytes;
        isize pad_len;

        if (argc == 1) {
                pad = (u8 const *)" ";
                pad_bytes = pad_len = 1;
        } else {
                Value vPad = ARGx(1, VALUE_STRING);
                pad = ss(vPad);
                pad_bytes = sN(vPad);
                pad_len = TyStrLen(&vPad);
        }

        isize n = (width - string_len) / pad_len + 1;
        u8 *result = value_string_alloc(ty, sN(*string) + pad_bytes * n);

        isize current = 0;
        isize bytes = 0;
        while (current + pad_len <= width - string_len) {
                memcpy(result + bytes, pad, pad_bytes);
                current += pad_len;
                bytes += pad_bytes;
        }

        if (current != width - string_len) {
                isize partial = x_x_x(pad, pad_bytes, width - string_len - current);
                memcpy(result + bytes, pad, partial);
                bytes += partial;
        }

        memcpy(result + bytes, ss(*string), sN(*string));
        bytes += sN(*string);

        return STRING(result, bytes);
}

static Value
string_pad_right(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.rpad()", 1, 2);

        isize width = INT_ARG(0);
        isize current = TyStrLen(string);

        if (current >= width) {
                return *string;
        }

        u8 const *pad;
        isize pad_bytes;
        isize pad_len;

        if (argc == 1) {
                pad = (u8 const *)" ";
                pad_bytes = pad_len = 1;
        } else {
                Value vPad = ARGx(1, VALUE_STRING);
                pad = ss(vPad);
                pad_bytes = sN(vPad);
                pad_len = TyStrLen(&vPad);
        }

        isize n = (width - current) / pad_len + 1;
        u8 *result = value_string_alloc(ty, sN(*string) + pad_bytes * n);
        isize bytes = sN(*string);
        memcpy(result, ss(*string), bytes);

        while (current + pad_len <= width) {
                memcpy(result + bytes, pad, pad_bytes);
                current += pad_len;
                bytes += pad_bytes;
        }

        if (current != width) {
                isize partial = x_x_x(pad, pad_bytes, width - current);
                memcpy(result + bytes, pad, partial);
                bytes += partial;
        }

        return STRING(result, bytes);
}

static Value
string_cstr(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("String.cstr() expects 0 arguments but got %d", argc);
        }

        return vSzs(ss(*string), sN(*string));
}

static Value
string_ptr(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("String.ptr() expects 0 arguments but got %d", argc);
        }

        return PTR((void *)ss(*string));
}

static Value
string_clone(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("String.clone(): expected 0 arguments but got %d", argc);
        }

        return vSs(ss(*string), sN(*string));
}

DEFINE_METHOD_TABLE(
        { .name = "bsearch",   .func = string_bsearch          },
        { .name = "bsearchr",  .func = string_bsearchr         },
        { .name = "bslice",    .func = string_bslice           },
        { .name = "byte",      .func = string_byte             },
        { .name = "bytes",     .func = string_bytes            },
        { .name = "char",      .func = string_char             },
        { .name = "chars",     .func = string_chars            },
        { .name = "clone",     .func = string_clone            },
        { .name = "comb",      .func = string_comb             },
        { .name = "comb?",     .func = string_try_comb         },
        { .name = "contains?", .func = string_contains         },
        { .name = "count",     .func = string_count            },
        { .name = "cstr",      .func = string_cstr             },
        { .name = "charCount", .func = string_grapheme_count   },
        { .name = "len",       .func = string_length           },
        { .name = "lines",     .func = string_lines            },
        { .name = "lower",     .func = string_lower            },
        { .name = "match",     .func = string_match            },
        { .name = "match?",    .func = string_is_match         },
        { .name = "matches",   .func = string_matches          },
        { .name = "lpad",      .func = string_pad_left         },
        { .name = "rpad",      .func = string_pad_right        },
        { .name = "pad",       .func = string_pad_right        },
        { .name = "ptr",       .func = string_ptr              },
        { .name = "repeat",    .func = string_repeat           },
        { .name = "replace",   .func = string_replace          },
        { .name = "scan",      .func = string_matches          },
        { .name = "search",    .func = string_search           },
        { .name = "searchr",   .func = string_searchr          },
        { .name = "searchAll", .func = string_search_all       },
        { .name = "size",      .func = string_size             },
        { .name = "slice",     .func = string_slice            },
        { .name = "split",     .func = string_split            },
        { .name = "sub",       .func = string_replace          },
        { .name = "upper",     .func = string_upper            },
        { .name = "width",     .func = string_width            },
        { .name = "words",     .func = string_words            },
);

DEFINE_METHOD_LOOKUP(string)
DEFINE_METHOD_TABLE_BUILDER(string)
DEFINE_METHOD_COMPLETER(string)

/* vim: set sw=8 sts=8 expandtab: */
