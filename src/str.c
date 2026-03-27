#include <string.h>

#include <utf8proc.h>
#include <pcre2.h>

#include "dict.h"
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
        return INTEGER(rune_count(ss(*string), sN(*string)));
}

static Value
string_width(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.width()", 0);
        return INTEGER(term_width(ss(*string), sN(*string)));
}

static Value
string_grapheme_count(Ty *ty, Value *string, int argc, Value *kwargs)
{
        u8 const *s = ss(*string);
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

        u8 const *str = ss(*string);
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
                                n = u8_rune_sz(s + ovec[1]);
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

        u8 const *s = ss(*string);
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
                        isize bytes = utf8proc_iterate((s + off), len - off, &cp);
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

                        if (off >= len) {
                                break;
                        }

                        off = ovec[1];
                        if (off <= ovec[0]) {
                                off += u8_rune_sz(s + off);
                        }

                        count += 1;

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
                u8 const *p = ss(pattern);

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

                if (plen == 0) {
                        return *string;
                }

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
                isize sz;

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
                        vvPn(chars, s + start, ovec[0] - start);
                        vvPn(chars, ss(replacement), sN(replacement));
                        if (ovec[0] >= len) {
                                start = len;
                                break;
                        } else if (ovec[0] == ovec[1]) {
                                sz = u8_rune_sz(s + ovec[1]);
                                uvPn(chars, s + ovec[1], sz);
                                start = ovec[1] + sz;
                        } else {
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

                Value match;
                Value subst;

                while (
                        (start < len)
                     && (rc = ty_re_match(re, s, len, start, 0)) > 0
                ) {
                        // Need to grab these now in case the callback clobbers ovec
                        isize i = ovec[0];
                        isize j = ovec[1];

                        vvPn(chars, s + start, i - start);

                        match = mkmatch(ty, string, ovec, rc, pattern.regex->detailed);
                        gP(&match);
                        subst = vm_eval_function(ty, &replacement, &match, NULL);
                        vmP(&subst);
                        subst = builtin_str(ty, 1, NULL);
                        vmX();
                        gX();

                        uvPn(chars, ss(subst), sN(subst));

                        if (i == j && i < len) {
                                j += u8_rune_sz(s + i);
                                uvPn(chars, s + i, j - i);
                        }

                        start = j;
                }

                vvPn(chars, s + start, len - start);
        } else {
                zP("String.replace(): invalid replacement: %s", VSC(&replacement));
        }

        Value r = vSs(vv(chars), vN(chars));

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
                v_L(*result.array) = mkmatch(ty, string, ovec, rc, pattern.regex->detailed);

                if (ovec[0] == ovec[1]) {
                        if (ovec[0] >= sN(*string)) {
                                rc = PCRE2_ERROR_NOMATCH;
                                break;
                        }
                        offset = ovec[1] + u8_rune_sz(ss(*string) + ovec[1]);
                } else {
                        offset = ovec[1];
                }
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
        isize n = utf8proc_iterate(ss(*string), sN(*string), &cp);

        while (offset < sN(*string) && n > 0 && j --> 0) {
                offset += max(1, n);
                n = utf8proc_iterate(ss(*string) + offset, sN(*string), &cp);
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

enum {
        US_BOLD, US_ITALIC, US_DIM, US_REVERSE,
        US_UL, US_FG, US_BGBR, US_BG, US_UC, US_LNK, US_NA
};

typedef struct {
        u8      a[US_NA];
        u8      rgb[3][3];
        u8 const *link;
        isize   llen;
        u16     ord[US_NA];
        u16     nxt;
} UnchalkSt;

#define SN(lit) lit, (isize)(sizeof (lit) - 1)
#define svLIT(v, lit) svPn(v, lit, (isize)(sizeof (lit) - 1))

#define US_SET(st, ai, val) do {                \
        if ((st)->a[ai] == 0 && (val) != 0) {  \
                (st)->ord[ai] = (st)->nxt++;    \
        }                                       \
        (st)->a[ai] = (val);                    \
} while (0)

typedef struct { char const *s; isize n; } StrLen;

static StrLen us_fg_nm[] = {
        {SN("red")},     {SN("green")},   {SN("yellow")},
        {SN("blue")},    {SN("magenta")}, {SN("cyan")},
        {SN("white")}
};

static StrLen us_bg_nm[] = {
        {SN("bg-red")},  {SN("bg-green")},   {SN("bg-yellow")},
        {SN("bg-blue")}, {SN("bg-magenta")}, {SN("bg-cyan")},
        {SN("bg-white")}
};

static StrLen us_off_nm[] = {
        [US_BOLD]    = {SN("bold")},
        [US_ITALIC]  = {SN("italic")},
        [US_DIM]     = {SN("dim")},
        [US_REVERSE] = {SN("reverse")},
        [US_UL]      = {SN("underline")},
        [US_FG]      = {SN("fg")},
        [US_BGBR]    = {SN("bg-bright")},
        [US_BG]      = {SN("bg")},
        [US_UC]      = {SN("uc")},
        [US_LNK]     = {SN("link")}
};

static void
us_reset(UnchalkSt *st)
{
        memset(st, 0, sizeof *st);

        st->a[US_BOLD]    = 1;  st->ord[US_BOLD]    = 0;
        st->a[US_ITALIC]  = 1;  st->ord[US_ITALIC]  = 1;
        st->a[US_UL]      = 1;  st->ord[US_UL]      = 2;
        st->a[US_DIM]     = 1;  st->ord[US_DIM]     = 3;
        st->a[US_REVERSE] = 1;  st->ord[US_REVERSE] = 4;
        st->a[US_FG]      = 1;  st->ord[US_FG]      = 5;
        st->a[US_BG]      = 1;  st->ord[US_BG]      = 6;
        st->a[US_UC]      = 1;  st->ord[US_UC]      = 7;

        st->nxt = 8;
}

static void
us_parse_sgr(UnchalkSt *st, u8 const *p, isize n)
{
        isize i = 0;

        while (i < n) {
                while (i < n && p[i] == ';') {
                        i += 1;
                }

                if (i >= n) {
                        break;
                }

                int v = 0;
                isize start = i;

                while (i < n && p[i] >= '0' && p[i] <= '9') {
                        v = v * 10 + (p[i++] - '0');
                }

                if (i == start) {
                        i += 1;
                        continue;
                }

                switch (v) {
                case 0:
                        us_reset(st);
                        break;

                case 1:
                        US_SET(st, US_BOLD, 2);
                        break;

                case 3:
                        US_SET(st, US_ITALIC, 2);
                        break;

                case 4:
                        if (i < n && p[i] == ':') {
                                i += 1;
                                int sub = 0;
                                while (i < n && p[i] >= '0' && p[i] <= '9') {
                                        sub = sub * 10 + (p[i++] - '0');
                                }
                                if (sub <= 5) {
                                        US_SET(st, US_UL, sub ? sub + 1 : 1);
                                }
                        } else {
                                US_SET(st, US_UL, 2);
                        }
                        break;

                case 7:
                        US_SET(st, US_REVERSE, 2);
                        break;

                case 22: US_SET(st, US_BOLD,    1); break;
                case 23: US_SET(st, US_ITALIC,  1); break;
                case 24: US_SET(st, US_UL,      1); break;
                case 27: US_SET(st, US_REVERSE, 1); break;
                case 39: US_SET(st, US_FG,      1); break;
                case 49: US_SET(st, US_BG,      1); break;
                case 59: US_SET(st, US_UC,      1); break;

                case 38: case 48: case 58:
                {
                        if (i >= n || (p[i] != ';' && p[i] != ':')) {
                                break;
                        }

                        i += 1;

                        int ct = 0;
                        while (i < n && p[i] >= '0' && p[i] <= '9') {
                                ct = ct * 10 + (p[i++] - '0');
                        }

                        if (ct != 2) {
                                break;
                        }

                        int c[3] = {0};
                        for (int j = 0; j < 3; j++) {
                                if (i < n && (p[i] == ';' || p[i] == ':')) {
                                        i += 1;
                                }
                                while (i < n && p[i] >= '0' && p[i] <= '9') {
                                        c[j] = c[j] * 10 + (p[i++] - '0');
                                }
                        }

                        int ai = (v == 38) ? US_FG
                               : (v == 48) ? US_BG
                               :             US_UC;
                        int ri = (ai == US_FG) ? 0
                               : (ai == US_BG) ? 1
                               :                  2;

                        US_SET(st, ai, 9);

                        st->rgb[ri][0] = c[0];
                        st->rgb[ri][1] = c[1];
                        st->rgb[ri][2] = c[2];

                        break;
                }
                default:
                        if (v >= 31 && v <= 37) {
                                US_SET(st, US_FG, v - 30 + 1);
                        } else if (v >= 41 && v <= 47) {
                                US_SET(st, US_BG, v - 40 + 1);
                        } else if (v >= 91 && v <= 97) {
                                US_SET(st, US_FG, v - 90 + 1);
                        } else if (v >= 101 && v <= 107) {
                                US_SET(st, US_BGBR, 2);
                                US_SET(st, US_BG, v - 100 + 1);
                        }
                        break;
                }
        }
}

static void
us_emit_on(Ty *ty, byte_vector *out, UnchalkSt const *st, int ai)
{
        u8 v = st->a[ai];

        switch (ai) {
        case US_BOLD:
                svLIT(*out, "b");
                break;

        case US_ITALIC:
                svLIT(*out, "i");
                break;

        case US_DIM:
                svLIT(*out, "dim");
                break;

        case US_REVERSE:
                svLIT(*out, "reverse");
                break;

        case US_BGBR:
                svLIT(*out, "bg-bright");
                break;

        case US_UL:
                switch (v) {
                case 2: svLIT(*out, "u");  break;
                case 3: svLIT(*out, "uu"); break;
                case 4: svLIT(*out, "u~"); break;
                case 5: svLIT(*out, "u."); break;
                case 6: svLIT(*out, "u-"); break;
                }
                break;

        case US_FG:
                if (v >= 2 && v <= 8) {
                        StrLen nm = us_fg_nm[v - 2];
                        svPn(*out, nm.s, nm.n);
                } else {
                        sxdf(out, "#%02x%02x%02x",
                             st->rgb[0][0],
                             st->rgb[0][1],
                             st->rgb[0][2]);
                }
                break;

        case US_BG:
                if (v >= 2 && v <= 8) {
                        StrLen nm = us_bg_nm[v - 2];
                        svPn(*out, nm.s, nm.n);
                } else {
                        sxdf(out, "bg-#%02x%02x%02x",
                             st->rgb[1][0],
                             st->rgb[1][1],
                             st->rgb[1][2]);
                }
                break;

        case US_UC:
                sxdf(out, "uc-#%02x%02x%02x",
                     st->rgb[2][0],
                     st->rgb[2][1],
                     st->rgb[2][2]);
                break;

        case US_LNK:
                svLIT(*out, "link=");
                svPn(*out, st->link, st->llen);
                break;
        }
}

static void
us_emit_trans(Ty *ty, byte_vector *out,
              UnchalkSt const *a, UnchalkSt const *b)
{
        typedef struct { u8 ai; u16 ord; } Item;

        Item on[US_NA], off[US_NA];
        int non  = 0;
        int noff = 0;

        for (int ai = 0; ai < US_NA; ++ai) {
                if (ai == US_LNK) {
                        continue;
                }

                u8 ov = a->a[ai];
                u8 nv = b->a[ai];

                if (nv == 0) {
                        continue;
                }

                bool eq = (ov == nv);

                if (
                           eq
                        && nv == 9
                        && (ai == US_FG || ai == US_BG || ai == US_UC)
                ) {
                        int ri = (ai == US_FG) ? 0
                               : (ai == US_BG) ? 1
                               :                  2;
                        eq = memcmp(a->rgb[ri], b->rgb[ri], 3) == 0;
                }

                if (eq) {
                        continue;
                }

                if (nv == 1) {
                        if (ov != 0) {
                                off[noff++] = (Item){
                                        .ai  = ai,
                                        .ord = b->ord[ai]
                                };
                        }
                } else {
                        on[non++] = (Item){
                                .ai  = ai,
                                .ord = b->ord[ai]
                        };
                }
        }

        if (a->a[US_LNK] && !b->a[US_LNK]) {
                off[noff++] = (Item){ .ai = US_LNK, .ord = 0xFFFF };
        }

        if (b->a[US_LNK]) {
                bool same = a->a[US_LNK]
                         && a->llen == b->llen
                         && a->link != NULL
                         && memcmp(a->link, b->link, b->llen) == 0;
                if (!same) {
                        on[non++] = (Item){
                                .ai  = US_LNK,
                                .ord = b->ord[US_LNK]
                        };
                }
        }

        for (int i = 1; i < noff; ++i) {
                Item t = off[i];
                int j = i;
                while (j > 0 && off[j - 1].ord > t.ord) {
                        off[j] = off[j - 1];
                        j -= 1;
                }
                off[j] = t;
        }

        for (int i = 1; i < non; ++i) {
                Item t = on[i];
                int j = i;
                while (j > 0 && on[j - 1].ord > t.ord) {
                        on[j] = on[j - 1];
                        j -= 1;
                }
                on[j] = t;
        }

        if (noff > 0) {
                svLIT(*out, "[/");
                for (int i = 0; i < noff; ++i) {
                        if (i > 0) {
                                svLIT(*out, " ");
                        }
                        StrLen nm = us_off_nm[off[i].ai];
                        svPn(*out, nm.s, nm.n);
                }
                svLIT(*out, "]");
        }

        if (non > 0) {
                svLIT(*out, "[");
                for (int i = 0; i < non; ++i) {
                        if (i > 0) {
                                svLIT(*out, " ");
                        }
                        us_emit_on(ty, out, b, on[i].ai);
                }
                svLIT(*out, "]");
        }
}

static void
us_emit_esc(Ty *ty, byte_vector *out, u8 const *s, isize n)
{
        for (isize i = 0; i < n; ++i) {
                if (s[i] == '[' || s[i] == '\\') {
                        svLIT(*out, "\\");
                }
                svPn(*out, s + i, 1);
        }
}

static Value
string_unchalk(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.unchalk()", 0);

        u8 const *s = ss(*string);
        isize len   = sN(*string);

        SCRATCH_SAVE();

        UnchalkSt sty = {0};
        UnchalkSt ren = {0};

        byte_vector out = {0};

        isize pos = 0;

        for (;;) {
                isize esc     = pos;
                isize sgr_end = -1;
                isize osc_end = -1;

                while (esc < len) {
                        if (s[esc] != '\x1b' || esc + 1 >= len) {
                                esc += 1;
                                continue;
                        }

                        if (s[esc + 1] == '[') {
                                isize e = esc + 2;
                                while (e < len && s[e] != 'm') {
                                        e += 1;
                                }
                                if (e < len) {
                                        sgr_end = e;
                                        break;
                                }
                        }

                        if (
                                   esc + 4 < len
                                && s[esc + 1] == ']'
                                && s[esc + 2] == '8'
                                && s[esc + 3] == ';'
                                && s[esc + 4] == ';'
                        ) {
                                isize e = esc + 5;
                                while (
                                           e + 1 < len
                                        && !(s[e] == '\x1b' && s[e + 1] == '\\')
                                ) {
                                        e += 1;
                                }
                                if (e + 1 < len) {
                                        osc_end = e;
                                        break;
                                }
                        }

                        esc += 1;
                }

                us_emit_trans(ty, &out, &ren, &sty);
                us_emit_esc(ty, &out, s + pos, esc - pos);
                ren = sty;

                if (esc >= len) {
                        break;
                }

                if (sgr_end >= 0) {
                        us_parse_sgr(
                                &sty,
                                s + esc + 2,
                                sgr_end - esc - 2
                        );
                        pos = sgr_end + 1;
                } else {
                        isize url_start = esc + 5;
                        isize url_len   = osc_end - url_start;
                        if (url_len == 0) {
                                sty.a[US_LNK] = 0;
                                sty.link      = NULL;
                                sty.llen      = 0;
                        } else {
                                US_SET(&sty, US_LNK, 1);
                                sty.link = s + url_start;
                                sty.llen = url_len;
                        }
                        pos = osc_end + 2;
                }
        }

        UnchalkSt empty = {0};
        us_emit_trans(ty, &out, &ren, &empty);

        Value result = (vN(out) > 0)
                     ? vSs(vv(out), vN(out))
                     : STRING_EMPTY;

        SCRATCH_RESTORE();

        return result;
}

#undef US_SET

static Value
string_plain(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.plain()", 0);

        u8 const *s = ss(*string);
        isize     len = sN(*string);

        SCRATCH_SAVE();

        byte_vector out = {0};
        isize pos = 0;

        for (;;) {
                isize ts = pos;

                while (pos < len) {
                        if (
                                   s[pos] == '\\'
                                && pos + 1 < len
                                && (s[pos + 1] == '\\' || s[pos + 1] == '[')
                        ) {
                                break;
                        }
                        if (s[pos] == '[') {
                                break;
                        }
                        pos += 1;
                }

                for (isize i = ts; i < pos; ++i) {
                        if (s[i] == '\\' && i + 1 < pos) {
                                i += 1;
                        }
                        svPn(out, s + i, 1);
                }

                if (pos >= len) {
                        break;
                }

                if (s[pos] == '\\') {
                        svPn(out, s + pos + 1, 1);
                        pos += 2;
                        continue;
                }

                pos += 1;

                while (pos < len && s[pos] != ']') {
                        pos += 1;
                }

                if (pos < len) {
                        pos += 1;
                }
        }

        Value result = (vN(out) > 0)
                     ? vSs(vv(out), vN(out))
                     : STRING_EMPTY;

        SCRATCH_RESTORE();

        return result;
}

typedef struct {
        i8      bold, italic, dim, reverse;
        i8      bright, bg_bright;
        u8      fg_n, bg_n, uc_n, ul_n;
        u8      fg[5], bg[5], uc[5], ul[2];
        u8 const *link;
        isize   link_len;
} CkSty;

inline static bool
ck_arr_eq(u8 const *a, int an, u8 const *b, int bn)
{
        return (an == bn) && (an == 0 || memcmp(a, b, an) == 0);
}

inline static void
ck_merge(CkSty *d, CkSty const *s)
{
        if (s->bold)      { d->bold      = s->bold;      }
        if (s->italic)    { d->italic    = s->italic;    }
        if (s->dim)       { d->dim       = s->dim;       }
        if (s->reverse)   { d->reverse   = s->reverse;   }
        if (s->bright)    { d->bright    = s->bright;    }
        if (s->bg_bright) { d->bg_bright = s->bg_bright; }

        if (s->fg_n) { d->fg_n = s->fg_n; memcpy(d->fg, s->fg, s->fg_n); }
        if (s->bg_n) { d->bg_n = s->bg_n; memcpy(d->bg, s->bg, s->bg_n); }
        if (s->uc_n) { d->uc_n = s->uc_n; memcpy(d->uc, s->uc, s->uc_n); }
        if (s->ul_n) { d->ul_n = s->ul_n; memcpy(d->ul, s->ul, s->ul_n); }

        if (s->link) {
                d->link     = s->link;
                d->link_len = s->link_len;
        }
}

inline static void
ck_bright_fix(CkSty *s)
{
        if (
                   s->bright
                && s->fg_n == 1
                && s->fg[0] >= 30
                && s->fg[0] <= 37
        ) {
                s->fg[0] += 60;
        }

        if (
                   s->bg_bright
                && s->bg_n == 1
                && s->bg[0] >= 40
                && s->bg[0] <= 47
        ) {
                s->bg[0] += 60;
        }

        s->bright    = 0;
        s->bg_bright = 0;
}

static void
ck_emit_sgr(Ty *ty, byte_vector *out, u8 const *arr, int n, char sep)
{
        svLIT(*out, "\x1b[");
        for (int i = 0; i < n; ++i) {
                if (i > 0) {
                        svPn(*out, &sep, 1);
                }
                sxdf(out, "%d", (int)arr[i]);
        }
        svLIT(*out, "m");
}

static void
ck_emit_code(Ty *ty, byte_vector *out, int code)
{
        sxdf(out, "\x1b[%dm", code);
}

static void
ck_trans(Ty *ty, byte_vector *out,
         CkSty const *a, CkSty const *b)
{
        CkSty ca = *a;
        CkSty cb = *b;

        ck_bright_fix(&ca);
        ck_bright_fix(&cb);

        if (cb.fg_n && !ck_arr_eq(ca.fg, ca.fg_n, cb.fg, cb.fg_n)) {
                ck_emit_sgr(ty, out, cb.fg, cb.fg_n, ';');
        }
        if (cb.bg_n && !ck_arr_eq(ca.bg, ca.bg_n, cb.bg, cb.bg_n)) {
                ck_emit_sgr(ty, out, cb.bg, cb.bg_n, ';');
        }
        if (cb.uc_n && !ck_arr_eq(ca.uc, ca.uc_n, cb.uc, cb.uc_n)) {
                ck_emit_sgr(ty, out, cb.uc, cb.uc_n, ';');
        }
        if (cb.ul_n && !ck_arr_eq(ca.ul, ca.ul_n, cb.ul, cb.ul_n)) {
                ck_emit_sgr(ty, out, cb.ul, cb.ul_n, ':');
        }
        if (cb.bold && ca.bold != cb.bold) {
                ck_emit_code(ty, out, 1);
        }
        if (cb.italic && ca.italic != cb.italic) {
                ck_emit_code(ty, out, 3);
        }
        if (cb.reverse && ca.reverse != cb.reverse) {
                ck_emit_code(ty, out, 7);
        }

        if (ca.uc_n    && !cb.uc_n)    { ck_emit_code(ty, out, 59); }
        if (ca.bg_n    && !cb.bg_n)    { ck_emit_code(ty, out, 49); }
        if (ca.fg_n    && !cb.fg_n)    { ck_emit_code(ty, out, 39); }
        if (ca.reverse && !cb.reverse) { ck_emit_code(ty, out, 27); }
        if (ca.ul_n    && !cb.ul_n)    { ck_emit_code(ty, out, 24); }
        if (ca.italic  && !cb.italic)  { ck_emit_code(ty, out, 23); }
        if (ca.bold    && !cb.bold)    { ck_emit_code(ty, out, 22); }

        bool al   = (ca.link != NULL);
        bool bl   = (cb.link != NULL);
        bool same = al && bl
                  && ca.link_len == cb.link_len
                  && memcmp(ca.link, cb.link, ca.link_len) == 0;

        if (!same && al && !bl) {
                svLIT(*out, "\x1b]8;;\x1b\\");
        } else if (!same && bl) {
                svLIT(*out, "\x1b]8;;");
                svPn(*out, cb.link, cb.link_len);
                svLIT(*out, "\x1b\\");
        }
}

static int
ck_hex_digit(u8 c)
{
        if (c >= '0' && c <= '9') { return c - '0'; }
        if (c >= 'a' && c <= 'f') { return c - 'a' + 10; }
        if (c >= 'A' && c <= 'F') { return c - 'A' + 10; }
        return -1;
}

static bool
ck_resolve(Ty *ty, char const *name, isize len,
           CkSty *out, Dict *custom);

static bool
ck_try_builtin(char const *nm, isize n, CkSty *o)
{
#define IS(lit) \
        (n == (isize)(sizeof (lit) - 1) && memcmp(nm, lit, n) == 0)

        if (IS("b") || IS("bold"))     { o->bold = 1;   return true; }
        if (IS("no-b") || IS("no-bold"))
                                       { o->bold = 2;   return true; }

        if (IS("i") || IS("italic"))   { o->italic = 1; return true; }
        if (IS("no-i") || IS("no-italic"))
                                       { o->italic = 2; return true; }

        if (IS("dim"))       { o->dim       = 1; return true; }
        if (IS("reverse"))   { o->reverse   = 1; return true; }
        if (IS("bright"))    { o->bright    = 1; return true; }
        if (IS("bg-bright")) { o->bg_bright = 1; return true; }

        if (IS("u") || IS("underline")) {
                o->ul_n = 1; o->ul[0] = 4;
                return true;
        }
        if (IS("no-u") || IS("no-underline")) {
                o->ul_n = 1; o->ul[0] = 24;
                return true;
        }
        if (IS("uu")) { o->ul_n = 2; o->ul[0] = 4; o->ul[1] = 2; return true; }
        if (IS("u~")) { o->ul_n = 2; o->ul[0] = 4; o->ul[1] = 3; return true; }
        if (IS("u.")) { o->ul_n = 2; o->ul[0] = 4; o->ul[1] = 4; return true; }
        if (IS("u-")) { o->ul_n = 2; o->ul[0] = 4; o->ul[1] = 5; return true; }

        if (IS("no-uc")) { o->uc_n = 1; o->uc[0] = 59; return true; }
        if (IS("no-fg")) { o->fg_n = 1; o->fg[0] = 39; return true; }
        if (IS("no-bg")) { o->bg_n = 1; o->bg[0] = 49; return true; }

        if (IS("black"))   { o->fg_n = 1; o->fg[0] = 30; return true; }
        if (IS("red"))     { o->fg_n = 1; o->fg[0] = 31; return true; }
        if (IS("green"))   { o->fg_n = 1; o->fg[0] = 32; return true; }
        if (IS("yellow"))  { o->fg_n = 1; o->fg[0] = 33; return true; }
        if (IS("blue"))    { o->fg_n = 1; o->fg[0] = 34; return true; }
        if (IS("magenta")) { o->fg_n = 1; o->fg[0] = 35; return true; }
        if (IS("cyan"))    { o->fg_n = 1; o->fg[0] = 36; return true; }
        if (IS("white"))   { o->fg_n = 1; o->fg[0] = 37; return true; }

        if (IS("bg-black"))   { o->bg_n = 1; o->bg[0] = 40; return true; }
        if (IS("bg-red"))     { o->bg_n = 1; o->bg[0] = 41; return true; }
        if (IS("bg-green"))   { o->bg_n = 1; o->bg[0] = 42; return true; }
        if (IS("bg-yellow"))  { o->bg_n = 1; o->bg[0] = 43; return true; }
        if (IS("bg-blue"))    { o->bg_n = 1; o->bg[0] = 44; return true; }
        if (IS("bg-magenta")) { o->bg_n = 1; o->bg[0] = 45; return true; }
        if (IS("bg-cyan"))    { o->bg_n = 1; o->bg[0] = 46; return true; }
        if (IS("bg-white"))   { o->bg_n = 1; o->bg[0] = 47; return true; }

#undef IS
        return false;
}

inline static bool
ck_try_ul_color(Ty *ty, char const *nm, isize n,
                CkSty *o, Dict *custom, int ul_sub)
{
        CkSty inner = {0};

        if (!ck_resolve(ty, nm, n, &inner, custom) || inner.fg_n == 0) {
                return false;
        }

        if (ul_sub >= 0) {
                o->ul_n    = ul_sub ? 2 : 1;
                o->ul[0]   = 4;
                o->ul[1]   = ul_sub;
        }

        o->uc_n  = inner.fg_n;
        o->uc[0] = inner.fg[0] + 20;
        for (int i = 1; i < inner.fg_n; ++i) {
                o->uc[i] = inner.fg[i];
        }

        return true;
}

static bool
ck_try_parse(Ty *ty, char const *nm, isize n,
             CkSty *o, Dict *custom)
{
        if (n > 1 && nm[0] == '#') {
                int rv, gv, bv;
                bool ok;

                if (n == 4) {
                        rv = ck_hex_digit(nm[1]);
                        gv = ck_hex_digit(nm[2]);
                        bv = ck_hex_digit(nm[3]);
                        ok = (rv | gv | bv) >= 0;
                        rv *= 17;
                        gv *= 17;
                        bv *= 17;
                } else if (n == 7) {
                        rv = (ck_hex_digit(nm[1]) << 4) | ck_hex_digit(nm[2]);
                        gv = (ck_hex_digit(nm[3]) << 4) | ck_hex_digit(nm[4]);
                        bv = (ck_hex_digit(nm[5]) << 4) | ck_hex_digit(nm[6]);
                        ok = (rv | gv | bv) >= 0;
                } else {
                        ok = false;
                }

                if (ok) {
                        o->fg_n  = 5;
                        o->fg[0] = 38;
                        o->fg[1] = 2;
                        o->fg[2] = rv;
                        o->fg[3] = gv;
                        o->fg[4] = bv;
                        return true;
                }
        }

        if (n > 3 && memcmp(nm, "bg-", 3) == 0) {
                CkSty inner = {0};
                if (!ck_resolve(ty, nm + 3, n - 3, &inner, custom)) {
                        return false;
                }
                if (inner.fg_n == 0) {
                        return false;
                }
                o->bg_n  = inner.fg_n;
                o->bg[0] = inner.fg[0] + 10;
                for (int i = 1; i < inner.fg_n; ++i) {
                        o->bg[i] = inner.fg[i];
                }
                return true;
        }

        if (n > 3 && memcmp(nm, "uc-", 3) == 0) {
                return ck_try_ul_color(ty, nm + 3, n - 3, o, custom, -1);
        }

        if (n > 3 && nm[0] == 'u' && nm[1] == '-' && nm[2] == '-') {
                return ck_try_ul_color(ty, nm + 3, n - 3, o, custom, 5);
        }

        if (n > 3 && nm[0] == 'u' && nm[1] == '.' && nm[2] == '-') {
                return ck_try_ul_color(ty, nm + 3, n - 3, o, custom, 4);
        }

        if (n > 2 && nm[0] == 'u' && nm[1] == '~') {
                return ck_try_ul_color(ty, nm + 2, n - 2, o, custom, 3);
        }

        if (n > 3 && nm[0] == 'u' && nm[1] == 'u' && nm[2] == '-') {
                return ck_try_ul_color(ty, nm + 3, n - 3, o, custom, 2);
        }

        if (n > 2 && nm[0] == 'u' && nm[1] == '-') {
                return ck_try_ul_color(ty, nm + 2, n - 2, o, custom, 0);
        }

        if (n > 5 && memcmp(nm, "link=", 5) == 0) {
                o->link     = (u8 const *)(nm + 5);
                o->link_len = n - 5;
                return true;
        }

        return false;
}

static bool
ck_resolve(Ty *ty, char const *nm, isize len,
           CkSty *out, Dict *custom)
{
        memset(out, 0, sizeof *out);

        if (custom != NULL) {
                Value key = vSs(nm, len);
                Value *v  = dict_get_value(ty, custom, &key);

                if (v != NULL && v->type == VALUE_STRING) {
                        u8 const *w  = ss(*v);
                        isize     wl = sN(*v);
                        while (wl > 0) {
                                while (wl > 0 && *w == ' ') {
                                        w  += 1;
                                        wl -= 1;
                                }
                                if (wl == 0) {
                                        break;
                                }
                                u8 const *ws = w;
                                while (wl > 0 && *w != ' ') {
                                        w  += 1;
                                        wl -= 1;
                                }
                                CkSty part = {0};
                                if (ck_resolve(ty, (char const *)ws, w - ws, &part, custom)) {
                                        ck_merge(out, &part);
                                }
                        }
                        return out->bold || out->italic
                            || out->dim  || out->reverse
                            || out->bright || out->bg_bright
                            || out->fg_n || out->bg_n
                            || out->uc_n || out->ul_n
                            || out->link;
                }

                if (v != NULL && v->type == VALUE_TUPLE && v->ids != NULL) {
                        int id_bold      = M_ID("bold");
                        int id_italic    = M_ID("italic");
                        int id_dim       = M_ID("dim");
                        int id_reverse   = M_ID("reverse");
                        int id_bright    = M_ID("bright");
                        int id_fg        = M_ID("fg");
                        int id_bg        = M_ID("bg");
                        int id_uc        = M_ID("uc");
                        int id_underline = M_ID("underline");
                        int id_link      = M_ID("link");

                        for (int i = 0; i < v->count; ++i) {
                                int    id = v->ids[i];
                                Value *f  = &v->items[i];

                                if (id == id_bold && f->type == VALUE_BOOLEAN) {
                                        out->bold = f->boolean ? 1 : 2;
                                } else if (id == id_italic && f->type == VALUE_BOOLEAN) {
                                        out->italic = f->boolean ? 1 : 2;
                                } else if (id == id_dim && f->type == VALUE_BOOLEAN) {
                                        out->dim = f->boolean ? 1 : 2;
                                } else if (id == id_reverse && f->type == VALUE_BOOLEAN) {
                                        out->reverse = f->boolean ? 1 : 2;
                                } else if (id == id_bright && f->type == VALUE_BOOLEAN) {
                                        out->bright = f->boolean ? 1 : 0;
                                } else if (id == id_fg && f->type == VALUE_ARRAY) {
                                        out->fg_n = min(vN(*f->array), 5);
                                        for (int j = 0; j < out->fg_n; ++j) {
                                                out->fg[j] = v_(*f->array, j)->z;
                                        }
                                } else if (id == id_bg && f->type == VALUE_ARRAY) {
                                        out->bg_n = min(vN(*f->array), 5);
                                        for (int j = 0; j < out->bg_n; ++j) {
                                                out->bg[j] = v_(*f->array, j)->z;
                                        }
                                } else if (id == id_uc && f->type == VALUE_ARRAY) {
                                        out->uc_n = min(vN(*f->array), 5);
                                        for (int j = 0; j < out->uc_n; ++j) {
                                                out->uc[j] = v_(*f->array, j)->z;
                                        }
                                } else if (id == id_underline && f->type == VALUE_ARRAY) {
                                        out->ul_n = min(vN(*f->array), 2);
                                        for (int j = 0; j < out->ul_n; ++j) {
                                                out->ul[j] = v_(*f->array, j)->z;
                                        }
                                } else if (id == id_link && f->type == VALUE_STRING) {
                                        out->link     = ss(*f);
                                        out->link_len = sN(*f);
                                }
                        }
                        return true;
                }

                if (v != NULL && v->type == VALUE_NIL) {
                        return false;
                }
        }

        return ck_try_builtin(nm, len, out)
            || ck_try_parse(ty, nm, len, out, custom);
}

static bool
ck_stops(Ty *ty, char const *stop, isize slen,
         CkSty const *sty, Dict *custom)
{
#define IS(lit) \
        (slen == (isize)(sizeof (lit) - 1) && memcmp(stop, lit, slen) == 0)

        if (IS("fg"))                   { return sty->fg_n > 0;      }
        if (IS("bg"))                   { return sty->bg_n > 0;      }
        if (IS("uc"))                   { return sty->uc_n > 0;      }
        if (IS("u") || IS("underline")) { return sty->ul_n > 0;      }
        if (IS("link"))                 { return sty->link != NULL;   }

#undef IS

        CkSty ref = {0};

        if (!ck_resolve(ty, stop, slen, &ref, custom)) {
                return false;
        }

        if (memcmp(sty, &ref, offsetof(CkSty, link)) != 0) {
                return false;
        }

        if (sty->link_len != ref.link_len) {
                return false;
        }

        return sty->link == ref.link
            || (sty->link && ref.link
                && memcmp(sty->link, ref.link, ref.link_len) == 0);
}

#define CK_MAX_DEPTH  64
#define CK_MAX_PER    16
#define CK_MAX_OSTACK  8

typedef struct {
        CkSty   s[CK_MAX_PER];
        int     n;
        bool    is_fmt;
        u8 const *fmt;
        isize   fmt_len;
} CkFrame;

static CkSty
ck_flatten(CkFrame *frames, int nf)
{
        CkSty r = {0};

        for (int f = 0; f < nf; ++f) {
                if (frames[f].is_fmt) {
                        continue;
                }
                for (int i = 0; i < frames[f].n; ++i) {
                        ck_merge(&r, &frames[f].s[i]);
                }
        }

        return r;
}

static void
ck_apply_fmt(Ty *ty, byte_vector *dst,
             u8 const *text, isize tlen,
             u8 const *spec, isize slen)
{
        struct fspec fs;
        char const *p   = (char const *)spec;
        char const *end = p + slen;

        fspec_parse(&p, end, &fs);

        FspecPad fp = fspec_pad((char const *)text, tlen, &fs);

        for (int i = 0; i < fp.left; ++i) {
                svPn(*dst, fp.fill, fp.fill_sz);
        }
        svPn(*dst, text, tlen);
        for (int i = 0; i < fp.right; ++i) {
                svPn(*dst, fp.fill, fp.fill_sz);
        }
}

static void
ck_finish_fmt(Ty *ty, byte_vector *out, byte_vector *ostack,
              int *nos, CkFrame *frame)
{
        if (*nos <= 0) {
                return;
        }

        byte_vector cap = *out;

        *out = ostack[--(*nos)];

        ck_apply_fmt(
                ty, out,
                vv(cap), vN(cap),
                frame->fmt,
                frame->fmt_len
        );
}

static void
ck_next_word(u8 const **w, isize *wl,
             u8 const **ws, isize *wn)
{
        while (*wl > 0 && **w == ' ') {
                *w  += 1;
                *wl -= 1;
        }
        *ws = *w;
        while (*wl > 0 && **w != ' ') {
                *w  += 1;
                *wl -= 1;
        }
        *wn = *w - *ws;
}

#define CK_UPDATE() do {                        \
        CkSty nw = ck_flatten(stack, nf);       \
        ck_trans(ty, &out, &cur, &nw);          \
        cur = nw;                               \
} while (0)

static Value
string_chalk(Ty *ty, Value *string, int argc, Value *kwargs)
{
        ASSERT_ARGC("String.chalk()", 0, 1);

        Dict *custom = (argc == 1 && ARG(0).type == VALUE_DICT)
                      ? ARG(0).dict
                      : NULL;

        GC_STOP();

        u8 const *s = ss(*string);
        isize     len = sN(*string);

        SCRATCH_SAVE();

        byte_vector out = {0};

        CkFrame stack[CK_MAX_DEPTH];
        int nf = 1;
        stack[0] = (CkFrame){0};

        byte_vector ostack[CK_MAX_OSTACK];
        int nos = 0;

        CkSty cur = {0};
        isize pos = 0;

        for (;;) {
                isize ts = pos;

                while (pos < len) {
                        if (
                                   s[pos] == '\\'
                                && pos + 1 < len
                                && (s[pos + 1] == '\\' || s[pos + 1] == '[')
                        ) {
                                break;
                        }
                        if (s[pos] == '[') {
                                break;
                        }
                        pos += 1;
                }

                for (isize i = ts; i < pos; ++i) {
                        if (s[i] == '\\' && i + 1 < pos) {
                                i += 1;
                        }
                        svPn(out, s + i, 1);
                }

                if (pos >= len) {
                        break;
                }

                if (s[pos] == '\\') {
                        svPn(out, s + pos + 1, 1);
                        pos += 2;
                        continue;
                }

                isize bstart = pos;
                pos += 1;

                isize ps = pos;
                while (pos < len && (s[pos] == '/' || s[pos] == '%')) {
                        pos += 1;
                }
                isize plen = pos - ps;

                isize cs = pos;
                while (pos < len && s[pos] != ']') {
                        pos += 1;
                }
                isize clen = pos - cs;

                if (pos >= len) {
                        pos = bstart + 1;
                        svLIT(out, "[");
                        continue;
                }
                pos += 1;

                if (plen == 0) {
                        if (nf >= CK_MAX_DEPTH) {
                                continue;
                        }
                        CkFrame *f = &stack[nf++];
                        f->is_fmt = false;
                        f->n      = 0;
                        u8 const *w  = s + cs;
                        isize     wl = clen;
                        while (wl > 0) {
                                u8 const *ws;
                                isize     wn;
                                ck_next_word(&w, &wl, &ws, &wn);
                                if (wn == 0) {
                                        break;
                                }
                                CkSty st = {0};
                                if (
                                           f->n < CK_MAX_PER
                                        && ck_resolve(ty, (char const *)ws, wn, &st, custom)
                                ) {
                                        f->s[f->n++] = st;
                                }
                        }
                        CK_UPDATE();
                } else if (plen == 1 && s[ps] == '%') {
                        if (nf >= CK_MAX_DEPTH || nos >= CK_MAX_OSTACK) {
                                continue;
                        }
                        ostack[nos++] = out;
                        out = (byte_vector){0};
                        CkFrame *f = &stack[nf++];
                        f->is_fmt  = true;
                        f->fmt     = s + cs;
                        f->fmt_len = clen;
                        f->n       = 0;
                } else {
                        bool has_words = false;
                        for (isize i = 0; i < clen; ++i) {
                                if (s[cs + i] != ' ') {
                                        has_words = true;
                                        break;
                                }
                        }

                        if (!has_words) {
                                int npop = min((int)plen, nf);
                                for (int k = 0; k < npop && nf > 0; ++k) {
                                        nf -= 1;
                                        if (stack[nf].is_fmt) {
                                                ck_finish_fmt(
                                                        ty, &out, ostack,
                                                        &nos, &stack[nf]
                                                );
                                        }
                                }
                                CK_UPDATE();
                        } else {
                                u8 const *w  = s + cs;
                                isize     wl = clen;
                                while (wl > 0) {
                                        u8 const *ws;
                                        isize     wn;
                                        ck_next_word(&w, &wl, &ws, &wn);
                                        if (wn == 0) {
                                                break;
                                        }
                                        for (int fi = nf - 1; fi >= 0; --fi) {
                                                CkFrame *f = &stack[fi];
                                                if (f->is_fmt) {
                                                        continue;
                                                }
                                                bool found = false;
                                                for (int j = f->n - 1; j >= 0; --j) {
                                                        if (!ck_stops(ty, (char const *)ws, wn,
                                                                      &f->s[j], custom)) {
                                                                continue;
                                                        }
                                                        f->n -= 1;
                                                        for (int k = j; k < f->n; ++k) {
                                                                f->s[k] = f->s[k + 1];
                                                        }
                                                        found = true;
                                                        break;
                                                }
                                                if (found) {
                                                        break;
                                                }
                                        }
                                }
                                int dst = 0;
                                for (int fi = 0; fi < nf; ++fi) {
                                        if (stack[fi].n > 0 || stack[fi].is_fmt) {
                                                stack[dst++] = stack[fi];
                                        }
                                }
                                nf = dst;
                                CK_UPDATE();
                        }
                }
        }

        for (int fi = nf - 1; fi >= 0; --fi) {
                if (stack[fi].is_fmt) {
                        ck_finish_fmt(ty, &out, ostack, &nos, &stack[fi]);
                }
        }

        {
                int dst = 0;
                for (int fi = 0; fi < nf; ++fi) {
                        if (!stack[fi].is_fmt) {
                                stack[dst++] = stack[fi];
                        }
                }
                nf = dst;
        }

        CK_UPDATE();
        svLIT(out, "\x1b[0m");

        GC_RESUME();
        CheckUsed(ty);

        Value result = (vN(out) > 0)
                     ? vSs(vv(out), vN(out))
                     : STRING_EMPTY;

        SCRATCH_RESTORE();

        return result;
}

#undef CK_UPDATE
#undef SN
#undef svLIT

DEFINE_METHOD_TABLE(
        string,
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
        { .name = "chalk",     .func = string_chalk             },
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
        { .name = "plain",     .func = string_plain            },
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
        { .name = "unchalk",   .func = string_unchalk          },
        { .name = "upper",     .func = string_upper            },
        { .name = "width",     .func = string_width            },
        { .name = "words",     .func = string_words            },
);

DEFINE_METHOD_LOOKUP(string)
DEFINE_METHOD_TABLE_BUILDER(string)
DEFINE_METHOD_COMPLETER(string)

/* vim: set sw=8 sts=8 expandtab: */
