#include <ctype.h>
#include <string.h>

#include <utf8proc.h>
#include <pcre2.h>

#include "utf8.h"
#include "value.h"
#include "util.h"
#include "gc.h"
#include "vm.h"
#include "token.h"
#include "functions.h"
#include "polyfill_memmem.h"

static _Thread_local struct stringpos limitpos;
static _Thread_local struct stringpos outpos;

inline static void
stringcount(char const *s, int byte_lim, int grapheme_lim)
{
        limitpos.bytes = byte_lim;
        limitpos.graphemes = grapheme_lim;
        utf8_stringcount(s, byte_lim, &outpos, &limitpos);
}

inline static int
stringwidth(char const *s, int byte_lim)
{
        int width = 0;
        limitpos.graphemes = -1;

        while (byte_lim > 0) {
                limitpos.bytes = byte_lim;
                utf8_stringcount(s, byte_lim, &outpos, &limitpos);
                int n = max(1, outpos.bytes);
                byte_lim -= n;
                s += n;
                width += outpos.graphemes;
        }

        return width;
}

inline static bool
is_prefix(char const *big, int blen, char const *little, int slen)
{
        return (blen >= slen) && (memcmp(big, little, slen) == 0);
}

inline static char const *
sfind(char const *big, int blen, char const *little, int slen)
{
        register int i;

        while (blen >= slen) {
                for (i = 0; i < slen; ++i) {
                        if (big[i] != little[i]) {
                                goto Next;
                        }
                }

                return big;

Next:
                ++big;
                --blen;
        }

        return NULL;

}

inline static Value
mkmatch(Ty *ty, Value *s, size_t *ovec, int n, bool detailed)
{
        if (detailed) {
                Array *groups = vA();

                NOGC(groups);

                for (int i = 0, j = 0; i < n; ++i, j += 2) {
                        Value group = vT(2);
                        group.items[0] = INTEGER(ovec[j]);
                        group.items[1] = INTEGER(ovec[j + 1] - ovec[j]);
                        NOGC(group.items);
                        vAp(groups, group);
                        OKGC(group.items);
                }

                vmP(s);
                vmP(&ARRAY(groups));

                OKGC(groups);

                return vmC(&CLASS(CLASS_RE_MATCH), 2);
        } else if (n == 1) {
                return STRING_VIEW(*s, ovec[0], ovec[1] - ovec[0]);
        } else {
                Value match = ARRAY(vA());
                NOGC(match.array);

                for (int i = 0, j = 0; i < n; ++i, j += 2) {
                        vvP(*match.array, STRING_VIEW(*s, ovec[j], ovec[j + 1] - ovec[j]));
                }

                OKGC(match.array);

                return match;
        }
}

static Value
string_length(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *s = string->string;
        int size = string->bytes;
        int offset = 0;
        int state = 0;
        int length = 0;

        while (size > 0) {
                int codepoint;
                int n = utf8proc_iterate(s + offset, size, &codepoint);
                if (n <= 0) {
                        size -= 1;
                        offset += 1;
                        continue;
                } else while (n < size) {
                        int next;
                        int m = utf8proc_iterate(s + offset + n, size - n, &next);
                        if (m < 0)
                                break;
                        if (utf8proc_grapheme_break_stateful(codepoint, next, &state))
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
        char const *_name__ = "String.chars()";

        CHECK_ARGC(0);

        uint8_t const *s = (uint8_t *)string->string;
        int size = string->bytes;
        int offset = 0;
        int state = 0;

        struct array *r = vA();
        NOGC(r);

        while (size > 0) {
                int codepoint;
                int n = utf8proc_iterate(s + offset, size, &codepoint);
                if (n < 0) {
                        size -= 1;
                        offset += 1;
                        continue;
                } else if (codepoint & 0xC0) while (n < size) {
                        int next;
                        int m = utf8proc_iterate(s + offset + n, size - n, &next);
                        if (m < 0)
                                break;
                        if (utf8proc_grapheme_break_stateful(codepoint, next, &state))
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
        if (argc != 0)
                zP("str.size() expects no arguments but got %d", argc);

        return INTEGER(string->bytes);
}

static Value
string_bslice(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc == 0 || argc > 2)
                zP("str.bslice() expects 1 or 2 arguments but got %d", argc);

        Value start = ARG(0);

        if (start.type != VALUE_INTEGER)
                zP("str.bslice(): expected integer but got: %s", value_show(ty, &start));

        int i = start.integer;
        int n;

        if (i < 0) {
                i += string->bytes;
        }

        if (argc == 2) {
                Value len = ARG(1);
                if (len.type != VALUE_INTEGER)
                        zP("str.bslice(): expected integer but got: %s", value_show(ty, &len));
                n = len.integer;
        } else {
                n = (int)string->bytes - i;
        }

        i = min(max(i, 0), string->bytes);
        n = min(max(n, 0), string->bytes - i);

        return STRING_VIEW(*string, i, n);
}

static Value
string_slice(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc == 0 || argc > 2)
                zP("str.slice() expects 1 or 2 arguments but got %d", argc);

        Value start = ARG(0);

        if (start.type != VALUE_INTEGER)
                zP("non-integer passed as first argument to str.slice()");

        char const *s = string->string;
        int i = start.integer;
        int n;

        stringcount(s, string->bytes, -1);

        if (argc == 2) {
                Value len = ARG(1);
                if (len.type != VALUE_INTEGER)
                        zP("non-integer passed as second argument to str.slice()");
                n = len.integer;
        } else {
                n = outpos.graphemes;
        }

        if (i < 0)
                i += outpos.graphemes;
        i = min(max(0, i), outpos.graphemes);

        if (n < 0)
                n += outpos.graphemes;
        n = min(max(0, n), outpos.graphemes - i);

        stringcount(s, string->bytes, i);

        i = outpos.bytes;

        stringcount(s + i, limitpos.bytes - outpos.bytes, n);

        return STRING_VIEW(*string, i, outpos.bytes);
}

static Value
string_search_all(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("str.searchAll() expects 1 or 2 arguments but got %d", argc);

        Value pattern = ARG(0);

        if (pattern.type != VALUE_STRING && pattern.type != VALUE_REGEX)
                zP("the pattern argument to str.searchAll() must be a string or a regex");

        int offset;
        if (argc == 1)
                offset = 0;
        else if (ARG(1).type == VALUE_INTEGER)
                offset = ARG(1).integer;
        else
                zP("the second argument to str.searchAll() must be an integer");

        if (offset < 0) {
                stringcount(string->string, string->bytes, -1);
                offset += outpos.graphemes;
        }

        if (offset < 0)
                zP("invalid offset passed to str.searchAll()");

        stringcount(string->string, string->bytes, offset);
        if (outpos.graphemes != offset)
                return NIL;

        char const *s = string->string + outpos.bytes;
        int bytes = string->bytes - outpos.bytes;

        int n;
        int off = 0;

        Value result = ARRAY(vA());
        gP(&result);

        if (pattern.type == VALUE_STRING) {
                while (off < bytes) {
                        char const *match = memmem(s + off, bytes - off, pattern.string, pattern.bytes);

                        if (match == NULL)
                                break;

                        n = match - (s + off);

                        stringcount(s + off, n, -1);

                        vAp(result.array, INTEGER(offset + outpos.graphemes));

                        stringcount(s + off, n + pattern.bytes, -1);

                        offset += outpos.graphemes;
                        off += n + pattern.bytes;
                }
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);
                int rc;

                for (;;) {
                        rc = pcre2_match(re, (PCRE2_SPTR)s, 3, off, 0, ty->pcre2.match, ty->pcre2.ctx);

                        if (rc <= 0) {
                                break;
                        }

                        n = ovec[1] - ovec[0];

                        stringcount(s + off, n, -1);

                        vAp(result.array, INTEGER(offset + outpos.graphemes));

                        stringcount(s + off, ovec[1], -1);

                        offset += outpos.graphemes;
                        off = ovec[1];
                }

                switch (rc) {
                        char err[256];
                case PCRE2_ERROR_NOMATCH:
                case PCRE2_ERROR_BADOFFSET:
                        break;
                default:
                        pcre2_get_error_message(rc, (uint8_t *)err, sizeof err);
                        zP("String.searchAll(): PCRE2 error: %s", err);
                }
        }


        gX();

        return result;
}

static Value
string_bsearch(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.bsearch()";

        CHECK_ARGC(1, 2);

        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);
        int64_t offset = (argc == 1) ? 0 : INT_ARG(1);

        if (offset < 0) {
                offset += string->bytes;
        }

        if (offset < 0) {
                zP("String.search(): invalid offset: %"PRIi64, offset);
        }

        if (offset >= string->bytes) {
                return NIL;
        }

        char const *s = string->string + offset;
        int64_t bytes = (int64_t)string->bytes - offset;

        int64_t n;

        if (pattern.type == VALUE_STRING) {
                char const *match = memmem(s, bytes, pattern.string, pattern.bytes);

                if (match == NULL)
                        return NIL;

                n = match - s;
        } else if (pattern.type == VALUE_REGEX) {
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);
                int rc = pcre2_match(
                        pattern.regex->pcre2,
                        (PCRE2_SPTR)s,
                        bytes,
                        0,
                        0,
                        ty->pcre2.match,
                        ty->pcre2.ctx
                );

                if (rc == PCRE2_ERROR_NOMATCH) {
                        return NIL;
                }

                if (rc < 0) {
                        char err[256];
                        pcre2_get_error_message(rc, (uint8_t *)err, sizeof err);
                        zP("String.search(): PCRE2 error: %s", err);
                }

                n = ovec[0];
        } else {
                ARGx(0, VALUE_STRING, VALUE_REGEX);
        }

        return INTEGER(offset + n);
}

static Value
string_search(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.search()";

        CHECK_ARGC(1, 2);

        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);

        int64_t offset = (argc == 1) ? 0 : INT_ARG(1);

        if (offset < 0) {
                stringcount(string->string, string->bytes, -1);
                offset += outpos.graphemes;
        }

        if (offset < 0) {
                zP("String.search(): invalid offset: %"PRIi64, offset);
        }

        stringcount(string->string, string->bytes, offset);
        if (outpos.graphemes != offset) {
                return NIL;
        }

        char const *s = string->string + outpos.bytes;
        int64_t bytes = (int64_t)string->bytes - outpos.bytes;

        int64_t n;

        if (pattern.type == VALUE_STRING) {
                char const *match = memmem(s, bytes, pattern.string, pattern.bytes);

                if (match == NULL)
                        return NIL;

                n = match - s;
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);

                int rc = pcre2_match(re, (PCRE2_SPTR)s, bytes, 0, 0, ty->pcre2.match, ty->pcre2.ctx);

                if (rc == PCRE2_ERROR_NOMATCH) {
                        return NIL;
                }

                if (rc < -1) {
                        char err[256];
                        pcre2_get_error_message(rc, (uint8_t *)err, sizeof err);
                        zP("String.search(): PCRE2 error: %s", err);
                }

                n = ovec[0];
        }

        stringcount(s, n, -1);

        return INTEGER(offset + outpos.graphemes);
}

static Value
string_contains(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 1 && argc != 2)
                zP("str.contains?() expects 1 or 2 arguments but got %d", argc);

        Value pattern = ARG(0);

        if (pattern.type != VALUE_STRING)
                zP("the pattern argument to str.contains?() must be a string");

        int offset;
        if (argc == 1)
                offset = 0;
        else if (ARG(1).type == VALUE_INTEGER)
                offset = ARG(1).integer;
        else
                zP("the second argument to str.contains?() must be an integer");

        if (offset < 0) {
                stringcount(string->string, string->bytes, -1);
                offset += outpos.graphemes;
        }

        if (offset < 0)
                zP("invalid offset passed to str.contains?()");

        stringcount(string->string, string->bytes, offset);
        if (outpos.graphemes != offset)
                return BOOLEAN(false);

        char const *s = string->string + outpos.bytes;
        int bytes = string->bytes - outpos.bytes;

        char const *match = memmem(s, bytes, pattern.string, pattern.bytes);

        if (match == NULL)
                return BOOLEAN(false);

        stringcount(s, match - s, -1);

        return BOOLEAN(true);
}

static Value
string_words(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.words()";

        CHECK_ARGC(0);

        gP(string);

        struct array *a = vA();
        NOGC(a);

        int i = 0;
        int len = string->bytes;
        int n = 0;
        char const *s = string->string;

        if (len == 0) {
                goto End;
        }

        utf8proc_int32_t cp;


        while (i < len) {
                utf8proc_iterate(s + i, len - i, &cp);
                utf8proc_category_t c = utf8proc_category(cp);
                while (i < len &&
                        (isspace(s[i]) || c == UTF8PROC_CATEGORY_ZS || c == UTF8PROC_CATEGORY_ZL || c == UTF8PROC_CATEGORY_ZP)) {
                        i += n;
                        n = utf8proc_iterate(s + i, len - i, &cp);
                        c = utf8proc_category(cp);
                }

                if (i >= len)
                        break;

                Value str = STRING_VIEW(*string, i, 0);

                do {
                        str.bytes += n;
                        i += n;
                        n = utf8proc_iterate(s + i, len - i, &cp);
                        c = utf8proc_category(cp);
                } while (i < len && !isspace(s[i]) && c != UTF8PROC_CATEGORY_ZS && c != UTF8PROC_CATEGORY_ZL && c != UTF8PROC_CATEGORY_ZP);

                vAp(a, str);
        }
End:
        gX();
        OKGC(a);

        return ARRAY(a);
}

static Value
string_lines(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.lines()";

        CHECK_ARGC(0);

        gP(string);

        struct array *a = vA();
        NOGC(a);

        int i = 0;
        int len = string->bytes;
        char const *s = string->string;

        if (len == 0) {
                vAp(a, *string);
                goto End;
        }

        while (i < len) {
                Value str = STRING_VIEW(*string, i, 0);

                while (i < len && s[i] != '\n' && !is_prefix(s + i, len - i, "\r\n", 2)) {
                        ++str.bytes;
                        ++i;
                }

                vAp(a, str);

                if (i < len)
                        i += 1 + (s[i] == '\r');
        }
End:
        gX();
        OKGC(a);

        return ARRAY(a);
}

static Value
string_split(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.split()";

        CHECK_ARGC(1, 2);

        char const *s = string->string;
        int len = string->bytes;
        gP(string);

        Value pattern = ARGx(0, VALUE_INTEGER, VALUE_STRING, VALUE_REGEX);

        if (pattern.type == VALUE_INTEGER) {
                int i = pattern.integer;
                int n = utf8_charcount(s, len);
                if (i < 0)
                        i += n;
                if (i < 0)
                        i = 0;
                if (i > n)
                        i = n;
                stringcount(s, len, i);
                struct array *parts = vA();
                NOGC(parts);
                vAp(parts, STRING_VIEW(*string, 0, outpos.bytes));
                vAp(parts, STRING_VIEW(*string, outpos.bytes, len - outpos.bytes));
                OKGC(parts);
                gX();
                return ARRAY(parts);
        }

        if (argc == 2) {
                ARGx(1, VALUE_INTEGER);
        }

        Value result = ARRAY(vA());
        NOGC(result.array);

        if (pattern.type == VALUE_STRING) {
                char const *p = pattern.string;
                int n = pattern.bytes;

                if (n == 0)
                        goto End;

                int i = 0;
                while (i < len) {
                        Value str = STRING_VIEW(*string, i, 0);

                        if (argc == 2 && result.array->count == ARG(1).integer) {
                                str.bytes = len - i;
                                i = len;
                        } else {
                                while (i < len && !is_prefix(s + i, len - i, p, n)) {
                                        ++str.bytes;
                                        ++i;
                                }
                        }

                        vAp(result.array, str);

                        i += n;
                }

                if (i == len)
                        vAp(result.array, STRING_EMPTY);
        } else {
                pcre2_code *re = pattern.regex->pcre2;
                size_t len = string->bytes;
                int start = 0;
                int pstart = 0;
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);

                while (start < len) {
                        if ((argc == 2 && result.array->count == ARG(1).integer) ||
                            pcre2_match(re, (PCRE2_SPTR)s, len, pstart, 0, ty->pcre2.match, ty->pcre2.ctx) != 1) {
                                ovec[0] = len;
                                ovec[1] = len + 1;
                        }

                        vAp(result.array, STRING_VIEW(*string, start, ovec[0] - start));

                        pstart = ovec[1] + (ovec[0] == ovec[1]);
                        start = ovec[1];
                }

                if (start == len) {
                        vAp(result.array, STRING_EMPTY);
                }
        }

End:
        gX();
        OKGC(result.array);
        return result;
}

static Value
string_count(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.count()";

        CHECK_ARGC(1);

        Value pattern = ARG(0);
        int count = 0;

        char const *s = string->string;
        size_t len = string->bytes;

        if (s == NULL) {
                return STRING_EMPTY;
        }

        if (pattern.type == VALUE_STRING) {
                char const *m;
                char const *p = pattern.string;
                int plen = pattern.bytes;

                if (plen > 0) while ((m = sfind(s, len, p, plen)) != NULL) {
                        len -= (m - s + plen);
                        s = m + plen;
                        count += 1;
                }
        } else if (pattern.type == VALUE_REGEX) {
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);
                size_t off = 0;
                int rc;

                for (;;) {
                        rc = pcre2_match(
                                pattern.regex->pcre2,
                                (PCRE2_SPTR)s,
                                len,
                                off,
                                0,
                                ty->pcre2.match,
                                ty->pcre2.ctx
                        );

                        if (rc <= 0) { break; }

                        count += 1;
                        off = ovec[1];
                }
        } else {
                ARGx(0, VALUE_STRING, VALUE_REGEX);
        }

        return INTEGER(count);
}

/* copy + paste of replace, can fix later */
static Value
string_comb(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.comb()";

        CHECK_ARGC(1);

        vec(char) chars = {0};
        Value pattern = ARG(0);

        char const *s = string->string;

        if (s == NULL) {
                return STRING_EMPTY;
        }

        switch (pattern.type) {
        case VALUE_STRING:
        {
                char const *p = pattern.string;

                int len = string->bytes;
                int plen = pattern.bytes;
                char const *m;

                while ((m = sfind(s, len, p, plen)) != NULL) {
                        vvPn(chars, s, m - s);
                        len -= (m - s + plen);
                        s = m + plen;
                }

                vvPn(chars, s, len);

                break;
        }
        case VALUE_REGEX:
        {
                pcre2_code *re = pattern.regex->pcre2;
                size_t len = string->bytes;
                int start = 0;
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);

                while (pcre2_match(re, (PCRE2_SPTR)s, len, start, 0, ty->pcre2.match, ty->pcre2.ctx) == 1) {
                        vvPn(chars, s + start, ovec[0] - start);
                        start = ovec[1];
                }

                vvPn(chars, s + start, len - start);

                break;
        }
        default:
                ARGx(0, VALUE_STRING, VALUE_REGEX);
        }

        Value r = vSs(chars.items, chars.count);

        mF(chars.items);

        return r;
}

static Value
string_repeat(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 1) {
                zP("String.repeat(): expected 1 argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER || ARG(0).integer < 0) {
                zP("String.repeat(): argument mut be a non-negative integer");
        }

        char *s = value_string_alloc(ty, string->bytes * ARG(0).integer);
        size_t off = 0;

        for (int i = 0; i < ARG(0).integer; ++i) {
                memcpy(s + off, string->string, string->bytes);
                off += string->bytes;
        }

        return STRING(s, off);
}

static Value
string_replace(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.replace()";

        CHECK_ARGC(2);

        vec(char) chars = {0};
        Value pattern = ARGx(0, VALUE_REGEX, VALUE_STRING);
        Value replacement = ARG(1);

        char const *s = string->string;

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

                char const *p = pattern.string;
                char const *r = replacement.string;

                int len = string->bytes;
                int plen = pattern.bytes;
                char const *m;

                while ((m = sfind(s, len, p, plen)) != NULL) {
                        vvPn(chars, s, m - s);

                        vvPn(chars, r, replacement.bytes);

                        len -= (m - s + plen);
                        s = m + plen;
                }

                vvPn(chars, s, len);
        } else if (replacement.type == VALUE_STRING) {
                pcre2_code *re = pattern.regex->pcre2;
                size_t len = string->bytes;
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);
                int start = 0;

                while (pcre2_match(re, (PCRE2_SPTR)s, len, start, 0, ty->pcre2.match, ty->pcre2.ctx) == 1) {
                        if (ovec[1] == start) {
                                vvPn(chars, replacement.string, replacement.bytes);
                                vvP(chars, s[start]);
                                start = ovec[1] + 1;
                        } else {
                                vvPn(chars, s + start, ovec[0] - start);
                                vvPn(chars, replacement.string, replacement.bytes);
                                start = ovec[1];
                        }
                }

                if (start < len) {
                        vvPn(chars, s + start, len - start);
                }
        } else if (CALLABLE(replacement)) {
                pcre2_code *re = pattern.regex->pcre2;
                size_t len = string->bytes;
                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);
                int start = 0;
                int rc;

                while ((rc = pcre2_match(re, (PCRE2_SPTR)s, len, start, 0, ty->pcre2.match, ty->pcre2.ctx)) > 0) {
                        vvPn(chars, s + start, ovec[0] - start);

                        Value match;
                        if (rc == 1) {
                                match = STRING_VIEW(*string, ovec[0], ovec[1] - ovec[0]);
                        } else {
                                match = ARRAY(vA());
                                NOGC(match.array);

                                int j = 0;
                                for (int i = 0; i < rc; ++i, j += 2) {
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

                        Value substitute = vm_eval_function(ty, &replacement, &match, NULL);
                        vmP(&substitute);
                        substitute = builtin_str(ty, 1, NULL);
                        vmX();

                        if (match.type == VALUE_ARRAY) {
                                OKGC(match.array);
                        }

                        vvPn(chars, substitute.string, substitute.bytes);

                        start = ovec[1];
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
        char const *_name__ = "String.match?()";

        CHECK_ARGC(1);

        Value pattern = ARGx(0, VALUE_REGEX);

        int rc = pcre2_match(
                pattern.regex->pcre2,
                (PCRE2_SPTR)string->string,
                string->bytes,
                0,
                0,
                ty->pcre2.match,
                ty->pcre2.ctx
        );

        if (rc < -2)
                zP("error while executing regular expression: %d", rc);

        return BOOLEAN(rc > -1);
}

static Value
string_match(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.match!()";

        CHECK_ARGC(1);

        Value pattern = ARGx(0, VALUE_REGEX);
        size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);

        int rc = pcre2_match(
                pattern.regex->pcre2,
                (PCRE2_SPTR)string->string,
                string->bytes,
                0,
                0,
                ty->pcre2.match,
                ty->pcre2.ctx
        );

        if (rc < -2)
                zP("error while executing regular expression: %d", rc);

        if (rc < 0)
                return NIL;

        return mkmatch(ty, string, ovec, rc, pattern.regex->detailed);
}

static Value
string_matches(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.matches()";

        CHECK_ARGC(1);

        Value pattern = ARGx(0, VALUE_REGEX);

        Value result = ARRAY(vA());
        gP(&result);

        size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);
        size_t offset = 0;
        int rc;

        for (;;) {
                rc = pcre2_match(
                        pattern.regex->pcre2,
                        (PCRE2_SPTR)string->string,
                        string->bytes,
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
                char err[256];
        case PCRE2_ERROR_NOMATCH:
        case PCRE2_ERROR_BADOFFSET:
                break;
        default:
                pcre2_get_error_message(rc, (uint8_t *)err, sizeof err);
                zP("String.matches(): PCRE2 error: %s", err);
        }

        gX();

        return result;
}

static Value
string_byte(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("str.byte() expects 1 argument but got %d", argc);

        Value i = ARG(0);

        if (i.type != VALUE_INTEGER)
                zP("non-integer passed to str.byte()");

        if (i.integer < 0)
                i.integer += string->bytes;

        if (i.integer < 0 || i.integer >= string->bytes)
                return NIL; /* TODO: maybe panic */

        return INTEGER((unsigned char)string->string[i.integer]);
}

static Value
string_char(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.char()";

        CHECK_ARGC(1);

        int64_t i = INT_ARG(0);

        if (i < 0) {
                i += string_length(ty, string, 0, NULL).integer;
        }

        int cp;
        int64_t j = i;
        int64_t offset = 0;
        int n = utf8proc_iterate(string->string, string->bytes, &cp);

        while (offset < string->bytes && n > 0 && j --> 0) {
                offset += max(1, n);
                n = utf8proc_iterate(string->string + offset, string->bytes, &cp);
        }

        if (offset == string->bytes)
                return NIL;

        return STRING_VIEW(*string, offset, n);
}

static Value
string_bytes(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.bytes()";

        CHECK_ARGC(0);

        Value result = ARRAY(vA());
        NOGC(result.array);

        for (int i = 0; i < string->bytes; ++i) {
                vAp(result.array, INTEGER((unsigned char)string->string[i]));
        }

        OKGC(result.array);

        return result;
}

static Value
string_lower(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.lower()";

        CHECK_ARGC(0);

        utf8proc_int32_t c;
        utf8proc_uint8_t *s = (utf8proc_uint8_t *) string->string;
        size_t len = string->bytes;

        size_t outlen = 0;
        char *result = value_string_alloc(ty, 4 * string->bytes);

        while (len > 0) {
                int n = max(1, utf8proc_iterate(s, len, &c));
                s += n;
                len -= n;
                c = utf8proc_tolower(c);
                outlen += utf8proc_encode_char(c, (utf8proc_uint8_t *)result + outlen);
        }

        return STRING(result, outlen);
}

static Value
string_upper(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.upper()";

        CHECK_ARGC(0);

        utf8proc_int32_t c;
        utf8proc_uint8_t *s = (utf8proc_uint8_t *) string->string;
        size_t len = string->bytes;

        size_t outlen = 0;
        char *result = value_string_alloc(ty, 4 * string->bytes);

        while (len > 0) {
                int n = max(1, utf8proc_iterate(s, len, &c));
                s += n;
                len -= n;
                c = utf8proc_toupper(c);
                outlen += utf8proc_encode_char(c, (utf8proc_uint8_t *)result + outlen);
        }

        return STRING(result, outlen);
}

static Value
string_pad_left(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.padLeft()";

        CHECK_ARGC(1, 2);

        int64_t width = INT_ARG(0);

        int string_len = stringwidth(string->string, string->bytes);
        if (string_len >= width)
                return *string;

        char const *pad;
        int pad_bytes;
        int pad_len;

        if (argc == 1) {
                pad = " ";
                pad_bytes = pad_len = 1;
        } else {
                if (ARG(1).type != VALUE_STRING)
                        zP("the second argument to str.padLeft() must be a string");
                pad = ARG(1).string;
                pad_bytes = ARG(1).bytes;
                stringcount(pad, pad_bytes, -1);
                pad_len = outpos.graphemes;
        }

        int n = (width - string_len) / pad_len + 1;
        char *result = value_string_alloc(ty, string->bytes + pad_bytes * n);

        int current = 0;
        int bytes = 0;
        while (current + pad_len <= width - string_len) {
                memcpy(result + bytes, pad, pad_bytes);
                current += pad_len;
                bytes += pad_bytes;
        }

        if (current != width - string_len) {
                stringcount(pad, pad_bytes, width - string_len - current);
                memcpy(result + bytes, pad, outpos.bytes);
                bytes += outpos.bytes;
        }

        memcpy(result + bytes, string->string, string->bytes);
        bytes += string->bytes;

        return STRING(result, bytes);
}

static Value
string_pad_right(Ty *ty, Value *string, int argc, Value *kwargs)
{
        char const *_name__ = "String.padRight()";

        CHECK_ARGC(1, 2);

        int64_t width = INT_ARG(0);

        int current = stringwidth(string->string, string->bytes);
        if (current >= width)
                return *string;

        char const *pad;
        int pad_bytes;
        int pad_len;

        if (argc == 1) {
                pad = " ";
                pad_bytes = pad_len = 1;
        } else {
                if (ARG(1).type != VALUE_STRING)
                        zP("the second argument to str.padRight() must be a string");
                pad = ARG(1).string;
                pad_bytes = ARG(1).bytes;
                stringcount(pad, pad_bytes, -1);
                pad_len = outpos.graphemes;
        }

        int n = (width - current) / pad_len + 1;
        char *result = value_string_alloc(ty, string->bytes + pad_bytes * n);
        int bytes = string->bytes;
        memcpy(result, string->string, bytes);

        while (current + pad_len <= width) {
                memcpy(result + bytes, pad, pad_bytes);
                current += pad_len;
                bytes += pad_bytes;
        }

        if (current != width) {
                stringcount(pad, pad_bytes, width - current);
                memcpy(result + bytes, pad, outpos.bytes);
                bytes += outpos.bytes;
        }

        return STRING(result, bytes);
}

static Value
string_cstr(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("String.cstr() expects 0 arguments but got %d", argc);

        return vSzs(string->string, string->bytes);
}

static Value
string_ptr(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("String.ptr() expects 0 arguments but got %d", argc);

        return PTR((void *)string->string);
}

static Value
string_clone(Ty *ty, Value *string, int argc, Value *kwargs)
{
        if (argc != 0) {
                zP("String.clone(): expected 0 arguments but got %d", argc);
        }

        return vSs(string->string, string->bytes);
}

DEFINE_METHOD_TABLE(
        { .name = "bsearch",   .func = string_bsearch    },
        { .name = "bslice",    .func = string_bslice     },
        { .name = "byte",      .func = string_byte       },
        { .name = "bytes",     .func = string_bytes      },
        { .name = "char",      .func = string_char       },
        { .name = "chars",     .func = string_chars      },
        { .name = "clone",     .func = string_clone      },
        { .name = "comb",      .func = string_comb       },
        { .name = "contains?", .func = string_contains   },
        { .name = "count",     .func = string_count      },
        { .name = "cstr",      .func = string_cstr       },
        { .name = "len",       .func = string_length     },
        { .name = "lines",     .func = string_lines      },
        { .name = "lower",     .func = string_lower      },
        { .name = "match!",    .func = string_match      },
        { .name = "match?",    .func = string_is_match   },
        { .name = "matches",   .func = string_matches    },
        { .name = "padLeft",   .func = string_pad_left   },
        { .name = "padRight",  .func = string_pad_right  },
        { .name = "ptr",       .func = string_ptr        },
        { .name = "repeat",    .func = string_repeat     },
        { .name = "replace",   .func = string_replace    },
        { .name = "search",    .func = string_search     },
        { .name = "searchAll", .func = string_search_all },
        { .name = "size",      .func = string_size       },
        { .name = "slice",     .func = string_slice      },
        { .name = "split",     .func = string_split      },
        { .name = "sub",       .func = string_replace    },
        { .name = "upper",     .func = string_upper      },
        { .name = "words",     .func = string_words      },
);

DEFINE_METHOD_LOOKUP(string)
DEFINE_METHOD_TABLE_BUILDER(string)
DEFINE_METHOD_COMPLETER(string)

/* vim: set sw=8 sts=8 expandtab: */
