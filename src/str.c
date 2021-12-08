#include <string.h>

#include <utf8proc.h>
#include <ctype.h>

#include "utf8.h"
#include "value.h"
#include "util.h"
#include "gc.h"
#include "vm.h"
#include "token.h"
#include "functions.h"

static struct stringpos limitpos;
static struct stringpos outpos;

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
is_prefix(char const *big, int blen, char const *small, int slen)
{
        return (blen >= slen) && (memcmp(big, small, slen) == 0);
}

inline static char const *
sfind(char const *big, int blen, char const *small, int slen)
{
        register int i;

        while (blen >= slen) {
                for (i = 0; i < slen; ++i) {
                        if (big[i] != small[i]) {
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

static struct value
string_length(struct value *string, int argc)
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
                        if (m == -1)
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

static struct value
string_chars(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("str.chars() expects no arguments but got %d", argc);

        char const *s = string->string;
        int size = string->bytes;
        int offset = 0;
        int state = 0;

        struct array *r = value_array_new();
        NOGC(r);

        while (size > 0) {
                int codepoint;
                int n = utf8proc_iterate(s + offset, size, &codepoint);
                if (n == -1) {
                        size -= 1;
                        offset += 1;
                        continue;
                } else while (n < size) {
                        int next;
                        int m = utf8proc_iterate(s + offset + n, size - n, &next);
                        if (m == -1)
                                break;
                        if (utf8proc_grapheme_break_stateful(codepoint, next, &state))
                                break;
                        n += m;
                }
                value_array_push(r, STRING_VIEW(*string, offset, n));
                size -= n;
                offset += n;
        }

        OKGC(r);

        return ARRAY(r);
}

static struct value
string_size(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("str.size() expects no arguments but got %d", argc);

        return INTEGER(string->bytes);
}

static struct value
string_slice(struct value *string, int argc)
{
        if (argc == 0 || argc > 2)
                vm_panic("str.slice() expects 1 or 2 arguments but got %d", argc);

        struct value start = ARG(0);

        if (start.type != VALUE_INTEGER)
                vm_panic("non-integer passed as first argument to str.slice()");

        char const *s = string->string;
        int i = start.integer;
        int n;

        stringcount(s, string->bytes, -1);

        if (argc == 2) {
                struct value len = ARG(1);
                if (len.type != VALUE_INTEGER)
                        vm_panic("non-integer passed as second argument to str.slice()");
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

static struct value
string_search(struct value *string, int argc)
{
        if (argc != 1 && argc != 2)
                vm_panic("str.search() expects 1 or 2 arguments but got %d", argc);

        struct value pattern = ARG(0);

        if (pattern.type != VALUE_STRING && pattern.type != VALUE_REGEX)
                vm_panic("the pattern argument to str.search() must be a string or a regex");

        int offset;
        if (argc == 1)
                offset = 0;
        else if (ARG(1).type == VALUE_INTEGER)
                offset = ARG(1).integer;
        else
                vm_panic("the second argument to str.search() must be an integer");

        if (offset < 0) {
                stringcount(string->string, string->bytes, -1);
                offset += outpos.graphemes;
        }

        if (offset < 0)
                vm_panic("invalid offset passed to str.search()");

        stringcount(string->string, string->bytes, offset);
        if (outpos.graphemes != offset)
                return NIL;

        char const *s = string->string + outpos.bytes;
        int bytes = string->bytes - outpos.bytes;

        int n;

        if (pattern.type == VALUE_STRING) {
                char const *match = memmem(s, bytes, pattern.string, pattern.bytes);

                if (match == NULL)
                        return NIL;

                n = match - s;
        } else {
                pcre *re = pattern.regex->pcre;
                int rc;
                int out[3];

                rc = pcre_exec(re, pattern.regex->extra, s, bytes, 0, 0, out, 3);

                if (rc == -1 || rc == -2)
                        return NIL;

                if (rc < -1)
                        vm_panic("error executing regular expression: %d", rc);

                n = out[0];
        }

        stringcount(s, n, -1);

        return INTEGER(offset + outpos.graphemes);
}

static struct value
string_contains(struct value *string, int argc)
{
        if (argc != 1 && argc != 2)
                vm_panic("str.contains?() expects 1 or 2 arguments but got %d", argc);

        struct value pattern = ARG(0);

        if (pattern.type != VALUE_STRING)
                vm_panic("the pattern argument to str.contains?() must be a string");

        int offset;
        if (argc == 1)
                offset = 0;
        else if (ARG(1).type == VALUE_INTEGER)
                offset = ARG(1).integer;
        else
                vm_panic("the second argument to str.contains?() must be an integer");

        if (offset < 0) {
                stringcount(string->string, string->bytes, -1);
                offset += outpos.graphemes;
        }

        if (offset < 0)
                vm_panic("invalid offset passed to str.contains?()");

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

static struct value
string_words(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("the words method on strings expects no arguments but got %d", argc);

        gc_push(string);

        struct array *a = value_array_new();
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

                struct value str = STRING_VIEW(*string, i, 0);

                do {
                        str.bytes += n;
                        i += n;
                        n = utf8proc_iterate(s + i, len - i, &cp);
                        c = utf8proc_category(cp);
                } while (i < len && !isspace(s[i]) && c != UTF8PROC_CATEGORY_ZS && c != UTF8PROC_CATEGORY_ZL && c != UTF8PROC_CATEGORY_ZP);

                value_array_push(a, str);
        }
End:
        gc_pop();
        OKGC(a);

        return ARRAY(a);
}

static struct value
string_lines(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("the lines method on strings expects no arguments but got %d", argc);

        gc_push(string);

        struct array *a = value_array_new();
        NOGC(a);

        int i = 0;
        int len = string->bytes;
        char const *s = string->string;

        if (len == 0) {
                value_array_push(a, *string);
                goto End;
        }

        while (i < len) {
                struct value str = STRING_VIEW(*string, i, 0);

                while (i < len && s[i] != '\n' && !is_prefix(s + i, len - i, "\r\n", 2)) {
                        ++str.bytes;
                        ++i;
                }

                value_array_push(a, str);

                if (i < len)
                        i += 1 + (s[i] == '\r');
        }
End:
        gc_pop();
        OKGC(a);

        return ARRAY(a);
}

static struct value
string_split(struct value *string, int argc)
{
        if (argc != 1)
                vm_panic("the split method on strings expects 1 argument but got %d", argc);

        char const *s = string->string;
        int len = string->bytes;
        gc_push(string);

        struct value pattern = ARG(0);

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
                struct array *parts = value_array_new();
                NOGC(parts);
                value_array_push(parts, STRING_VIEW(*string, 0, outpos.bytes));
                value_array_push(parts, STRING_VIEW(*string, outpos.bytes, len - outpos.bytes));
                OKGC(parts);
                gc_pop();
                return ARRAY(parts);
        }

        if (pattern.type != VALUE_REGEX && pattern.type != VALUE_STRING)
                vm_panic("invalid argument to the split method on string");

        struct value result = ARRAY(value_array_new());
        NOGC(result.array);

        if (pattern.type == VALUE_STRING) {
                char const *p = pattern.string;
                int n = pattern.bytes;

                if (n == 0)
                        goto End;

                int i = 0;
                while (i < len) {

                        struct value str = STRING_VIEW(*string, i, 0);

                        while (i < len && !is_prefix(s + i, len - i, p, n)) {
                                ++str.bytes;
                                ++i;
                        }

                        value_array_push(result.array, str);

                        i += n;
                }

                if (i == len)
                        value_array_push(result.array, STRING_EMPTY);
        } else {
                pcre *re = pattern.regex->pcre;
                int len = string->bytes;
                int start = 0;
                int out[3];

                while (start < len) {
                        if (pcre_exec(re, pattern.regex->extra, s, len, start, 0, out, 3) != 1) {
                                out[0] = len;
                                out[1] = len + 1;
                        }

                        if (out[0] == out[1] && out[0] == start) {
                                out[0] = ++out[1];
                        }

                        int n = out[0] - start;
                        value_array_push(result.array, STRING_VIEW(*string, start, n));
                        start = out[1];
                }

                if (start == len)
                        value_array_push(result.array, STRING_EMPTY);
        }

End:
        gc_pop();
        OKGC(result.array);
        return result;
}

static struct value
string_count(struct value *string, int argc)
{
        if (argc != 1) {
                vm_panic("the count method on strings expects exactly 1 argument");
        }

        struct value pattern = ARG(0);
        int count = 0;

        if (pattern.type == VALUE_STRING) {
                char const *s = string->string;
                char const *p = pattern.string;
                int len = string->bytes;
                int plen = pattern.bytes;
                char const *m;

                if (plen > 0) while ((m = sfind(s, len, p, plen)) != NULL) {
                        len -= (m - s + plen);
                        s = m + plen;
                        count += 1;
                }
        } else if (pattern.type == VALUE_REGEX) {
                int ovec[30];
                char const *s = string->string;
                int len = string->bytes;
                int offset = 0;
                int rc;

                while ((rc = pcre_exec(
                                pattern.regex->pcre,
                                pattern.regex->extra,
                                s,
                                len,
                                0,
                                0,
                                ovec,
                                30
                        )) > 0) {
                        count += 1;
                        s += ovec[1];
                        offset += ovec[1];
                        len -= ovec[1];
                }
        } else {
                vm_panic("the argument to string.count() must be a string or a regex");
        }

        return INTEGER(count);
}

/* copy + paste of replace, can fix later */
static struct value
string_comb(struct value *string, int argc)
{
        vec(char) chars;
        size_t const header = offsetof(struct alloc, data);
        // TODO: yikes

        vec_init(chars);
        vec_reserve(chars, header);
        chars.count = chars.capacity;

        if (argc != 1)
                vm_panic("the comb method on strings expects 1 arguments but got %d", argc);

        struct value pattern = ARG(0);
        struct value replacement = STRING_EMPTY;

        if (pattern.type != VALUE_REGEX && pattern.type != VALUE_STRING)
                vm_panic("the pattern argument to string's comb method must be a regex or a string");

        char const *s = string->string;

        if (pattern.type == VALUE_STRING) {

                char const *p = pattern.string;
                char const *r = replacement.string;

                int len = string->bytes;
                int plen = pattern.bytes;
                char const *m;

                while ((m = sfind(s, len, p, plen)) != NULL) {
                        vec_push_n(chars, s, m - s);

                        vec_push_n(chars, r, replacement.bytes);

                        len -= (m - s + plen);
                        s = m + plen;
                }

                vec_push_n(chars, s, len);
        } else {
                pcre *re = pattern.regex->pcre;
                char const *r = replacement.string;
                int len = string->bytes;
                int start = 0;
                int out[3];

                while (pcre_exec(re, pattern.regex->extra, s, len, start, 0, out, 3) == 1) {

                        vec_push_n(chars, s + start, out[0] - start);

                        vec_push_n(chars, r, replacement.bytes);

                        start = out[1];
                }

                vec_push_n(chars, s + start, len - start);

        }

        struct alloc *a = (void *)chars.items;
        a->type = GC_STRING;
        a->mark = GC_NONE;

        return STRING(chars.items + header, chars.count - header);
}

static struct value
string_replace(struct value *string, int argc)
{
        vec(char) chars;
        size_t const header = offsetof(struct alloc, data);
        // TODO: yikes

        vec_init(chars);
        vec_reserve(chars, header);
        chars.count = chars.capacity;

        if (argc != 2)
                vm_panic("the replace method on strings expects 2 arguments but got %d", argc);

        struct value pattern = ARG(0);
        struct value replacement = ARG(1);

        if (pattern.type != VALUE_REGEX && pattern.type != VALUE_STRING)
                vm_panic("the pattern argument to string's replace method must be a regex or a string");

        char const *s = string->string;

        if (pattern.type == VALUE_STRING) {

                vm_push(&replacement);
                replacement = builtin_str(1);
                vm_pop();

                if (replacement.type != VALUE_STRING)
                        vm_panic("non-string replacement passed to string's replace method with a string pattern");

                char const *p = pattern.string;
                char const *r = replacement.string;

                int len = string->bytes;
                int plen = pattern.bytes;
                char const *m;

                while ((m = sfind(s, len, p, plen)) != NULL) {
                        vec_push_n(chars, s, m - s);

                        vec_push_n(chars, r, replacement.bytes);

                        len -= (m - s + plen);
                        s = m + plen;
                }

                vec_push_n(chars, s, len);
        } else if (replacement.type == VALUE_STRING) {
                pcre *re = pattern.regex->pcre;
                char const *r = replacement.string;
                int len = string->bytes;
                int start = 0;
                int out[3];

                while (pcre_exec(re, pattern.regex->extra, s, len, start, 0, out, 3) == 1) {

                        vec_push_n(chars, s + start, out[0] - start);

                        vec_push_n(chars, r, replacement.bytes);

                        start = out[1];
                }

                vec_push_n(chars, s + start, len - start);

        } else if (CALLABLE(replacement)) {
                pcre *re = pattern.regex->pcre;
                int len = string->bytes;
                int start = 0;
                int out[30];
                int rc;

                while ((rc = pcre_exec(re, pattern.regex->extra, s, len, start, 0, out, 30)) > 0) {

                        vec_push_n(chars, s + start, out[0] - start);

                        struct value match;

                        if (rc == 1) {
                                match = STRING_VIEW(*string, out[0], out[1] - out[0]);
                        } else {
                                match = ARRAY(value_array_new());
                                NOGC(match.array);

                                int j = 0;
                                for (int i = 0; i < rc; ++i, j += 2)
                                        vec_push(*match.array, STRING_VIEW(*string, out[j], out[j + 1] - out[j]));
                        }

                        struct value repstr = vm_eval_function(&replacement, &match, NULL);
                        vm_push(&repstr);
                        repstr = builtin_str(1);
                        vm_pop();
                        if (repstr.type != VALUE_STRING)
                                vm_panic("non-string returned by the replacement function passed to string's replace method");

                        if (match.type == VALUE_ARRAY)
                            OKGC(match.array);

                        vec_push_n(chars, repstr.string, repstr.bytes);

                        start = out[1];
                }

                vec_push_n(chars, s + start, len - start);
        } else {
                vm_panic("invalid replacement passed to replace method on string");
        }

        struct alloc *a = (void *)chars.items;
        a->type = GC_STRING;
        a->mark = GC_NONE;
        return STRING(chars.items + header, chars.count - header);
}

static struct value
string_is_match(struct value *string, int argc)
{
        if (argc != 1)
                vm_panic("the match? method on strings expects 1 argument but got %d", argc);

        struct value pattern = ARG(0);

        if (pattern.type != VALUE_REGEX)
                vm_panic("non-regex passed to the match? method on string");

        int len = string->bytes;
        int rc;

        rc = pcre_exec(
                pattern.regex->pcre,
                pattern.regex->extra,
                string->string,
                len,
                0,
                0,
                NULL,
                0
        );

        if (rc < -2)
                vm_panic("error while executing regular expression: %d", rc);

        return BOOLEAN(rc > -1);
}

static struct value
string_match(struct value *string, int argc)
{
        if (argc != 1)
                vm_panic("the match method on strings expects 1 argument but got %d", argc);

        struct value pattern = ARG(0);

        if (pattern.type != VALUE_REGEX)
                vm_panic("non-regex passed to the match method on string");

        static int ovec[30];
        int len = string->bytes;
        int rc;

        rc = pcre_exec(
                pattern.regex->pcre,
                pattern.regex->extra,
                string->string,
                len,
                0,
                0,
                ovec,
                30
        );

        if (rc < -2)
                vm_panic("error while executing regular expression: %d", rc);

        if (rc < 0)
                return NIL;

        struct value match;

        if (rc == 1) {
                match = STRING_VIEW(*string, ovec[0], ovec[1] - ovec[0]);
        } else {
                match = ARRAY(value_array_new());
                NOGC(match.array);
                value_array_reserve(match.array, rc);

                int j = 0;
                for (int i = 0; i < rc; ++i, j += 2)
                        vec_push(*match.array, STRING_VIEW(*string, ovec[j], ovec[j + 1] - ovec[j]));

                OKGC(match.array);
        }

        return match;
}

static struct value
string_matches(struct value *string, int argc)
{
        if (argc != 1)
                vm_panic("the matches method on strings expects 1 argument but got %d", argc);

        struct value pattern = ARG(0);

        if (pattern.type != VALUE_REGEX)
                vm_panic("non-regex passed to the matches method on string");

        struct value result = ARRAY(value_array_new());
        gc_push(&result);

        static int ovec[30];
        char const *s = string->string;
        int len = string->bytes;
        int offset = 0;
        int rc;

        while ((rc = pcre_exec(
                        pattern.regex->pcre,
                        pattern.regex->extra,
                        s,
                        len,
                        0,
                        0,
                        ovec,
                        30
                )) > 0) {

                if (rc == 1) {
                        value_array_push(result.array, STRING_VIEW(*string, offset + ovec[0], ovec[1] - ovec[0]));
                } else {
                        struct value match = ARRAY(value_array_new());
                        NOGC(match.array);

                        value_array_reserve(match.array, rc);

                        int j = 0;
                        for (int i = 0; i < rc; ++i, j += 2)
                                value_array_push(match.array, STRING_VIEW(*string, ovec[j] + offset, ovec[j + 1] - ovec[j]));

                        value_array_push(result.array, match);
                        OKGC(match.array);
                }

                s += ovec[1];
                offset += ovec[1];
                len -= ovec[1];
        }

        if (rc < -2)
                vm_panic("error while executing regular expression: %d", rc);

        gc_pop();

        return result;
}

static struct value
string_byte(struct value *string, int argc)
{
        if (argc != 1)
                vm_panic("str.byte() expects 1 argument but got %d", argc);

        struct value i = ARG(0);

        if (i.type != VALUE_INTEGER)
                vm_panic("non-integer passed to str.byte()");

        if (i.integer < 0)
                i.integer += string->bytes;

        if (i.integer < 0 || i.integer >= string->bytes)
                return NIL; /* TODO: maybe panic */

        return INTEGER((unsigned char)string->string[i.integer]);
}

static struct value
string_char(struct value *string, int argc)
{
        if (argc != 1)
                vm_panic("the char method on strings expects 1 argument but got %d", argc);

        struct value i = ARG(0);

        if (i.type != VALUE_INTEGER)
                vm_panic("non-integer passed to the char method on string");

        if (i.integer < 0)
                i.integer += string_length(string, 0).integer;

        int cp;
        int j = i.integer;
        int offset = 0;
        int n = utf8proc_iterate(string->string, string->bytes, &cp);

        while (offset < string->bytes && n > 0 && j --> 0) {
                offset += max(1, n);
                n = utf8proc_iterate(string->string + offset, string->bytes, &cp);
        }

        if (offset == string->bytes)
                return NIL;

        return STRING_VIEW(*string, offset, n);
}

static struct value
string_bytes(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("str.bytes() expects no arguments but got %d", argc);

        struct value result = ARRAY(value_array_new());
        NOGC(result.array);

        for (char const *c = string->string; *c != '\0'; ++c) {
                value_array_push(result.array, INTEGER((unsigned char)*c));
        }

        OKGC(result.array);

        return result;
}

static struct value
string_lower(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("str.lower() expects no arguments but got %d", argc);

        utf8proc_int32_t c;

        utf8proc_uint8_t *s = (utf8proc_uint8_t *) string->string;
        size_t len = string->bytes;

        size_t outlen = 0;
        char *result = value_string_alloc(4 * string->bytes);

        while (len > 0) {
                int n = utf8proc_iterate(s, len, &c);
                s += n;
                len -= n;
                c = utf8proc_tolower(c);
                outlen += utf8proc_encode_char(c, (utf8proc_uint8_t *)result + outlen);
        }

        return STRING(result, outlen);
}

static struct value
string_upper(struct value *string, int argc)
{
        if (argc != 0)
                vm_panic("str.upper() expects no arguments but got %d", argc);

        utf8proc_int32_t c;

        utf8proc_uint8_t *s = (utf8proc_uint8_t *) string->string;
        size_t len = string->bytes;

        size_t outlen = 0;
        char *result = value_string_alloc(4 * string->bytes);

        while (len > 0) {
                int n = utf8proc_iterate(s, len, &c);
                s += n;
                len -= n;
                c = utf8proc_toupper(c);
                outlen += utf8proc_encode_char(c, (utf8proc_uint8_t *)result + outlen);
        }

        return STRING(result, outlen);
}

static struct value
string_pad_left(struct value *string, int argc)
{
        if (argc != 1 && argc != 2)
                vm_panic("str.padLeft() expects 1 or 2 arguments but got %d", argc);

        struct value len = ARG(0);
        if (len.type != VALUE_INTEGER)
                vm_panic("the first argument to str.padLeft() must be an integer");

        int string_len = stringwidth(string->string, string->bytes);
        if (string_len >= len.integer)
                return *string;

        char const *pad;
        int pad_bytes;
        int pad_len;

        if (argc == 1) {
                pad = " ";
                pad_bytes = pad_len = 1;
        } else {
                if (ARG(1).type != VALUE_STRING)
                        vm_panic("the second argument to str.padLeft() must be a string");
                pad = ARG(1).string;
                pad_bytes = ARG(1).bytes;
                stringcount(pad, pad_bytes, -1);
                pad_len = outpos.graphemes;
        }

        int n = (len.integer - string_len) / pad_len + 1;
        char *result = value_string_alloc(string->bytes + pad_bytes * n);

        int current = 0;
        int bytes = 0;
        while (current + pad_len <= len.integer - string_len) {
                memcpy(result + bytes, pad, pad_bytes);
                current += pad_len;
                bytes += pad_bytes;
        }

        if (current != len.integer - string_len) {
                stringcount(pad, pad_bytes, len.integer - string_len - current);
                memcpy(result + bytes, pad, outpos.bytes);
                bytes += outpos.bytes;
        }

        memcpy(result + bytes, string->string, string->bytes);
        bytes += string->bytes;

        return STRING(result, bytes);
}

static struct value
string_pad_right(struct value *string, int argc)
{
        if (argc != 1 && argc != 2)
                vm_panic("str.padRight() expects 1 or 2 arguments but got %d", argc);

        struct value len = ARG(0);
        if (len.type != VALUE_INTEGER)
                vm_panic("the first argument to str.padRight() must be an integer");

        int current = stringwidth(string->string, string->bytes);
        if (current >= len.integer)
                return *string;

        char const *pad;
        int pad_bytes;
        int pad_len;

        if (argc == 1) {
                pad = " ";
                pad_bytes = pad_len = 1;
        } else {
                if (ARG(1).type != VALUE_STRING)
                        vm_panic("the second argument to str.padRight() must be a string");
                pad = ARG(1).string;
                pad_bytes = ARG(1).bytes;
                stringcount(pad, pad_bytes, -1);
                pad_len = outpos.graphemes;
        }

        int n = (len.integer - current) / pad_len + 1;
        char *result = value_string_alloc(string->bytes + pad_bytes * n);
        int bytes = string->bytes;
        memcpy(result, string->string, bytes);

        while (current + pad_len <= len.integer) {
                memcpy(result + bytes, pad, pad_bytes);
                current += pad_len;
                bytes += pad_bytes;
        }

        if (current != len.integer) {
                stringcount(pad, pad_bytes, len.integer - current);
                memcpy(result + bytes, pad, outpos.bytes);
                bytes += outpos.bytes;
        }

        return STRING(result, bytes);
}

DEFINE_METHOD_TABLE(
        { .name = "byte",      .func = string_byte      },
        { .name = "bytes",     .func = string_bytes     },
        { .name = "char",      .func = string_char      },
        { .name = "chars",     .func = string_chars     },
        { .name = "comb",      .func = string_comb      },
        { .name = "contains?", .func = string_contains  },
        { .name = "count",     .func = string_count     },
        { .name = "len",       .func = string_length    },
        { .name = "lines",     .func = string_lines     },
        { .name = "lower",     .func = string_lower     },
        { .name = "match!",    .func = string_match     },
        { .name = "match?",    .func = string_is_match  },
        { .name = "matches",   .func = string_matches   },
        { .name = "padLeft",   .func = string_pad_left  },
        { .name = "padRight",  .func = string_pad_right },
        { .name = "replace",   .func = string_replace   },
        { .name = "search",    .func = string_search    },
        { .name = "size",      .func = string_size      },
        { .name = "slice",     .func = string_slice     },
        { .name = "split",     .func = string_split     },
        { .name = "sub",       .func = string_replace   },
        { .name = "upper",     .func = string_upper     },
        { .name = "words",     .func = string_words     },
);

DEFINE_METHOD_LOOKUP(string)
DEFINE_METHOD_COMPLETER(string)
