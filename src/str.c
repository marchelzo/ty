#include <string.h>

#include <utf8proc.h>

#include "utf8.h"
#include "value.h"
#include "util.h"
#include "vm.h"

static struct stringpos limitpos;
static struct stringpos outpos;

inline static void
stringcount(char const *s, int byte_lim, int grapheme_lim)
{
        limitpos.bytes = byte_lim;
        limitpos.graphemes = grapheme_lim;
        utf8_stringcount(s, byte_lim, &outpos, &limitpos);
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
                                goto next;
                        }
                }

                return big;

next:
                ++big;
                --blen;
        }

        return NULL;

}

static struct value
string_length(struct value *string, value_vector *args)
{
        if (args->count != 0)
                vm_panic("str.len() expects no arguments but got %zu", args->count);

        stringcount(string->string, string->bytes, -1);

        return INTEGER(outpos.graphemes);
}

static struct value
string_slice(struct value *string, value_vector *args)
{
        if (args->count == 0 || args->count > 2)
                vm_panic("str.slice() expects 1 or 2 arguments but got %zu", args->count);

        struct value start = args->items[0];

        if (start.type != VALUE_INTEGER)
                vm_panic("non-integer passed as first argument to str.slice()");

        char const *s = string->string;
        int i = start.integer;
        int n;

        if (args->count == 2) {
                struct value len = args->items[1];
                if (len.type != VALUE_INTEGER)
                        vm_panic("non-integer passed as second argument to str.slice()");
                if (len.integer < 0)
                        vm_panic("negative integer passed as second argument to str.slice()");
                n = len.integer;
        } else {
                n = -1;
        }

        stringcount(s, string->bytes, -1);

        if (i < 0)
                i += outpos.graphemes;
                
        if (i < 0 || i > outpos.graphemes)
                return NIL;
        
        stringcount(s, string->bytes, i);

        i = outpos.bytes;

        stringcount(s + i, limitpos.bytes - outpos.bytes, n);

        return STRING_VIEW(*string, i, outpos.bytes);
}

static struct value
string_search(struct value *string, value_vector *args)
{
        if (args->count != 1 && args->count != 2)
                vm_panic("str.search() expects 1 or 2 arguments but got %zu", args->count);

        struct value pattern = args->items[0];

        if (pattern.type != VALUE_STRING && pattern.type != VALUE_REGEX)
                vm_panic("the pattern argument to str.search() must be a string or a regex");

        int offset;
        if (args->count == 1)
                offset = 0;
        else if (args->items[1].type == VALUE_INTEGER)
                offset = args->items[1].integer;
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
                pcre *re = pattern.regex;
                int rc;
                int out[3];

                rc = pcre_exec(re, NULL, s, bytes, 0, 0, out, 3);

                if (rc == -1)
                        return NIL;

                if (rc < -1)
                        vm_panic("error executing regular expression");

                n = out[0];
        }

        stringcount(s, n, -1);

        return INTEGER(offset + outpos.graphemes);
}

static struct value
string_split(struct value *string, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the split method on strings expects 1 argument but got %zu", args->count);

        struct value pattern = args->items[0];

        if (pattern.type != VALUE_REGEX && pattern.type != VALUE_STRING)
                vm_panic("invalid argument to the split method on string");

        struct value result = ARRAY(value_array_new());
        NOGC(result.array);

        char const *s = string->string;
        int len = string->bytes;
        if (pattern.type == VALUE_STRING) {
                char const *p = pattern.string;
                int n = pattern.bytes;

                if (n == 0)
                        goto end;

                int i = 0;
                while (i < len && is_prefix(s + i, len - i, p, n))
                        i += n;
                
                while (i < len) {

                        struct value str = STRING_VIEW(*string, i, 0);

                        while (i < len && !is_prefix(s + i, len - i, p, n)) {
                                ++str.bytes;
                                ++i;
                        }

                        value_array_push(result.array, str);

                        while (i < len && is_prefix(s + i, len - i, p, n))
                                i += n;
                }
        } else {
                pcre *re = pattern.regex;
                int len = string->bytes;
                int start = 0;
                int out[3];

                while (start < len) {
                        if (pcre_exec(re, NULL, s, len, start, 0, out, 3) != 1)
                                out[0] = out[1] = len;

                        if (out[0] == out[1] && out[1] != len) {
                                ++out[0];
                                ++out[1];
                        }

                        int n = out[0] - start;

                        if (n > 0)
                                value_array_push(result.array, STRING_VIEW(*string, start, n));

                        start = out[1];
                }
        }

end:
        OKGC(result.array);
        return result;
}

static struct value
string_replace(struct value *string, value_vector *args)
{
        static vec(char) chars;

        if (args->count != 2)
                vm_panic("the replace method on strings expects 2 arguments but got %zu", args->count);

        struct value pattern = args->items[0];
        struct value replacement = args->items[1];

        if (pattern.type != VALUE_REGEX && pattern.type != VALUE_STRING)
                vm_panic("the pattern argument to string's replace method must be a regex or a string");

        if (replacement.type != VALUE_STRING && !CALLABLE(replacement))
                vm_panic("the replacement argument to string's replace method must be callable or a string");

        chars.count = 0;

        char const *s = string->string;

        if (pattern.type == VALUE_STRING) {

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
                pcre *re = pattern.regex;
                char const *r = replacement.string;
                int len = string->bytes;
                int start = 0;
                int out[3];

                while (pcre_exec(re, NULL, s, len, start, 0, out, 3) == 1) {

                        vec_push_n(chars, s + start, out[0] - start);

                        vec_push_n(chars, r, replacement.bytes);

                        start = out[1];
                }

                vec_push_n(chars, s + start, len - start);

        } else {
                pcre *re = pattern.regex;
                int len = string->bytes;
                int start = 0;
                int out[30];
                int rc;

                while ((rc = pcre_exec(re, NULL, s, len, start, 0, out, 30)) > 0) {

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

                        struct value repstr = vm_eval_function(&replacement, &match);
                        if (repstr.type != VALUE_STRING)
                                vm_panic("non-string returned by the replacement function passed to string's replace method");

                        OKGC(match.array);

                        vec_push_n(chars, repstr.string, repstr.bytes);

                        start = out[1];
                }

                vec_push_n(chars, s + start, len - start);
        }

        return STRING_CLONE(chars.items, chars.count);
}

static struct value
string_is_match(struct value *string, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the match? method on strings expects 1 argument but got %zu", args->count);

        struct value pattern = args->items[0];

        if (pattern.type != VALUE_REGEX)
                vm_panic("non-regex passed to the match? method on string");

        int len = string->bytes;
        int rc;

        rc = pcre_exec(
                pattern.regex,
                NULL,
                string->string,
                len,
                0,
                0,
                NULL,
                0
        );

        if (rc < -1)
                vm_panic("error while executing regular expression");

        return BOOLEAN(rc != -1);
}

static struct value
string_match(struct value *string, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the match method on strings expects 1 argument but got %zu", args->count);

        struct value pattern = args->items[0];

        if (pattern.type != VALUE_REGEX)
                vm_panic("non-regex passed to the match method on string");

        static int ovec[30];
        int len = string->bytes;
        int rc;

        rc = pcre_exec(
                pattern.regex,
                NULL,
                string->string,
                len,
                0,
                0,
                ovec,
                30
        );

        if (rc < -1)
                vm_panic("error while executing regular expression");

        if (rc == -1)
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
string_matches(struct value *string, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the matches method on strings expects 1 argument but got %zu", args->count);

        struct value pattern = args->items[0];

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
                        pattern.regex,
                        pattern.extra,
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
                                value_array_push(match.array, STRING_VIEW(*string, ovec[j], ovec[j + 1] - ovec[j]));

                        OKGC(match.array);

                        value_array_push(result.array, match);
                }

                s += ovec[1];
                offset += ovec[1];
                len -= ovec[1];
        }

        if (rc < -1)
                vm_panic("error while executing regular expression");

        return result;
}

static struct value
string_byte(struct value *string, value_vector *args)
{
        if (args->count != 1)
                vm_panic("str.byte() expects 1 argument but got %zu", args->count);

        struct value i = args->items[0];

        if (i.type != VALUE_INTEGER)
                vm_panic("non-integer passed to str.byte()");

        if (i.integer < 0)
                i.integer += string->bytes;

        if (i.integer < 0 || i.integer >= string->bytes)
                return NIL; /* TODO: maybe panic */

        return INTEGER(string->string[i.integer]);
}

static struct value
string_char(struct value *string, value_vector *args)
{
        if (args->count != 1)
                vm_panic("the char method on strings expects 1 argument but got %zu", args->count);

        struct value i = args->items[0];

        if (i.type != VALUE_INTEGER)
                vm_panic("non-integer passed to the char method on string");

        if (i.integer < 0)
                i.integer += utf8_charcount(string->string, string->bytes);


        stringcount(string->string, string->bytes, i.integer);

        if (outpos.graphemes != i.integer)
                return NIL;

        int offset = outpos.bytes;

        stringcount(string->string + offset, string->bytes - offset, 1);

        if (outpos.graphemes != 1)
                return NIL;

        return STRING_VIEW(*string, offset, outpos.bytes);
}

static struct value
string_chars(struct value *string, value_vector *args)
{
        if (args->count != 0)
                vm_panic("str.chars() expects no arguments but got %zu", args->count);

        struct value result = ARRAY(value_array_new());
        NOGC(result.array);

        int i = 0;
        int n = string->bytes;

        while (n > 0) {
                stringcount(string->string + i, n, 1);
                value_array_push(result.array, STRING_VIEW(*string, i, outpos.bytes));
                i += outpos.bytes;
                n -= outpos.bytes;
        }

        OKGC(result.array);

        return result;
}

static struct value
string_lower(struct value *string, value_vector *args)
{
        if (args->count != 0)
                vm_panic("str.lower() expects no arguments but got %zu", args->count);

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

        return STRING(result, outlen, result);
}

static struct value
string_upper(struct value *string, value_vector *args)
{
        if (args->count != 0)
                vm_panic("str.upper() expects no arguments but got %zu", args->count);

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

        return STRING(result, outlen, result);
}

static struct value
string_pad_left(struct value *string, value_vector *args)
{
        if (args->count != 1 && args->count != 2)
                vm_panic("str.padLeft() expects 1 or 2 arguments but got %zu", args->count);

        struct value len = args->items[0];
        if (len.type != VALUE_INTEGER)
                vm_panic("the first argument to str.padLeft() must be an integer");

        stringcount(string->string, string->bytes, -1);
        int string_len = outpos.graphemes;

        if (string_len >= len.integer)
                return *string;

        char const *pad;
        int pad_bytes;
        int pad_len;

        if (args->count == 1) {
                pad = " ";
                pad_bytes = pad_len = 1;
        } else {
                if (args->items[1].type != VALUE_STRING)
                        vm_panic("the second argument to str.padLeft() must be a string");
                pad = args->items[1].string;
                pad_bytes = args->items[1].bytes;
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

        return STRING(result, bytes, result);
}

static struct value
string_pad_right(struct value *string, value_vector *args)
{
        if (args->count != 1 && args->count != 2)
                vm_panic("str.padRight() expects 1 or 2 arguments but got %zu", args->count);

        struct value len = args->items[0];
        if (len.type != VALUE_INTEGER)
                vm_panic("the first argument to str.padRight() must be an integer");

        stringcount(string->string, string->bytes, -1);
        int current = outpos.graphemes;

        if (current >= len.integer)
                return *string;

        char const *pad;
        int pad_bytes;
        int pad_len;

        if (args->count == 1) {
                pad = " ";
                pad_bytes = pad_len = 1;
        } else {
                if (args->items[1].type != VALUE_STRING)
                        vm_panic("the second argument to str.padRight() must be a string");
                pad = args->items[1].string;
                pad_bytes = args->items[1].bytes;
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

        return STRING(result, bytes, result);
}

DEFINE_METHOD_TABLE(
        { .name = "byte",      .func = string_byte      },
        { .name = "char",      .func = string_char      },
        { .name = "chars",     .func = string_chars     },
        { .name = "len",       .func = string_length    },
        { .name = "lower",     .func = string_lower     },
        { .name = "match!",    .func = string_match     },
        { .name = "match?",    .func = string_is_match  },
        { .name = "matches",   .func = string_matches   },
        { .name = "padLeft",   .func = string_pad_left  },
        { .name = "padRight",  .func = string_pad_right },
        { .name = "replace",   .func = string_replace   },
        { .name = "search",    .func = string_search    },
        { .name = "slice",     .func = string_slice     },
        { .name = "split",     .func = string_split     },
        { .name = "upper",     .func = string_upper     },
);

DEFINE_METHOD_LOOKUP(string)
