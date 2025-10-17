#include <setjmp.h>
#include <ctype.h>
#include <stdlib.h>
#include <errno.h>
#include <utf8proc.h>

#include "test.h"
#include "value.h"
#include "dict.h"
#include "util.h"
#include "dtoa.h"
#include "itable.h"
#include "class.h"
#include "vec.h"
#include "vm.h"
#include "ty.h"

#define KW_DELIM(c) (strchr(" \n}],", c) != NULL)
#define FAIL longjmp(jb, 1)

static _Thread_local jmp_buf jb;
static _Thread_local char const *json;
static _Thread_local usize len;
static _Thread_local bool xd;

typedef byte_vector str;

static _Thread_local vec(void const *) Visiting;

inline static char
peek(void)
{
        return (len == 0) ? '\0' : json[0];
}

inline static char
peek1(void)
{
        return (len <= 1) ? '\0' : json[1];
}

inline static char
next(void)
{
        if (len <= 0)
                return '\0';
        --len;
        return *json++;
}

static Value
value(Ty *ty);

inline static void
space(void)
{
        while (isspace(peek())) next();
}

static Value
number(void)
{
        char numbuf[512];
        char const *num = json;
        bool integral = true;

        if (peek() == '-')
                next();

        if (!isdigit(peek()))
                FAIL;

        while (isdigit(peek()))
                next();

        if (peek() == '.') {
                integral = false;
                next();
                if (!isdigit(peek()))
                        FAIL;
                while (isdigit(peek()))
                        next();
        }

        if (peek() == 'e' || peek() == 'E') {
                integral = false;
                next();
                if (peek() == '-' || peek() == '+')
                        next();
                if (!isdigit(peek()))
                        FAIL;
                while (isdigit(peek()))
                        next();
        }

        int n = min(json - num, sizeof numbuf - 1);
        memcpy(numbuf, num, n);
        numbuf[n] = '\0';

        Value result;

        errno = 0;
        if (integral)
                result = INTEGER(strtoimax(num, NULL, 10));
        else
                result = REAL(strtod(num, NULL));

        if (errno != 0)
                FAIL;

        return result;
}

static Value
null(void)
{
        if (strncmp(json, "null", 4) != 0)
                FAIL;

        if (!KW_DELIM(json[4]))
                FAIL;

        json += 4;
        len -= 4;

        return NIL;
}

static Value
jtrue(void)
{
        if (strncmp(json, "true", 4) != 0)
                FAIL;

        if (!KW_DELIM(json[4]))
                FAIL;

        json += 4;
        len -= 4;

        return BOOLEAN(true);
}

static Value
jfalse(void)
{
        if (strncmp(json, "false", 5) != 0)
                FAIL;

        if (!KW_DELIM(json[5]))
                FAIL;

        json += 5;
        len -= 5;

        return BOOLEAN(false);
}

static u8 const xtable[256] = {
        ['0'] = 0, ['1'] = 1, ['2'] = 2, ['3'] = 3, ['4'] = 4,
        ['5'] = 5, ['6'] = 6, ['7'] = 7, ['8'] = 8, ['9'] = 9,

        ['A'] = 10, ['a'] = 10,
        ['B'] = 11, ['b'] = 11,
        ['C'] = 12, ['c'] = 12,
        ['D'] = 13, ['d'] = 13,
        ['E'] = 14, ['e'] = 14,
        ['F'] = 15, ['f'] = 15
};

inline static u16
next16x(Ty *ty)
{
        u8 b0 = xtable[(u8)next()];
        u8 b1 = xtable[(u8)next()];
        u8 b2 = xtable[(u8)next()];
        u8 b3 = xtable[(u8)next()];

        return (b3 << 0)
             | (b2 << 4)
             | (b1 << 8)
             | (b0 << 12);
}

inline static u8
next8x(Ty *ty)
{
        u8 b0 = xtable[(u8)next()];
        u8 b1 = xtable[(u8)next()];

        return (b1 << 0)
             | (b0 << 4);
}

static Value
string(Ty *ty)
{
        if (next() != '"')
                FAIL;

        vec(char) str = {0};

        char b[8] = {0};
        i32 cp;
        u16 lo;
        u16 hi;
        utf8proc_ssize_t n;

        while (peek() != '\0' && peek() != '"') {
                switch ((peek() == '\\') ? (next(), next()) : -1) {
                case 't':  xvP(str, '\t'); break;
                case 'f':  xvP(str, '\f'); break;
                case 'n':  xvP(str, '\n'); break;
                case 'r':  xvP(str, '\r'); break;
                case 'b':  xvP(str, '\b'); break;
                case '"':  xvP(str, '"');  break;
                case '/':  xvP(str, '/');  break;
                case '\\': xvP(str, '\\'); break;

                case 'x':
                        xvP(str, next8x(ty));
                        break;

                case 'u':
                        cp = next16x(ty);
                        if ((cp & 0xF800) == 0xD800) {
                                if (next() != '\\' || next() != 'u') {
                                        FAIL;
                                }

                                hi = cp;
                                lo = next16x(ty);

                                cp = 0x10000 + ((hi - 0xD800) << 10) + (lo - 0xDC00);
                        }
                        n = utf8proc_encode_char(cp, (u8 *)b);
                        xvPn(str, b, n);
                        break;

                default:
                        xvP(str, next());
                }
        }

        if (next() != '"')
                FAIL;

        n = str.count;

        if (n == 0)
                return STRING_NOGC(NULL, 0);

        char *s = value_string_alloc(ty, n);
        memcpy(s, str.items, n);

        free(str.items);

        return STRING(s, n);
}

static Value
array(Ty *ty)
{
        if (next() != '[')
                FAIL;

        Array *a = vA();

        while (peek() != '\0' && peek() != ']') {
                vvP(*a, value(ty));
                space();
                if (peek() != ']' && next() != ',')
                        FAIL;
        }

        if (next() != ']')
                FAIL;

        return ARRAY(a);
}

inline static Value
object_lol(Ty *ty)
{
        if (next() != '{')
                FAIL;

        Dict *obj = dict_new(ty);

        while (peek() != '\0' && peek() != '}') {
                space();
                Value key = string(ty);
                space();
                if (next() != ':')
                        FAIL;
                Value val = value(ty);
                dict_put_value(ty, obj, key, val);
                space();
                if (peek() != '}' && next() != ',')
                        FAIL;
        }

        if (next() != '}')
                FAIL;

        return DICT(obj);
}

inline static Value
object_xD(Ty *ty)
{
        if (next() != '{')
                FAIL;

        SCRATCH_SAVE();

        ValueVector keys   = {0};
        ValueVector values = {0};

        while (peek() != '\0' && peek() != '}') {
                space();

                Value key = string(ty);

                space();
                if (next() != ':') {
                        SCRATCH_RESTORE();
                        FAIL;
                }

                Value val = value(ty);

                space();
                if (peek() != '}' && next() != ',') {
                        SCRATCH_RESTORE();
                        FAIL;
                }

                svP(keys, key);
                svP(values, val);
        }

        if (next() != '}')
                FAIL;

        Value object = value_record(ty, vN(keys));

        for (u32 i = 0; i < vN(keys); ++i) {
                char const *key = TY_TMP_C_STR(v__(keys, i));
                object.ids[i]   = M_ID(key);
                object.items[i] = v__(values, i);
        }

        SCRATCH_RESTORE();

        return object;
}

static Value
object(Ty *ty)
{
        return xd ? object_xD(ty) : object_lol(ty);
}

static Value
value(Ty *ty)
{
        space();

        switch (peek()) {
        case '{': return object(ty);
        case '[': return array(ty);
        case '"': return string(ty);
        case 'n': return null();
        case 't': return jtrue();
        case 'f': return jfalse();
        case '-': case '0': case '1': case '2': case '3': case '4':
        case '5': case '6': case '7': case '8': case '9':
                return number();
        default: FAIL;
        }
}

inline static bool
visiting(void const *p)
{
        for (int i = 0; i < Visiting.count; ++i) {
                if (Visiting.items[i] == p) {
                        return true;
                }
        }

        return false;
}

inline static bool
try_visit(void const *p)
{
        if (visiting(p)) {
                return false;
        } else {
                xvP(Visiting, p);
                return true;
        }
}

static bool
encode(Ty *ty, Value const *v, str *out)
{
        if (v->type & VALUE_TAGGED) {
                Value val = *v;
                char const *tn = tags_name(ty, tags_first(ty, v->tags));

                val.tags = tags_pop(ty, v->tags);
                if (val.tags == 0) {
                        val.type &= ~VALUE_TAGGED;
                }

                dump((void *)out, "{\"type\":\"%s\",\"value\":", tn);

                if (!encode(ty, &val, out)) {
                        return false;
                }

                xvP(*out, '}');

                return true;
        }

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_NIL:
                xvPn(*out, "null", 4);
                break;
        case VALUE_TAG:
                dump((void *)out, "\"%s\"", tags_name(ty, v->tag));
                break;
        case VALUE_STRING:
                xvP(*out, '"');
                for (int i = 0; i < v->bytes; ++i) {
                        int n;
                        int32_t cp;
                        switch (v->str[i]) {
                        case '\t':
                                xvP(*out, '\\');
                                xvP(*out, 't');
                                break;
                        case '\n':
                                xvP(*out, '\\');
                                xvP(*out, 'n');
                                break;
                        case '\\':
                        case '"':
                                xvP(*out, '\\');
                        default:
                                if (((uint8_t)v->str[i]) > 127) {
                                        n = utf8proc_iterate((uint8_t *)&v->str[i], v->bytes - i, &cp);
                                        if (n <= 0) {
                                                dump(out, "\\x%02hhx", v->str[i]);
                                        } else {
                                                if (cp <= 0xFFFF) {
                                                        dump(out, "\\u%04x", cp);
                                                } else {
                                                        cp -= 0x10000;
                                                        u16 hi = 0xD800 + (cp >> 10);
                                                        u16 lo = 0xDC00 + (cp & 0x3FF);
                                                        dump(out, "\\u%04x\\u%04x", hi, lo);
                                                }
                                        }
                                        i += n - 1;
                                } else if (iscntrl(v->str[i])) {
                                        dump(out, "\\x%02hhx", v->str[i]);
                                } else {
                                        xvP(*out, v->str[i]);
                                }
                                break;
                        }
                }
                xvP(*out, '"');
                break;
        case VALUE_BOOLEAN:
                if (v->boolean)
                        xvPn(*out, "true", 4);
                else
                        xvPn(*out, "false", 5);
                break;
        case VALUE_INTEGER:
                xvR(*out, out->count + 64);
                out->count += snprintf(out->items + out->count, 64, "%"PRIiMAX, v->integer);
                break;
        case VALUE_REAL:
                xvR(*out, out->count + 64);
                out->count += dtoa(v->real, out->items + out->count, 64);
                break;
        case VALUE_ARRAY:
                xvP(*out, '[');
                if (!try_visit(v->array))
                        return false;
                for (int i = 0; i < v->array->count; ++i) {
                        if (!encode(ty, &v->array->items[i], out))
                                return false;
                        if (i + 1 < v->array->count)
                                xvP(*out, ',');
                }
                vvX(Visiting);
                xvP(*out, ']');
                break;
        case VALUE_DICT:
                xvP(*out, '{');
                int last = -1;
                for (int i = 0; i < v->dict->size; ++i)
                        if (v->dict->keys[i].type == VALUE_STRING)
                                last = i;
                if (!try_visit(v->dict))
                        return false;
                for (int i = 0; i < v->dict->size; ++i) {
                        if (v->dict->keys[i].type != VALUE_STRING)
                                continue;
                        if (!encode(ty, &v->dict->keys[i], out))
                                return false;
                        xvP(*out, ':');
                        if (!encode(ty, &v->dict->values[i], out))
                                return false;
                        if (i != last)
                                xvP(*out, ',');
                }
                vvX(Visiting);
                xvP(*out, '}');
                break;
        case VALUE_OBJECT:
        {
                if (!try_visit(v->object))
                        return false;

                Value *vp = class_lookup_method_i(ty, v->class, NAMES.json);

                if (vp != NULL) {
                        Value method = METHOD(NAMES.json, vp, v);
                        Value s = vm_eval_function(ty, NULL, &method, NULL);
                        if (s.type == VALUE_STRING) {
                                gP(&s);
                                xvPn(*out, s.str, s.bytes);
                                gX();
                        } else {
                                return encode(ty, &s, out);
                        }
                } else {
                        xvP(*out, '{');
                        for (int i = 0; i < vN(v->object->ids); ++i) {
                                char const *name = M_NAME(v__(v->object->ids, i));
                                xvP(*out, '"');
                                xvPn(*out, name, strlen(name));
                                xvP(*out, '"');
                                xvP(*out, ':');
                                if (!encode(ty, v_(v->object->values, i), out))
                                        return false;
                                xvP(*out, ',');
                        }
                        vvX(Visiting);
                        if (*vvL(*out) == ',')
                                *vvL(*out) = '}';
                        else
                                xvP(*out, '}');
                }
                break;
        }
        case VALUE_TUPLE:
                xvP(*out, '{');
                if (!try_visit(v->items))
                        return false;
                for (int i = 0; i < v->count; ++i) {
                        xvP(*out, '"');
                        if (v->ids != NULL && v->ids[i] != -1) {
                                char const *name = M_NAME(v->ids[i]);
                                xvPn(*out, name, strlen(name));
                        } else {
                                char b[32];
                                snprintf(b, sizeof b - 1, "%d", i);
                                xvPn(*out, b, strlen(b));
                        }
                        xvP(*out, '"');
                        xvP(*out, ':');
                        if (!encode(ty, &v->items[i], out)) {
                                return false;
                        }
                        xvP(*out, ',');
                }
                vvX(Visiting);
                if (*vvL(*out) == ',') {
                        *vvL(*out) = '}';
                } else {
                        xvP(*out, '}');
                }
                break;
        case VALUE_BLOB:
                xvP(*out, '"');
                for (int i = 0; i < v->blob->count; ++i) {
                        char b[3];
                        snprintf(b, sizeof b, "%.2X", (unsigned)v->blob->items[i]);
                        xvP(*out, '\\');
                        xvP(*out, 'x');
                        xvP(*out, b[0]);
                        xvP(*out, b[1]);
                }
                xvP(*out, '"');
                break;
        default:
                return false;

        }

        return true;
}

Value
json_parse(Ty *ty, char const *s, usize n)
{
        json = s;
        len = n;

        xd = false;

        GC_STOP();

        if (setjmp(jb) != 0) {
                GC_RESUME();
                return NIL;
        }

        Value v = value(ty);
        space();

        if (peek() != '\0')
                v = NIL;

        GC_RESUME();

        return v;
}

Value
json_parse_xD(Ty *ty, char const *s, usize n)
{
        json = s;
        len = n;

        xd = true;

        GC_STOP();

        if (setjmp(jb) != 0) {
                GC_RESUME();
                return NIL;
        }

        Value v = value(ty);
        space();

        if (peek() != '\0')
                v = NIL;

        GC_RESUME();

        return v;
}

Value
json_encode(Ty *ty, Value const *v)
{
        str s;
        vec_init(s);

        Value r = NIL;

        Visiting.count = 0;

        if (encode(ty, v, &s)) {
                r = vSs(s.items, s.count);
                free(s.items);
        }

        return r;
}


bool
json_dump(Ty *ty, Value const  *v, byte_vector *out)
{
        Visiting.count = 0;

        size_t start = vN(*out);

        if (!encode(ty, v, out)) {
                out->count = start;
                return false;
        }

        return true;
}
