#include <setjmp.h>
#include <ctype.h>
#include <stdlib.h>
#include <errno.h>

#include "test.h"
#include "value.h"
#include "dict.h"
#include "util.h"
#include "table.h"
#include "vec.h"
#include "vm.h"

#define KW_DELIM(c) (strchr(" \n}],", c) != NULL)
#define FAIL longjmp(jb, 1)

static _Thread_local jmp_buf jb;
static _Thread_local char const *json;
static _Thread_local int len;

typedef vec(char) str;

static _Thread_local vec(void const *) Visiting;

inline static char
peek(void)
{
        if (len <= 0)
                return '\0';

        return *json;
}

inline static char
next(void)
{
        if (len <= 0)
                return '\0';
        --len;
        return *json++;
}

static struct value
value(void);

inline static void
space(void)
{
        while (isspace(peek())) next();
}

static struct value
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

        struct value result;

        errno = 0;
        if (integral)
                result = INTEGER(strtoimax(num, NULL, 10));
        else
                result = REAL(strtod(num, NULL));

        if (errno != 0)
                FAIL;

        return result;
}

static struct value
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

static struct value
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

static struct value
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

static struct value
string(void)
{
        if (next() != '"')
                FAIL;

        vec(char) str;
        vec_init(str);

        char b[3] = {0};
        unsigned hex;

        while (peek() != '\0' && peek() != '"') {
                if (peek() == '\\') switch (next(), next()) {
                case 't':  vec_push(str, '\t'); break;
                case 'f':  vec_push(str, '\f'); break;
                case 'n':  vec_push(str, '\n'); break;
                case 'r':  vec_push(str, '\r'); break;
                case 'b':  vec_push(str, '\b'); break;
                case '"':  vec_push(str, '"');  break;
                case '/':  vec_push(str, '/');  break;
                case '\\': vec_push(str, '\\'); break;
                case 'x':
                        b[0] = next();
                        b[1] = next();
                        if (sscanf(b, "%X", &hex) != 1) {
                                FAIL;
                        }
                        vec_push(str, (char)hex);
                        break;
                } else vec_push(str, next());
        }

        if (next() != '"')
                FAIL;

        int n = str.count;

        if (n == 0)
                return STRING_NOGC(NULL, 0);

        char *s = value_string_alloc(n);
        memcpy(s, str.items, n);

        vec_empty(str);

        return STRING(s, n);
}

static struct value
array(void)
{
        if (next() != '[')
                FAIL;

        struct array *a = value_array_new();

        while (peek() != '\0' && peek() != ']') {
                vec_push(*a, value());
                space();
                if (peek() != ']' && next() != ',')
                        FAIL;
        }

        if (next() != ']')
                FAIL;

        return ARRAY(a);
}

static struct value
object(void)
{
        if (next() != '{')
                FAIL;

        struct dict *obj = dict_new();

        while (peek() != '\0' && peek() != '}') {
                space();
                struct value key = string();
                space();
                if (next() != ':')
                        FAIL;
                struct value val = value();
                dict_put_value(obj, key, val);
                space();
                if (peek() != '}' && next() != ',')
                        FAIL;
        }

        if (next() != '}')
                FAIL;

        return DICT(obj);
}

static struct value
value(void)
{
        space();

        switch (peek()) {
        case '{': return object();
        case '[': return array();
        case '"': return string();
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
                vec_push(Visiting, p);
                return true;
        }
}

static bool
encode(struct value const *v, str *out)
{
        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_NIL:
                vec_push_n(*out, "null", 4);
                break;
        case VALUE_STRING:
                vec_push(*out, '"');
                for (int i = 0; i < v->bytes; ++i) {
                        switch (v->string[i]) {
                        case '\t':
                                vec_push(*out, '\\');
                                vec_push(*out, 't');
                                break;
                        case '\n':
                                vec_push(*out, '\\');
                                vec_push(*out, 'n');
                                break;
                        case '\\':
                        case '"':
                                vec_push(*out, '\\');
                        default:
                                vec_push(*out, v->string[i]);
                                break;
                        }
                }
                vec_push(*out, '"');
                break;
        case VALUE_BOOLEAN:
                if (v->boolean)
                        vec_push_n(*out, "true", 4);
                else
                        vec_push_n(*out, "false", 5);
                break;
        case VALUE_INTEGER:
                vec_reserve(*out, out->count + 64);
                out->count += snprintf(out->items + out->count, 64, "%"PRIiMAX, v->integer);
                break;
        case VALUE_REAL:
                vec_reserve(*out, out->count + 64);
                out->count += snprintf(out->items + out->count, 64, "%g", v->real);
                break;
        case VALUE_ARRAY:
                vec_push(*out, '[');
                if (!try_visit(v->array))
                        return false;
                for (int i = 0; i < v->array->count; ++i) {
                        if (!encode(&v->array->items[i], out))
                                return false;
                        if (i + 1 < v->array->count)
                                vec_push(*out, ',');
                }
                vec_pop(Visiting);
                vec_push(*out, ']');
                break;
        case VALUE_DICT:
                vec_push(*out, '{');
                int last = -1;
                for (int i = 0; i < v->dict->size; ++i)
                        if (v->dict->keys[i].type == VALUE_STRING)
                                last = i;
                if (!try_visit(v->dict))
                        return false;
                for (int i = 0; i < v->dict->size; ++i) {
                        if (v->dict->keys[i].type != VALUE_STRING)
                                continue;
                        if (!encode(&v->dict->keys[i], out))
                                return false;
                        vec_push(*out, ':');
                        if (!encode(&v->dict->values[i], out))
                                return false;
                        if (i != last)
                                vec_push(*out, ',');
                }
                vec_pop(Visiting);
                vec_push(*out, '}');
                break;
        case VALUE_OBJECT:
                vec_push(*out, '{');
                if (!try_visit(v->object))
                        return false;
                for (int i = 0; i < TABLE_SIZE; ++i) {
                        for (int j = 0; j < v->object->buckets[i].names.count; ++j) {
                                vec_push(*out, '"');
                                char const *name = v->object->buckets[i].names.items[j];
                                vec_push_n(*out, name, strlen(name));
                                vec_push(*out, '"');
                                vec_push(*out, ':');
                                if (!encode(&v->object->buckets[i].values.items[j], out))
                                        return false;
                                vec_push(*out, ',');
                        }
                }
                vec_pop(Visiting);
                if (*vec_last(*out) == ',')
                        *vec_last(*out) = '}';
                else
                        vec_push(*out, '}');
                break;
        case VALUE_TUPLE:
                vec_push(*out, '{');
                if (!try_visit(v->items))
                        return false;
                for (int i = 0; i < v->count; ++i) {
                        vec_push(*out, '"');
                        if (v->names != NULL && v->names[i] != NULL) {
                                vec_push_n(*out, v->names[i], strlen(v->names[i]));
                        } else {
                                char b[32];
                                snprintf(b, sizeof b - 1, "%d", i);
                                vec_push_n(*out, b, strlen(b));
                        }
                        vec_push(*out, '"');
                        vec_push(*out, ':');
                        if (!encode(&v->items[i], out)) {
                                return false;
                        }
                        vec_push(*out, ',');
                }
                vec_pop(Visiting);
                if (*vec_last(*out) == ',') {
                        *vec_last(*out) = '}';
                } else {
                        vec_push(*out, '}');
                }
                break;
        case VALUE_BLOB:
                vec_push(*out, '"');
                for (int i = 0; i < v->blob->count; ++i) {
                        char b[3];
                        snprintf(b, sizeof b, "%.2X", (unsigned)v->blob->items[i]);
                        vec_push(*out, '\\');
                        vec_push(*out, 'x');
                        vec_push(*out, b[0]);
                        vec_push(*out, b[1]);
                }
                vec_push(*out, '"');
                break;
        default:
                return false;

        }

        return true;
}

struct value
json_parse(char const *s, int n)
{
        json = s;
        len = n;

        ++GC_OFF_COUNT;

        if (setjmp(jb) != 0) {
                --GC_OFF_COUNT;
                return NIL;
        }

        struct value v = value();
        space();

        if (peek() != '\0')
                v = NIL;

        --GC_OFF_COUNT;

        return v;
}

struct value
json_encode(struct value const *v)
{
        str s;
        vec_init(s);

        struct value r = NIL;

        Visiting.count = 0;

        if (encode(v, &s)) {
                r = STRING_CLONE(s.items, s.count);
                vec_empty(s);
        }

        return r;
}
