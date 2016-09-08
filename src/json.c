#include <setjmp.h>
#include <ctype.h>
#include <stdlib.h>
#include <errno.h>

#include "test.h"
#include "value.h"
#include "object.h"
#include "util.h"
#include "vec.h"
#include "vm.h"

#define KW_DELIM(c) (strchr(" \n}],", c) != NULL)

#define FAIL longjmp(jb, 1)

static jmp_buf jb;
static char const *json;
static int len;

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
                } else vec_push(str, next());
        }

        if (next() != '"')
                FAIL;

        int n = str.count;
        struct string *s = value_string_alloc(n);
        memcpy(s->data, str.items, n);

        vec_empty(str);

        return STRING(s->data, n, s);
}

static struct value
array(void)
{
        if (next() != '[')
                FAIL;

        struct value_array *a = value_array_new();

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
        
        struct object *obj = object_new();

        while (peek() != '\0' && peek() != '}') {
                space();
                struct value key = string();
                space();
                if (next() != ':')
                        FAIL;
                struct value val = value();
                object_put_value(obj, key, val);
                space();
                if (peek() != '}' && next() != ',')
                        FAIL;
        }

        if (next() != '}')
                FAIL;

        return OBJECT(obj);
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

struct value
json_parse(char const *s, int n)
{
        json = s;
        len = n;

        if (setjmp(jb) != 0)
                return NIL;

        struct value v = value();
        space();

        if (peek() != '\0')
                return NIL;

        return v;
}

TEST(null)
{
        vm_init();
        char const *s = " null ";
        struct value v = json_parse(s, 6);
        claim(value_test_equality(&v, &NIL));
}

TEST(jtrue)
{
        vm_init();
        char const *s = " true";
        struct value v = json_parse(s, 5);
        claim(value_test_equality(&v, &BOOLEAN(true)));
}

TEST(jfalse)
{
        vm_init();
        char const *s = " false";
        struct value v = json_parse(s, 6);
        claim(value_test_equality(&v, &BOOLEAN(false)));
}
