#include <setjmp.h>
#include <ctype.h>
#include <stdlib.h>
#include <errno.h>
#include <utf8proc.h>

#include "test.h"
#include "value.h"
#include "dict.h"
#include "xd.h"
#include "dtoa.h"
#include "itable.h"
#include "class.h"
#include "vec.h"
#include "vm.h"
#include "ty.h"
#include "types2.h"

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

        byte_vector str = {0};

        char b[8] = {0};
        i32 cp;
        u16 lo;
        u16 hi;
        utf8proc_size_t n;

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

        xvF(str);

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

        bool first = true;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_NIL:
                xvPn(*out, "null", 4);
                break;

        case VALUE_TAG:
                dump((void *)out, "\"%s\"", tags_name(ty, v->tag));
                break;

        case VALUE_STRING:
                xvP(*out, '"');
                for (int i = 0; i < sN(*v); ++i) {
                        int n;
                        int32_t cp;
                        switch (ss(*v)[i]) {
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
                                if ((ss(*v)[i]) > 127) {
                                        n = utf8proc_iterate(&ss(*v)[i], sN(*v) - i, &cp);
                                        if (n <= 0) {
                                                dump(out, "\\x%02hhx", ss(*v)[i]);
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
                                } else if (iscntrl(ss(*v)[i])) {
                                        dump(out, "\\x%02hhx", ss(*v)[i]);
                                } else {
                                        xvP(*out, ss(*v)[i]);
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
                out->count += snprintf(out->items + out->count, 64, "%"PRIiMAX, v->z);
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
                if (!try_visit(v->dict)) {
                        return false;
                }
                dfor(v->dict, {
                        if (key->type != VALUE_STRING) {
                                continue;
                        }
                        if (!first) {
                                xvP(*out, ',');
                        }
                        if (!encode(ty, key, out)) {
                                return false;
                        }
                        xvP(*out, ':');
                        if (!encode(ty, val, out)) {
                                return false;
                        }
                        first = false;
                });
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
                                xvPn(*out, ss(s), sN(s));
                                gX();
                        } else {
                                return encode(ty, &s, out);
                        }
                } else {
                        xvP(*out, '{');
                        for (int i = 0; i < v->object->nslot; ++i) {
                                char const *name = M_NAME(v__(v->object->class->fields.ids, i));
                                xvPn(*out, name, strlen(name));
                                xvP(*out, '"');
                                xvP(*out, ':');
                                if (!encode(ty, &v->object->slots[i], out)) {
                                        return false;
                                }
                                xvP(*out, ',');
                        }
                        if (v->object->dynamic != NULL) {
                                for (int i = 0; i < vN(v->object->dynamic->ids); ++i) {
                                        char const *name = M_NAME(v__(v->object->dynamic->ids, i));
                                        xvPn(*out, name, strlen(name));
                                        xvP(*out, '"');
                                        xvP(*out, ':');
                                        if (!encode(ty, &v->object->slots[i], out)) {
                                                return false;
                                        }
                                        xvP(*out, ',');
                                }
                        }
                        vvX(Visiting);
                        if (*vvL(*out) == ',') {
                                *vvL(*out) = '}';
                        } else {
                                xvP(*out, '}');
                        }
                }
                break;
        }

        case VALUE_TUPLE:
                xvP(*out, '{');
                if (!try_visit(v->items)) {
                        return false;
                }
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

        if (peek() != '\0') {
                v = NIL;
        }

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

        if (peek() != '\0') {
                v = NIL;
        }

        GC_RESUME();

        return v;
}

static Value
typed_value(Ty *ty, T2Type t0);

static Value
checked_value(Ty *ty, T2Type t0)
{
        Value v = value(ty);
        if (!types2_check(ty, t0, &v)) {
                FAIL;
        }
        return v;
}

static Value
typed_array(Ty *ty, T2Type element)
{
        if (next() != '[') FAIL;

        Array *a = vA();

        while (peek() != '\0' && peek() != ']') {
                vvP(*a, element == T2_TYPE_INVALID ? value(ty) : typed_value(ty, element));
                space();
                if (peek() != ']' && next() != ',') FAIL;
        }

        if (next() != ']') FAIL;

        return ARRAY(a);
}

static Value
typed_dict(Ty *ty, T2Type val_type)
{
        if (next() != '{') FAIL;

        Dict *obj = dict_new(ty);

        while (peek() != '\0' && peek() != '}') {
                space();
                Value key = string(ty);
                space();
                if (next() != ':') FAIL;
                Value val = val_type == T2_TYPE_INVALID ? value(ty) : typed_value(ty, val_type);
                dict_put_value(ty, obj, key, val);
                space();
                if (peek() != '}' && next() != ',') FAIL;
        }

        if (next() != '}') FAIL;

        return DICT(obj);
}

static Value
typed_tuple(Ty *ty, T2Type t0, size_t typed_count)
{
        T2Universe *universe = types2_universe();

        if (next() != '[') FAIL;

        SCRATCH_SAVE();
        ValueVector items = {0};

        while (peek() != '\0' && peek() != ']') {
                size_t i = vN(items);
                svP(items, i < typed_count ? typed_value(ty, t2_type_child(universe, t0, i)) : value(ty));
                space();
                if (peek() != ']' && next() != ',') {
                        SCRATCH_RESTORE();
                        FAIL;
                }
        }

        if (next() != ']' || vN(items) < typed_count) {
                SCRATCH_RESTORE();
                FAIL;
        }

        Value tuple = vT(vN(items));
        for (u32 i = 0; i < vN(items); ++i) {
                tuple.items[i] = v__(items, i);
        }

        SCRATCH_RESTORE();

        return tuple;
}

static Value
typed_record(Ty *ty, T2Type t0)
{
        T2Universe *universe = types2_universe();

        if (next() != '{') FAIL;

        SCRATCH_SAVE();

        size_t nfields = t2_record_field_count(universe, t0);

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

                char const *kstr = TY_TMP_C_STR(key);
                T2Type field_type = t2_record_field_type(universe, t0, kstr, NULL, NULL);
                Value val = field_type == T2_TYPE_INVALID ? value(ty) : typed_value(ty, field_type);

                space();
                if (peek() != '}' && next() != ',') {
                        SCRATCH_RESTORE();
                        FAIL;
                }

                svP(keys, key);
                svP(values, val);
        }

        if (next() != '}') {
                SCRATCH_RESTORE();
                FAIL;
        }

        Value object = value_record(ty, vN(keys));

        for (u32 i = 0; i < vN(keys); ++i) {
                char const *key = TY_TMP_C_STR(v__(keys, i));
                object.ids[i]   = M_ID(key);
                object.items[i] = v__(values, i);
        }

        for (size_t i = 0; i < nfields; ++i) {
                T2FieldSpec field;
                if (!t2_record_field(universe, t0, i, &field) || field.presence != T2_PRESENCE_REQUIRED) {
                        continue;
                }
                int fid = M_ID(field.name);
                bool found = false;
                for (u32 j = 0; j < vN(keys); ++j) {
                        if (object.ids[j] == fid) {
                                found = true;
                                break;
                        }
                }
                if (!found) {
                        SCRATCH_RESTORE();
                        FAIL;
                }
        }

        SCRATCH_RESTORE();

        return object;
}

static Value
typed_union(Ty *ty, T2Type t0)
{
        T2Universe *universe = types2_universe();
        char const *saved_json = json;
        usize saved_len = len;
        size_t arity = t2_type_arity(universe, t0);

        for (size_t i = 0; i < arity; ++i) {
                json = saved_json;
                len = saved_len;

                jmp_buf saved_jb;
                memcpy(saved_jb, jb, sizeof jb);

                if (setjmp(jb) == 0) {
                        Value v = typed_value(ty, t2_type_child(universe, t0, i));
                        memcpy(jb, saved_jb, sizeof jb);
                        return v;
                }

                memcpy(jb, saved_jb, sizeof jb);
        }

        FAIL;
}

static Value
typed_nominal(Ty *ty, T2Type t0)
{
        T2Universe *universe = types2_universe();
        uint64_t symbol = t2_type_payload(universe, t0);
        int class = types2_symbol_class(symbol);

        switch (class) {
        case CLASS_INT:    return typed_value(ty, t2_primitive(universe, T2_TYPE_INT));
        case CLASS_FLOAT:  return typed_value(ty, t2_primitive(universe, T2_TYPE_FLOAT));
        case CLASS_STRING: return typed_value(ty, t2_primitive(universe, T2_TYPE_STRING));
        case CLASS_BOOL:   return typed_value(ty, t2_primitive(universe, T2_TYPE_BOOL));
        case CLASS_ARRAY:  return typed_array(ty, t2_type_child(universe, t0, 0));
        case CLASS_DICT:   return typed_dict(ty, t2_type_child(universe, t0, 1));
        default:           return value(ty);
        }
}

static Value
typed_value(Ty *ty, T2Type t0)
{
        T2Universe *universe = types2_universe();

        space();

        Value v;

        switch (t2_type_kind(universe, t0)) {
        case T2_TYPE_NIL:
                return null();

        case T2_TYPE_INT:
                v = number();
                if (v.type != VALUE_INTEGER) {
                        FAIL;
                }
                return v;

        case T2_TYPE_FLOAT:
                v = number();
                if (v.type == VALUE_INTEGER) {
                        return REAL((double)v.z);
                }
                if (v.type != VALUE_REAL) {
                        FAIL;
                }
                return v;

        case T2_TYPE_STRING:
                return string(ty);

        case T2_TYPE_BOOL:
                if (peek() == 't') return jtrue();
                if (peek() == 'f') return jfalse();
                FAIL;

        case T2_TYPE_LITERAL_BOOL:
        case T2_TYPE_LITERAL_INT:
        case T2_TYPE_LITERAL_STRING:
        case T2_TYPE_INT_RANGE:
                return checked_value(ty, t0);

        case T2_TYPE_REFINEMENT:
                return typed_value(ty, t2_type_child(universe, t0, 0));

        case T2_TYPE_COMPUTED:
        {
                T2Type resolved = t2_type_resolve_computed(universe, t0);
                return resolved == T2_TYPE_INVALID || resolved == t0
                     ? value(ty)
                     : typed_value(ty, resolved);
        }

        case T2_TYPE_RECURSIVE:
        {
                T2Type unfolded = t2_recursive_unfold(universe, t0);
                return unfolded == T2_TYPE_INVALID || unfolded == t0
                     ? value(ty)
                     : typed_value(ty, unfolded);
        }

        case T2_TYPE_NOMINAL:
                return typed_nominal(ty, t0);

        case T2_TYPE_RECORD:
                return typed_record(ty, t0);

        case T2_TYPE_TUPLE:
                return typed_tuple(ty, t0, t2_type_arity(universe, t0));

        case T2_TYPE_VARIADIC_TUPLE:
                return typed_tuple(ty, t0, (size_t)t2_type_payload(universe, t0));

        case T2_TYPE_UNION:
                return typed_union(ty, t0);

        default:
                return value(ty);
        }
}

Value
json_parse_typed(Ty *ty, T2Type t0, char const *s, usize n)
{
        json = s;
        len  = n;

        xd = true;

        GC_STOP();

        if (setjmp(jb) != 0) {
                GC_RESUME();
                zP(
                        "json.parse(): failed to parse JSON as %s",
                        types2_show(ty, t0)
                );
        }

        Value v = typed_value(ty, t0);
        space();

        if (peek() != '\0') {
                GC_RESUME();
                zP(
                        "json.parse(): unexpected trailing data after parsing %s",
                        types2_show(ty, t0)
                );
        }

        GC_RESUME();

        return v;
}

Value
json_encode(Ty *ty, Value const *v)
{
        str buf = {0};
        Value r = NIL;

        v0(Visiting);

        if (encode(ty, v, &buf)) {
                r = vSs(vv(buf), vN(buf));
                xvF(buf);
        }

        return r;
}


bool
json_dump(Ty *ty, Value const  *v, byte_vector *out)
{
        Visiting.count = 0;

        usize start = vN(*out);

        if (!encode(ty, v, out)) {
                out->count = start;
                return false;
        }

        return true;
}
