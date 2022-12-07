#include <inttypes.h>
#include <math.h>
#include <errno.h>
#include <limits.h>
#include <string.h>
#include <stdnoreturn.h>
#include <time.h>
#include <locale.h>

#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netdb.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <netdb.h>
#include <netinet/ip.h>
#include <sys/time.h>
#include <poll.h>
#include <signal.h>
#include <sys/mman.h>
#include <openssl/md5.h>
#include <openssl/sha.h>
#include <utf8proc.h>
#include <sys/epoll.h>
#include <pthread.h>

#include "tags.h"
#include "value.h"
#include "parse.h"
#include "vm.h"
#include "log.h"
#include "util.h"
#include "token.h"
#include "json.h"
#include "dict.h"
#include "object.h"
#include "class.h"
#include "compiler.h"

static _Thread_local char buffer[1024 * 1024 * 4];

static _Thread_local vec(char) B;

#define ASSERT_ARGC(func, ac) \
        if (argc != (ac)) { \
                vm_panic(func " expects " #ac " argument(s) but got %d", argc); \
        }

#define ASSERT_ARGC_2(func, ac1, ac2) \
        if (argc != (ac1) && argc != (ac2)) { \
                vm_panic(func " expects " #ac1 " or " #ac2 " argument(s) but got %d", argc); \
        }

#define ASSERT_ARGC_3(func, ac1, ac2, ac3) \
        if (argc != (ac1) && argc != (ac2) && argc != (ac3)) { \
                vm_panic(func " expects " #ac1 ", " #ac2 ", or " #ac3 " argument(s) but got %d", argc); \
        }

struct value
builtin_print(int argc, struct value *kwargs)
{
        struct value *sep = NAMED("sep");

        if (sep != NULL && sep->type != VALUE_STRING) {
                vm_panic(
                        "print(): %s%ssep%s must be a string",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        struct value *end = NAMED("end");

        if (end != NULL && end->type != VALUE_STRING) {
                vm_panic(
                        "print(): %s%send%s must be a string",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        struct value *flush = NAMED("flush");
        bool do_flush = flush != NULL && value_truthy(flush);

        flockfile(stdout);

        for (int i = 0; i < argc; ++i) {
                struct value *v = &ARG(i);
                if (i > 0) {
                        if (sep != NULL) {
                                fwrite(sep->string, 1, sep->bytes, stdout);
                        } else {
                                fputs(", ", stdout);
                        }
                }
                if (v->type == VALUE_STRING) {
                        fwrite(v->string, 1, v->bytes, stdout);
                } else {
                        char *s = value_show(&ARG(i));
                        fputs(s, stdout);
                        gc_free(s);
                }
        }


        if (end != NULL) {
                fwrite(end->string, 1, end->bytes, stdout);
        } else {
                putchar('\n');
        }

        if (do_flush) {
                fflush(stdout);
        }

        funlockfile(stdout);

        return NIL;
}

struct value
builtin_slurp(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("slurp()", 0, 1);

        char p[PATH_MAX + 1];
        int fd;
        bool need_close = false;

        if (argc == 0) {
                fd = 0;
        } else if (ARG(0).type == VALUE_STRING) {
                struct value v = ARG(0);

                if (v.bytes >= sizeof p)
                        return NIL;

                memcpy(p, v.string, v.bytes);
                p[v.bytes] = '\0';

                fd = open(p, O_RDONLY);
                if (fd < 0)
                        return NIL;

                need_close = true;
        } else if (ARG(0).type == VALUE_INTEGER) {
                fd = ARG(0).integer;
        } else {
                vm_panic("the argument to slurp() must be a path or a file descriptor");
        }

        struct stat st;
        if (fstat(fd, &st) != 0) {
                close(fd);
                return NIL;
        }

        if (S_ISREG(st.st_mode) || S_ISLNK(st.st_mode)) {
                size_t n = st.st_size;
                void *m = mmap(NULL, n, PROT_READ, MAP_SHARED, fd, 0);
                if (m == NULL) {
                        close(fd);
                        return NIL;
                }

                char *s = value_string_alloc(n);
                memcpy(s, m, n);

                munmap(m, n);
                close(fd);

                return STRING(s, n);
        } else if (!S_ISDIR(st.st_mode)) {
                FILE *f = fdopen(fd, "r");
                int r;

                ReleaseLock(true);

                B.count = 0;

                while (!feof(f) && (r = fread(buffer, 1, sizeof buffer, f)) > 0) {
                        vec_push_n(B, buffer, r);
                }

                TakeLock();

                struct value str = STRING_CLONE(B.items, B.count);

                if (need_close)
                        fclose(f);

                return str;
        }

        return NIL;
}

struct value
builtin_die(int argc, struct value *kwargs)
{
        ASSERT_ARGC("die()", 1);

        struct value message = ARG(0);
        if (message.type != VALUE_STRING)
                vm_panic("the argument to die() must be a string");

        vm_panic("%.*s", (int) message.bytes, message.string);
}

struct value
builtin_read(int argc, struct value *kwargs)
{
        ASSERT_ARGC("readLine()", 0);

        B.count = 0;

        ReleaseLock(true);

        int c;
        while (c = getchar(), c != EOF && c != '\n')
                vec_push(B, c);

        TakeLock();

        if (B.count == 0 && c != '\n')
                return NIL;

        return STRING_CLONE(B.items, B.count);
}

struct value
builtin_rand(int argc, struct value *kwargs)
{
        long low, high;

        ASSERT_ARGC_3("rand()", 0, 1, 2);

        long z = random();

        if (argc == 0) {
                return REAL(z / (double)((1UL << 31) - 1));
        }

        if (argc == 1 && ARG(0).type == VALUE_ARRAY) {
                int n = ARG(0).array->count;
                if (n == 0)
                        return NIL;
                else
                        return ARG(0).array->items[z % n];
        }

        for (int i = 0; i < argc; ++i)
                if (ARG(i).type != VALUE_INTEGER)
                        vm_panic("non-integer passed as argument %d to rand", i + 1);

        switch (argc) {
        case 1:  low = 0;              high = ARG(0).integer; break;
        case 2:  low = ARG(0).integer; high = ARG(1).integer; break;
        }

        return INTEGER((z % (high - low)) + low);

}

struct value
builtin_abs(int argc, struct value *kwargs)
{
        ASSERT_ARGC("abs()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return INTEGER(llabs(x.integer));
        case VALUE_REAL:    return REAL(fabs(x.real));
        default:
                vm_panic("the argument to abs() must be a number");
        }
}

struct value
builtin_gcd(int argc, struct value *kwargs)
{
        ASSERT_ARGC("gcd()", 2);

        struct value t = ARG(0);
        struct value u = ARG(1);

        if (t.type == VALUE_REAL) t = INTEGER(t.real);
        if (u.type == VALUE_REAL) u = INTEGER(u.real);

        if (t.type != VALUE_INTEGER || u.type != VALUE_INTEGER) {
                vm_panic("both arguments to gcd() must be integers");
        }

        intmax_t a = t.integer;
        intmax_t b = u.integer;

        while (b != 0) {
                intmax_t t = b;
                b = a % b;
                a = t;
        }

        return INTEGER(a);
}

struct value
builtin_lcm(int argc, struct value *kwargs)
{
        ASSERT_ARGC("lcm()", 2);

        struct value t = ARG(0);
        struct value u = ARG(1);

        if (t.type == VALUE_REAL) t = INTEGER(t.real);
        if (u.type == VALUE_REAL) u = INTEGER(u.real);

        if (t.type != VALUE_INTEGER || u.type != VALUE_INTEGER) {
                vm_panic("both arguments to lcm() must be integers");
        }

        intmax_t a = t.integer;
        intmax_t b = u.integer;

        while (b != 0) {
                intmax_t t = b;
                b = a % b;
                a = t;
        }

        return INTEGER(llabs(t.integer * u.integer) / a);
}

struct value
builtin_round(int argc, struct value *kwargs)
{
        ASSERT_ARGC("round()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return REAL(round(x.real));
        default:
                vm_panic("the argument to round() must be a number");
        }
}

struct value
builtin_iround(int argc, struct value *kwargs)
{
        ASSERT_ARGC("iround()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return INTEGER(llround(x.real));
        default:
                vm_panic("the argument to iround() must be a number");
        }
}

struct value
builtin_ceil(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ceil()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return INTEGER(ceil(x.real));
        default:
                vm_panic("the argument to ceil() must be a number");
        }
}

struct value
builtin_floor(int argc, struct value *kwargs)
{
        ASSERT_ARGC("floor()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return INTEGER(floor(x.real));
        default:
                vm_panic("the argument to floor() must be a number");
        }
}

struct value
builtin_chr(int argc, struct value *kwargs)
{
        ASSERT_ARGC("chr()", 1);

        struct value k = ARG(0);

        if (k.type != VALUE_INTEGER)
                vm_panic("the argument to chr() must be an integer");

        if (!utf8proc_codepoint_valid(k.integer))
                return NIL;

        char b[4];
        int n = utf8proc_encode_char(k.integer, b);

        return STRING_CLONE(b, n);
}

struct value
builtin_ord(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ord()", 1);

        struct value c = ARG(0);

        if (c.type != VALUE_STRING)
                vm_panic("the argument to ord() must be a string");

        int codepoint;
        int n = utf8proc_iterate(c.string, c.bytes, &codepoint);

        if (codepoint == -1 || n < c.bytes)
                return NIL;

        return INTEGER(codepoint);
}

struct value
builtin_hash(int argc, struct value *kwargs)
{
        ASSERT_ARGC("hash()", 1);
        return INTEGER(value_hash(&ARG(0)));
}

struct value
builtin_float(int argc, struct value *kwargs)
{
        ASSERT_ARGC("float()", 1);

        struct value v = ARG(0);

        switch (v.type) {
        case VALUE_NIL:     return NIL;
        case VALUE_INTEGER: return REAL((double)v.integer);
        case VALUE_REAL:    return v;
        case VALUE_STRING:;
                char buf[128];
                char *end;
                unsigned n = umin(v.bytes, 127);

                memcpy(buf, v.string, n);
                buf[n] = '\0';

                errno = 0;
                double x = strtod(buf, &end);

                if (errno != 0 || *end != '\0')
                        return NIL;

                return REAL(x);
        }

        vm_panic("invalid type passed to float()");
}

struct value
builtin_isnan(int argc, struct value *kwargs)
{
        ASSERT_ARGC("nan?()", 1);

        if (ARG(0).type != VALUE_REAL) {
                vm_panic("nan?() expects a float but got: %s", value_show(&ARG(0)));
        }

        return BOOLEAN(isnan(ARG(0).real));
}

struct value
builtin_blob(int argc, struct value *kwargs)
{
        ASSERT_ARGC("blob()", 0);
        return BLOB(value_blob_new());
}

struct value
builtin_int(int argc, struct value *kwargs)
{
        struct value v = INTEGER(0), a, s, b;
        int base;

        char const *string = buffer;

        ASSERT_ARGC_3("int()", 0, 1, 2);

        switch (argc) {
        case 0: return v;
        case 1: goto Coerce;
        case 2: goto CustomBase;
        }

Coerce:

        a = ARG(0);
        switch (a.type) {
        case VALUE_INTEGER:                                               return a;
        case VALUE_REAL:    v.integer = a.real;                           return v;
        case VALUE_BOOLEAN: v.integer = a.boolean;                        return v;
        case VALUE_ARRAY:   v.integer = a.array->count;                   return v;
        case VALUE_DICT:    v.integer = a.dict->count;                    return v;
        case VALUE_BLOB:    v.integer = a.blob->count;                    return v;
        case VALUE_STRING:
                base = 0;
                if (a.bytes >= sizeof buffer)
                        goto TooBig;
                memcpy(buffer, a.string, a.bytes);
                buffer[a.bytes] = '\0';
                goto String;
        default:                                                          return NIL;
        }

CustomBase:

        s = ARG(0);
        b = ARG(1);

        if (s.type != VALUE_STRING)
                vm_panic("non-string passed as first of two arguments to int()");
        if (b.type != VALUE_INTEGER)
                vm_panic("non-integer passed as second argument to int()");
        if (b.integer < 0 || b.integer == 1 || b.integer > 36)
                vm_panic("invalid base passed to int(): expected 0 or 2..36, but got %d", (int) b.integer);

        base = b.integer;

        if (s.bytes >= sizeof buffer)
                goto TooBig;
        memcpy(buffer, s.string, s.bytes);
        buffer[s.bytes] = '\0';

        /*
         * The 0b syntax for base-2 integers is not standard C, so the strto* family of
         * functions doesn't recognize it. Thus, we must handle it specially here.
         */
        if (base == 0 && string[0] == '0' && string[1] == 'b') {
                base = 2;
                string += 2;
        }

String:

        errno = 0;

        char *end;
        intmax_t n = strtoimax(string, &end, base);

        if (errno != 0 || *end != '\0')
                return NIL;

        return INTEGER(n);

TooBig:
        errno = ERANGE;
        return NIL;
}

struct value
builtin_str(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("str()", 0, 1);

        if (argc == 0)
                return STRING_NOGC(NULL, 0);

        struct value arg = ARG(0);
        if (arg.type == VALUE_STRING) {
                return arg;
        } else {
                char *str = value_show(&arg);
                struct value result = STRING_CLONE(str, strlen(str));
                gc_free(str);
                return result;
        }
}

struct value
builtin_bool(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bool()", 1);
        return BOOLEAN(value_truthy(&ARG(0)));
}

struct value
builtin_dict(int argc, struct value *kwargs)
{
        ASSERT_ARGC("dict()", 0);
        return DICT(dict_new());
}

struct value
builtin_array(int argc, struct value *kwargs)
{
        ASSERT_ARGC("array()", 0);
        return ARRAY(value_array_new());
}

struct value
builtin_tuple(int argc, struct value *kwargs)
{
        int named = 0;
        vec(char) names = {0};
        struct dict *d = (kwargs != NULL) ? kwargs->dict : NULL;

        if (d != NULL) for (int i = 0; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        named += 1;
                        vec_push_n(names, d->keys[i].string, d->keys[i].bytes);
                        vec_push(names, '\0');
                }
        }

        struct value tuple = value_tuple(argc + named);

        if (named > 0) {
                tuple.names = gc_alloc_object((argc + named) * sizeof (char *), GC_ANY);
        } else {
                tuple.gc_names = true;
        }

        for (int i = 0; i < argc; ++i) {
                tuple.items[i] = ARG(i);
                if (tuple.names != NULL) {
                        tuple.names[i] = NULL;
                }
        }

        char *name = names.items;

        if (d != NULL) for (int i = 0, n = argc; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        tuple.items[n] = d->values[i];
                        tuple.names[n] = name;
                        name += strlen(name) + 1;
                        n += 1;
                }
        }

        return tuple;
}

struct value
builtin_regex(int argc, struct value *kwargs)
{
        ASSERT_ARGC("regex()", 1);

        struct value pattern = ARG(0);

        if (pattern.type == VALUE_REGEX)
                return pattern;

        if (pattern.type != VALUE_STRING)
                vm_panic("non-string passed to regex()");

        snprintf(buffer, sizeof buffer - 1, "%.*s", (int) pattern.bytes, pattern.string);

        char const *err;
        int off;

        pcre *re = pcre_compile(buffer, 0, &err, &off, NULL);
        if (re == NULL)
                return NIL;

        pcre_extra *extra = pcre_study(re, PCRE_STUDY_EXTRA_NEEDED | PCRE_STUDY_JIT_COMPILE, &err);
        if (extra == NULL)
                return NIL;

        pcre_assign_jit_stack(extra, NULL, JITStack);

        struct regex *r = gc_alloc_object(sizeof *r, GC_REGEX);
        r->pcre = re;
        r->extra = extra;
        r->pattern = sclone(buffer);
        r->gc = true;

        return REGEX(r);
}

struct value
builtin_min(int argc, struct value *kwargs)
{
        if (argc < 2)
                vm_panic("min() expects 2 or more arguments, but got %d", argc);

        struct value min, v;
        min = ARG(0);

        for (int i = 1; i < argc; ++i) {
                v = ARG(i);
                if (value_compare(&v, &min) < 0)
                        min = v;
        }

        return min;
}

struct value
builtin_max(int argc, struct value *kwargs)
{
        if (argc < 2)
                vm_panic("max() expects 2 or more arguments, but got %d", argc);

        struct value max, v;
        max = ARG(0);

        for (int i = 1; i < argc; ++i) {
                v = ARG(i);
                if (value_compare(&v, &max) > 0)
                        max = v;
        }

        return max;
}

struct value
builtin_exp(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.exp()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math.exp() must be a float");

        return REAL(exp(x.real));
}

struct value
builtin_log(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.log()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math.log() must be a float");

        return REAL(log(x.real));
}

struct value
builtin_log2(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.log2()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math.log2() must be a float");

        return REAL(log2(x.real));
}

struct value
builtin_log10(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.log10()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math.log10() must be a float");

        return REAL(log10(x.real));
}

struct value
builtin_pow(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.pow()", 2);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the first argument to math.pow() must be a float");

        struct value y = ARG(1);
        if (y.type == VALUE_INTEGER)
                y = REAL(y.integer);
        if (y.type != VALUE_REAL)
                vm_panic("the second argument to math.pow() must be a float");

        return REAL(pow(x.real, y.real));
}

struct value
builtin_atan2(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.atan2()", 2);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the first argument to math.atan2() must be a float");

        struct value y = ARG(1);
        if (y.type == VALUE_INTEGER)
                y = REAL(y.integer);
        if (y.type != VALUE_REAL)
                vm_panic("the second argument to math.atan2() must be a float");

        return REAL(atan2(x.real, y.real));
}

#define MATH_WRAP(func)                                 \
        struct value                                    \
        builtin_ ## func (int argc, struct value *kwargs)           \
        {                                               \
                ASSERT_ARGC("math." #func "()", 1);    \
                                                        \
                struct value x = ARG(0);        \
                if (x.type == VALUE_INTEGER)            \
                        x = REAL(x.integer);            \
                if (x.type != VALUE_REAL)               \
                        vm_panic("the argument to math." #func "() must be a float"); \
                                                        \
                return REAL(func ## f (x.real));        \
        }

MATH_WRAP(cos)
MATH_WRAP(sin)
MATH_WRAP(tan)
MATH_WRAP(acos)
MATH_WRAP(asin)
MATH_WRAP(atan)
MATH_WRAP(tanh)
MATH_WRAP(sinh)
MATH_WRAP(cosh)

struct value
builtin_sqrt(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.sqrt()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math.sqrt() must be a float");

        return REAL(sqrt(x.real));
}

struct value
builtin_cbrt(int argc, struct value *kwargs)
{
        ASSERT_ARGC("math.cbrt()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math.cbrt() must be a float");

        return REAL(cbrt(x.real));
}

struct value
builtin_bit_and(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bit.and()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit.and() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit.and() must be an integer");

        return INTEGER(a.integer & b.integer);
}

struct value
builtin_bit_or(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bit.or()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit.or() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit.or() must be an integer");

        return INTEGER(a.integer | b.integer);
}

struct value
builtin_bit_xor(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bit.xor()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit.xor() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit.xor() must be an integer");

        return INTEGER(a.integer ^ b.integer);
}

struct value
builtin_bit_shift_left(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bit.shiftLeft()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit.shiftLeft() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit.shiftLeft() must be an integer");

        return INTEGER(a.integer << b.integer);
}

struct value
builtin_bit_shift_right(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bit.shiftRight()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit.shiftRight() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit.shiftRight() must be an integer");

        return INTEGER(a.integer >> b.integer);
}

struct value
builtin_bit_complement(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bit.complement()", 1);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit.complement() must be an integer");

        return INTEGER(~a.integer);
}

struct value
builtin_setenv(int argc, struct value *kwargs)
{
        static _Thread_local vec(char) varbuf;
        static _Thread_local vec(char) valbuf;

        ASSERT_ARGC("setenv()", 2);

        struct value var = ARG(0);
        struct value val = ARG(1);

        if (var.type != VALUE_STRING || val.type != VALUE_STRING)
                vm_panic("both arguments to setenv() must be strings");

        vec_push_n(varbuf, var.string, var.bytes);
        vec_push(varbuf, '\0');

        vec_push_n(valbuf, val.string, val.bytes);
        vec_push(valbuf, '\0');

        setenv(varbuf.items, valbuf.items, 1);

        varbuf.count = 0;
        valbuf.count = 0;

        return NIL;
}

struct value
builtin_getenv(int argc, struct value *kwargs)
{
        ASSERT_ARGC("getenv()", 1);

        struct value var = ARG(0);

        if (var.type != VALUE_STRING)
                vm_panic("non-string passed to getenv()");

        char buffer[256];

        if (var.bytes >= sizeof buffer)
                vm_panic("argument to getenv() is too long: '%.10s..'", var.string);

        memcpy(buffer, var.string, var.bytes);
        buffer[var.bytes] = '\0';

        char const *val = getenv(buffer);

        if (val == NULL)
                return NIL;
        else
                return STRING_NOGC(val, strlen(val));
}

struct value
builtin_locale_setlocale(int argc, struct value *kwargs)
{
        ASSERT_ARGC("locale.setlocale()", 2);

        if (ARG(0).type != VALUE_INTEGER) {
                vm_panic("locale.setlocale(): expected integer but got: %s", value_show(&ARG(0)));
        }

        if (ARG(1).type != VALUE_STRING) {
                vm_panic("locale.setlocale(): expected string but got: %s", value_show(&ARG(0)));
        }

        size_t n = min(ARG(1).bytes, sizeof buffer - 1);
        memcpy(buffer, ARG(1).string, n);
        buffer[n] = '\0';

        setlocale(ARG(0).integer, buffer);

        return NIL;
}

struct value
builtin_json_parse(int argc, struct value *kwargs)
{
        ASSERT_ARGC("json.parse()", 1);

        struct value json = ARG(0);
        if (json.type != VALUE_STRING)
                vm_panic("non-string passed to json.parse()");

        return json_parse(json.string, json.bytes);
}

struct value
builtin_json_encode(int argc, struct value *kwargs)
{
        ASSERT_ARGC("json.parse()", 1);
        return json_encode(&ARG(0));
}

struct value
builtin_sha1(int argc, struct value *kwargs)
{
        ASSERT_ARGC("sha1", 1);

        struct value s = ARG(0);
        unsigned char digest[SHA_DIGEST_LENGTH];

        if (s.type == VALUE_STRING) {
                SHA1((unsigned char const *)s.string, s.bytes, digest);
        } else if (s.type == VALUE_BLOB) {
                SHA1(s.blob->items, s.blob->count, digest);
        }

        struct blob *b = value_blob_new();
        vec_push_n(*b, digest, sizeof digest);

        return BLOB(b);
}

struct value
builtin_md5(int argc, struct value *kwargs)
{
        ASSERT_ARGC("md5", 1);

        struct value s = ARG(0);
        unsigned char digest[MD5_DIGEST_LENGTH];

        if (s.type == VALUE_STRING) {
                MD5((unsigned char const *)s.string, s.bytes, digest);
        } else if (s.type == VALUE_BLOB) {
                MD5(s.blob->items, s.blob->count, digest);
        }

        struct blob *b = value_blob_new();
        vec_push_n(*b, digest, sizeof digest);

        return BLOB(b);
}

static bool
b64dec(char const *s, size_t n)
{
        static unsigned char table[256] = {
                ['A'] =  0, ['B'] =  1, ['C'] =  2, ['D'] =  3, ['E'] =  4, ['F'] =  5,
                ['G'] =  6, ['H'] =  7, ['I'] =  8, ['J'] =  9, ['K'] = 10, ['L'] = 11,
                ['M'] = 12, ['N'] = 13, ['O'] = 14, ['P'] = 15, ['Q'] = 16, ['R'] = 17,
                ['S'] = 18, ['T'] = 19, ['U'] = 20, ['V'] = 21, ['W'] = 22, ['X'] = 23,
                ['Y'] = 24, ['Z'] = 25,

                ['a'] =  0 + 26, ['b'] =  1 + 26, ['c'] =  2 + 26, ['d'] =  3 + 26, ['e'] =  4 + 26, ['f'] =  5 + 26,
                ['g'] =  6 + 26, ['h'] =  7 + 26, ['i'] =  8 + 26, ['j'] =  9 + 26, ['k'] = 10 + 26, ['l'] = 11 + 26,
                ['m'] = 12 + 26, ['n'] = 13 + 26, ['o'] = 14 + 26, ['p'] = 15 + 26, ['q'] = 16 + 26, ['r'] = 17 + 26,
                ['s'] = 18 + 26, ['t'] = 19 + 26, ['u'] = 20 + 26, ['v'] = 21 + 26, ['w'] = 22 + 26, ['x'] = 23 + 26,
                ['y'] = 24 + 26, ['z'] = 25 + 26,

                ['0'] = 0 + 26 + 26, ['1'] = 1 + 26 + 26, ['2'] = 2 + 26 + 26, ['3'] = 3 + 26 + 26, ['4'] = 4 + 26 + 26,
                ['5'] = 5 + 26 + 26, ['6'] = 6 + 26 + 26, ['7'] = 7 + 26 + 26, ['8'] = 8 + 26 + 26, ['9'] = 9 + 26 + 26,

                ['+'] = 0 + 26 + 26 + 10, ['/'] = 1 + 26 + 26 + 10
        };

        B.count = 0;

        while (n > 0 && s[n - 1] == '=') {
                n -= 1;
        }

        for (size_t i = 0; i < n; ++i) {
                if (s[i] != 'A' && table[(unsigned char)s[i]] == 0) {
                        return false;
                }
        }

        lldiv_t d = lldiv(n, 4);
        unsigned char g[4];

        unsigned char s1, s2, s3, s4;

        for (size_t i = 0; i < d.quot; ++i) {
                memcpy(g, s + 4*i, 4);
                s1 = table[g[0]];
                s2 = table[g[1]];
                s3 = table[g[2]];
                s4 = table[g[3]];
                vec_push(B, (s1 << 2) | (s2 >> 4));
                vec_push(B, ((s2 & 0x0F) << 4) | (s3 >> 2));
                vec_push(B, ((s3 & 0x03) << 6) | s4);
        }

        memset(g, 0, sizeof g);
        memcpy(g, s + 4*d.quot, d.rem);

        switch (d.rem) {
        case 3:
                s1 = table[g[0]];
                s2 = table[g[1]];
                s3 = table[g[2]];
                vec_push(B, (s1 << 2) | (s2 >> 4));
                vec_push(B, ((s2 & 0x0F) << 4) | (s3 >> 2));
                break;
        case 2:
                s1 = table[g[0]];
                s2 = table[g[1]];
                vec_push(B, (s1 << 2) | (s2 >> 4));
                break;
        case 1:
                s1 = table[g[0]];
                vec_push(B, s1 << 2);
                break;
        }

        return true;
}

static void
b64enc(char const *s, size_t n)
{
        B.count = 0;

        lldiv_t d = lldiv(n, 3);
        unsigned char g[3];

        static char table[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                              "abcdefghijklmnopqrstuvwxyz"
                              "0123456789"
                              "+/";

        for (size_t i = 0; i < d.quot; ++i) {
                memcpy(g, s + 3*i, 3);
                vec_push(B, table[g[0] >> 2]);
                vec_push(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                vec_push(B, table[((g[1] & 0x0F) << 2) | (g[2] >> 6)]);
                vec_push(B, table[g[2] & 0x3F]);
        }

        memset(g, 0, sizeof g);
        memcpy(g, s + 3*d.quot, d.rem);

        switch (d.rem) {
        case 2:
                vec_push(B, table[g[0] >> 2]);
                vec_push(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                vec_push(B, table[((g[1] & 0x0F) << 2) | (g[2] >> 6)]);
                vec_push(B, '=');
                break;
        case 1:
                vec_push(B, table[g[0] >> 2]);
                vec_push(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                vec_push(B, '=');
                vec_push(B, '=');
                break;
        }
}

struct value
builtin_base64_encode(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("base64.encode()", 1, 2);

        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        vm_panic("base64.encode(): the second argument must be an integer");
                }

                size_t n = ARG(1).integer;

                switch (ARG(0).type) {
                case VALUE_PTR:
                        b64enc(ARG(0).ptr, n);
                        break;
                default:
                        goto Bad;
                }
        } else {
                switch (ARG(0).type) {
                case VALUE_STRING:
                        b64enc(ARG(0).string, ARG(0).bytes);
                        break;
                case VALUE_BLOB:
                        b64enc((char *)ARG(0).blob->items, ARG(0).blob->count);
                        break;
                default:
                        goto Bad;
                }
        }

        return STRING_CLONE(B.items, B.count);

Bad:
        vm_panic("base64.encode(): invalid argument(s)");

}

struct value
builtin_base64_decode(int argc, struct value *kwargs)
{
        ASSERT_ARGC("base64.decode()", 1);

        if (ARG(0).type != VALUE_STRING) {
                vm_panic("base64.decode(): argument must be a string");
        }

        if (!b64dec(ARG(0).string, ARG(0).bytes)) {
                return NIL;
        }

        struct blob *b = value_blob_new();

        NOGC(b);
        vec_push_n(*b, B.items, B.count);
        OKGC(b);

        return BLOB(b);
}

struct value
builtin_os_umask(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.umask()", 1);

        struct value mask = ARG(0);
        if (mask.type != VALUE_INTEGER) {
                vm_panic("the argument to os.umask() must be an integer");
        }

        return INTEGER(umask(mask.integer));
}

struct value
builtin_os_open(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.open()", 2, 3);

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                vm_panic("the path passed to os.open() must be a string");

        B.count = 0;

        vec_push_n(B, path.string, path.bytes);
        vec_push(B, '\0');

        struct value flags = ARG(1);
        if (flags.type != VALUE_INTEGER)
                vm_panic("the second argument to os.open() must be an integer (flags)");

        int fd;

        if (flags.integer & O_CREAT) {
                if (argc != 3)
                        vm_panic("os.open() called with O_CREAT but no third argument");
                if (ARG(2).type != VALUE_INTEGER)
                        vm_panic("the third argument to os.open() must be an integer");
                fd = open(B.items, flags.integer, (mode_t) ARG(2).integer);
        } else {
                fd = open(B.items, flags.integer);
        }


        return INTEGER(fd);
}

struct value
builtin_os_close(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.close()", 1);

        struct value file = ARG(0);

        if (file.type != VALUE_INTEGER)
                vm_panic("the argument to os.close() must be an integer");

        return INTEGER(close(file.integer));
}

struct value
builtin_os_mktemp(int argc, struct value *kwargs)
{
        char template[PATH_MAX + 1] = {0};

        if (argc > 2) {
                vm_panic("os.mktemp() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (argc >= 1 && ARG(0).type != VALUE_NIL) {
                struct value s = ARG(0);
                if (s.type != VALUE_STRING)
                        vm_panic("the first argument to os.mktemp() must be a string");
                /* -8 to make room for the .XXXXXX suffix and NUL byte */
                memcpy(template, s.string, min(s.bytes, sizeof template - 8));
        } else {
                strcpy(template, "tmp");
        }

        strcat(template, ".XXXXXX");

        int fd;

        if (argc == 2) {
                struct value flags = ARG(1);
                if (flags.type != VALUE_INTEGER)
                        vm_panic("the second argument to os.mktemp() must be an integer");
                fd = mkostemp(template, flags.integer);
        } else {
                fd = mkstemp(template);
        }

        if (fd == -1) {
                return NIL;
        }

        struct value pair = value_tuple(2);

        pair.items[0] = INTEGER(fd);
        pair.items[1] = STRING_CLONE(template, strlen(template));

        return pair;
}

struct value
builtin_os_opendir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.opendir()", 1);

        struct value path = ARG(0);
        DIR *d;

        if (path.type == VALUE_STRING) {
                if (path.bytes >= sizeof buffer) {
                        errno = ENOENT;
                        return NIL;
                }
                memcpy(buffer, path.string, path.bytes);
                buffer[path.bytes] = '\0';
                d = opendir(buffer);
        } else if (path.type == VALUE_INTEGER) {
                d = fdopendir(path.integer);
        } else {
                vm_panic("the argument to os.opendir() must be a path or a file descriptor");
        }

        if (d == NULL)
                return NIL;

        return PTR(d);
}

struct value
builtin_os_readdir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.readdir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                vm_panic("the argument to os.readdir() must be a pointer");

        struct dirent *entry = readdir(d.ptr);
        if (entry == NULL)
                return NIL;

        return value_named_tuple(
                "d_ino", INTEGER(entry->d_ino),
                "d_off", INTEGER(entry->d_off),
                "d_reclen", INTEGER(entry->d_reclen),
                "d_type", INTEGER(entry->d_type),
                "d_name", STRING_CLONE(entry->d_name, strlen(entry->d_name)),
                NULL
        );
}

struct value
builtin_os_rewinddir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.rewinddir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                vm_panic("the argument to os.rewinddir() must be a pointer");

        rewinddir(d.ptr);

        return NIL;
}

struct value
builtin_os_seekdir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.seekdir()", 2);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                vm_panic("the first argument to os.seekdir() must be a pointer");

        struct value off = ARG(1);
        if (off.type != VALUE_INTEGER)
                vm_panic("the second argument to os.seekdir() must be an integer");

        seekdir(d.ptr, off.integer);

        return NIL;
}

struct value
builtin_os_telldir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.telldir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                vm_panic("the argument to os.telldir() must be a pointer");

        return INTEGER(telldir(d.ptr));
}

struct value
builtin_os_closedir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.closedir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                vm_panic("the argument to os.closedir() must be a pointer");

        return INTEGER(closedir(d.ptr));
}

struct value
builtin_os_getcwd(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.getcwd()", 0);

        if (getcwd(buffer, sizeof buffer) == NULL)
                return NIL;

        return STRING_CLONE(buffer, strlen(buffer));
}

struct value
builtin_os_unlink(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.unlink()", 1);

        struct value path = ARG(0);

        if (path.type != VALUE_STRING)
                vm_panic("the argument to os.unlink() must be a string");

        if (path.bytes >= sizeof buffer) {
                errno = ENOENT;
                return INTEGER(-1);
        }

        memcpy(buffer, path.string, path.bytes);
        buffer[path.bytes] = '\0';

        return INTEGER(unlink(buffer));
}

struct value
builtin_os_mkdir(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.mkdir()", 1, 2);

        struct value path = ARG(0);

        if (path.type != VALUE_STRING) {
                vm_panic("os.mkdir(): expected string as first argument but got: %s", value_show(&ARG(0)));
        }

        mode_t mode = 0777;

        if (argc == 2 && ARG(1).type != VALUE_NIL) {
                if (ARG(1).type != VALUE_INTEGER) {
                        vm_panic("os.mkdir(): expected integer as second argument but got: %s", value_show(&ARG(1)));
                } else {
                        mode = ARG(1).integer;
                }
        }

        B.count = 0;
        vec_push_n(B, path.string, path.bytes);
        vec_push(B, '\0');

        return INTEGER(mkdir(B.items, mode));
}

struct value
builtin_os_rmdir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.rmdir()", 1);

        struct value path = ARG(0);

        if (path.type != VALUE_STRING) {
                vm_panic("os.rmdir(): expected string as first argument but got: %s", value_show(&ARG(0)));
        }

        B.count = 0;
        vec_push_n(B, path.string, path.bytes);
        vec_push(B, '\0');

        return INTEGER(rmdir(B.items));
}

struct value
builtin_os_chdir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.chdir()", 1);

        struct value dir = ARG(0);

        if (dir.type == VALUE_STRING) {
                if (dir.bytes >= sizeof buffer) {
                        errno = ENOENT;
                        return INTEGER(-1);
                }

                memcpy(buffer, dir.string, dir.bytes);
                buffer[dir.bytes] = '\0';

                return INTEGER(chdir(buffer));
        } else if (dir.type == VALUE_INTEGER) {
                return INTEGER(fchdir(dir.integer));
        } else {
                vm_panic("the argument to os.chdir() must be a path or a file descriptor");
        }


}

struct value
builtin_os_read(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.read()", 2, 3);

        struct value file = ARG(0);

        struct value blob;
        struct value n;

        if (argc == 3) {
                blob = ARG(1);
                n = ARG(2);
        } else {
                blob = BLOB(value_blob_new());
                n = ARG(1);
        }

        if (file.type != VALUE_INTEGER)
                vm_panic("the first argument to os.read() must be an integer");

        if (blob.type != VALUE_BLOB)
                vm_panic("the second argument to os.read() must be a blob");

        if (n.type != VALUE_INTEGER)
                vm_panic("the third argument to os.read() must be an integer");

        if (n.integer < 0)
                vm_panic("the third argument to os.read() must be non-negative");

        vec_reserve(*blob.blob, blob.blob->count + n.integer);

        ReleaseLock(true);
        ssize_t nr = read(file.integer, blob.blob->items + blob.blob->count, n.integer);
        TakeLock();

        if (nr != -1)
                blob.blob->count += nr;

        if (argc == 3)
                return INTEGER(nr);
        else if (nr != -1)
                return blob;
        else
                return NIL;
}

struct value
builtin_os_write(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.write()", 2, 3);

        struct value file = ARG(0);
        struct value data = ARG(1);

        if (file.type != VALUE_INTEGER)
                vm_panic("the first argument to os.write() must be an integer");

        ssize_t n;

        ReleaseLock(true);

        switch (data.type) {
        case VALUE_BLOB:
                n = write(file.integer, (void *)data.blob->items, data.blob->count);
                break;
        case VALUE_STRING:
                n = write(file.integer, data.string, data.bytes);
                break;
        case VALUE_INTEGER:
                n = write(file.integer, &((unsigned char){data.integer}), 1);
                break;
        case VALUE_PTR:
                if (argc != 3 || ARG(2).type != VALUE_INTEGER) {
                        vm_panic("os.write(): expected integer as third argument");
                }
                n = write(file.integer, data.ptr, ARG(2).integer);
                break;
        default:
                vm_panic("invalid argument to os.write()");
        }

        TakeLock();

        return INTEGER(n);
}

struct value
builtin_os_fsync(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.fsync()", 1);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER) {
                vm_panic("os.fsync(): expected integer but got: %s", value_show(&fd));
        }

        return INTEGER(fsync(fd.integer));
}

struct value
builtin_os_sync(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.sync()", 0);

        sync();

        return NIL;
}

struct value
builtin_os_spawn(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.spawn()", 1);

        struct value cmd = ARG(0);
        if (cmd.type != VALUE_ARRAY)
                vm_panic("the argument to os.spawn() must be an array");

        if (cmd.array->count == 0)
                vm_panic("empty array passed to os.spawn()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        vm_panic("non-string in array passed to os.spawn()");

        struct value *detached = NAMED("detached");
        struct value *combine = NAMED("combineOutput");
        struct value *share_stderr = NAMED("shareStderr");

        if (share_stderr != NULL && !value_truthy(share_stderr)) {
                share_stderr = NULL;
        }

        if (detached != NULL && detached->type != VALUE_BOOLEAN) {
                vm_panic(
                        "os.spawn(): %s%sdetached%s must be a boolean",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        int in[2];
        int out[2];
        int err[2];
        int exc[2];

        if (pipe(in) == -1) {
                return NIL;
        }

        if (pipe(out) == -1) {
                close(in[0]);
                close(in[1]);
                return NIL;
        }

        if (!share_stderr && pipe(err) == -1) {
                close(in[0]);
                close(in[1]);
                close(out[0]);
                close(out[1]);
                return NIL;
        }

        if (pipe(exc) == -1) {
                close(in[0]);
                close(in[1]);
                close(out[0]);
                close(out[1]);
                if (!share_stderr) {
                        close(err[0]);
                        close(err[1]);
                }
                return NIL;
        }

        pid_t pid = fork();
        switch (pid) {
        case -1:
                close(in[0]);
                close(in[1]);
                close(out[0]);
                close(out[1]);
                if (!share_stderr) {
                        close(err[0]);
                        close(err[1]);
                }
                close(exc[0]);
                close(exc[1]);
                return NIL;
        case 0:
                close(in[1]);
                close(out[0]);
                if (!share_stderr) {
                        close(err[0]);
                }

                int errfd = err[1];

                if (combine && combine->boolean) {
                        errfd = out[1];
                        close(err[1]);
                }

                if (dup2(in[0], STDIN_FILENO) == -1
                ||  dup2(out[1], STDOUT_FILENO) == -1
                ||  (!share_stderr && dup2(errfd, STDERR_FILENO) == -1)) {
                        write(exc[1], &errno, sizeof errno);
                        exit(EXIT_FAILURE);
                }

                fcntl(exc[1], F_SETFD, FD_CLOEXEC);

                if (detached && detached->boolean) {
                        setpgid(0, 0);
                }

                vec(char *) args;
                vec_init(args);

                for (int i = 0; i < cmd.array->count; ++i) {
                        char *arg = gc_alloc(cmd.array->items[i].bytes + 1);
                        memcpy(arg, cmd.array->items[i].string, cmd.array->items[i].bytes);
                        arg[cmd.array->items[i].bytes] = '\0';
                        vec_push(args, arg);
                }

                vec_push(args, NULL);

                if (execvp(args.items[0], args.items) == -1) {
                        write(exc[1], &errno, sizeof errno);
                        exit(EXIT_FAILURE);
                }

                return NIL;
        default:
                close(in[0]);
                close(out[1]);
                if (!share_stderr) {
                        close(err[1]);
                }
                close(exc[1]);

                int status;
                if (read(exc[0], &status, sizeof status) != 0) {
                        errno = status;
                        close(in[1]);
                        close(out[0]);
                        if (!share_stderr) {
                                close(err[0]);
                        }
                        close(exc[0]);
                        return NIL;
                }

                close(exc[0]);

                struct value stderrfd;

                if (!share_stderr && (!combine || !combine->boolean)) {
                        stderrfd = INTEGER(err[0]);
                } else {
                        stderrfd = NIL;
                        close(err[0]);
                }

                return value_named_tuple(
                        "stdin",   INTEGER(in[1]),
                        "stdout",  INTEGER(out[0]),
                        "stderr",  stderrfd,
                        "pid",     INTEGER(pid),
                        NULL
                );
        }
}

struct value
builtin_thread_join(int argc, struct value *kwargs)
{
        if (argc != 1) {
                vm_panic("thread.join() expects one argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("non-pointer passed to thread.join(): %s", value_show(&ARG(0)));
        }

        ReleaseLock(true);
        pthread_join((pthread_t)ARG(0).ptr, NULL);
        TakeLock();

        return NIL;
}

struct value
builtin_thread_detach(int argc, struct value *kwargs)
{
        if (argc != 1) {
                vm_panic("thread.detach() expects one argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("non-pointer passed to thread.detach(): %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_detach((pthread_t)ARG(0).ptr));
}

struct value
builtin_thread_mutex(int argc, struct value *kwargs)
{
        pthread_mutex_t *p = gc_alloc_object(sizeof *p, GC_ANY);
        pthread_mutex_init(p, NULL);
        return GCPTR(p, p);
}

struct value
builtin_thread_cond(int argc, struct value *kwargs)
{
        pthread_cond_t *p = gc_alloc_object(sizeof *p, GC_ANY);
        pthread_cond_init(p, NULL);
        return GCPTR(p, p);
}

struct value
builtin_thread_cond_wait(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("thread.waitCond()", 2, 3);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.waitCond() expects a pointer as its first argument but got: %s", value_show(&ARG(0)));
        }

        if (ARG(1).type != VALUE_PTR) {
                vm_panic("thread.waitCond() expects a pointer as its second argument but got: %s", value_show(&ARG(1)));
        }

        int r;

        ReleaseLock(true);

        if (argc == 2) {
                r = pthread_cond_wait(ARG(0).ptr, ARG(1).ptr);
        } else {
                if (ARG(2).type != VALUE_INTEGER) {
                        vm_panic("thread.waitCond() expects an integer as its third argument but got: %s", value_show(&ARG(2)));
                }

                struct timespec ts;
                clock_gettime(CLOCK_REALTIME, &ts);

                ts.tv_sec += ARG(2).integer / 1000000;
                ts.tv_nsec += (ARG(2).integer % 1000000) * 1000;

                r = pthread_cond_timedwait(ARG(0).ptr, ARG(1).ptr, &ts);
        }

        TakeLock();

        return INTEGER(r);
}

struct value
builtin_thread_cond_signal(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.signalCond()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.signalCond() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_cond_signal(ARG(0).ptr));
}

struct value
builtin_thread_cond_broadcast(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.broadcastCond()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.broadcastCond() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_cond_broadcast(ARG(0).ptr));
}

struct value
builtin_thread_cond_destroy(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.destroyCond()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.destroyCond() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_cond_destroy(ARG(0).ptr));
}

struct value
builtin_thread_mutex_destroy(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.destroyMutex()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.destroyMutex() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_mutex_destroy(ARG(0).ptr));
}

struct value
builtin_thread_lock(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.lock()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.lock() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        ReleaseLock(true);
        int r = pthread_mutex_lock(ARG(0).ptr);
        TakeLock();

        return INTEGER(r);
}

struct value
builtin_thread_trylock(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.tryLock()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.tryLock() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_mutex_trylock(ARG(0).ptr));
}

struct value
builtin_thread_unlock(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.unlock()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("thread.unlock() expects a pointer but got: %s", value_show(&ARG(0)));
        }

        return INTEGER(pthread_mutex_unlock(ARG(0).ptr));
}

struct value
builtin_thread_create(int argc, struct value *kwargs)
{
        if (argc == 0) {
                vm_panic("thread.create() expects at least one argument");
        }

        if (!CALLABLE(ARG(0))) {
                vm_panic("non-callable value passed to thread.create(): %s", value_show(&ARG(0)));
        }

        pthread_t p;
        struct value *ctx = gc_alloc(sizeof (struct value[argc + 1]));

        for (int i = 0; i < argc; ++i) {
                ctx[i] = ARG(i);
        }

        ctx[argc] = NONE;

        NewThread(&p, ctx);

        return PTR((void *)p);
}

struct value
builtin_thread_kill(int argc, struct value *kwargs)
{
        ASSERT_ARGC("thread.kill()", 2);

        struct value t = ARG(0);

        if (t.type != VALUE_PTR) {
                vm_panic("thread.kill() expects a pointer as the first argument but got: %s", value_show(&t));
        }

        struct value sig = ARG(1);

        if (sig.type != VALUE_INTEGER) {
                vm_panic("thread.kill(): expected integer as second argument but got: %s", value_show(&sig));
        }

        return INTEGER(pthread_kill((pthread_t)t.ptr, sig.integer));
}

struct value
builtin_os_fork(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.fork()", 0);
        return INTEGER(fork());
}

struct value
builtin_os_pipe(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.pipe()", 0);

        int p[2];

        if (pipe(p) == -1)
                return NIL;

        struct value fds = value_tuple(2);

        fds.items[0] = INTEGER(p[0]);
        fds.items[1] = INTEGER(p[1]);

        return fds;
}

struct value
builtin_os_dup(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.dup()", 1);

        struct value old = ARG(0);

        if (old.type != VALUE_INTEGER)
                vm_panic("os.dup(): argument must be an integer");

        return INTEGER(dup(old.integer));
}

struct value
builtin_os_dup2(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.dup2()", 2);

        struct value old = ARG(0);
        struct value new = ARG(1);

        if (old.type != VALUE_INTEGER || new.type != VALUE_INTEGER)
                vm_panic("the arguments to os.dup2() must be integers");

        return INTEGER(dup2(old.integer, new.integer));
}

struct value
builtin_os_socket(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.socket()", 3);

        struct value domain = ARG(0);
        struct value type = ARG(1);
        struct value protocol = ARG(2);

        if (domain.type != VALUE_INTEGER || type.type != VALUE_INTEGER || protocol.type != VALUE_INTEGER)
                vm_panic("the arguments to os.socket() must be integers");

        return INTEGER(socket(domain.integer, type.integer, protocol.integer));
}

struct value
builtin_os_setsockopt(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.setsockopt()", 3, 4);

        struct value sock = ARG(0);
        if (sock.type != VALUE_INTEGER)
                vm_panic("the first argument to os.setsockopt() must be an integer (socket fd)");

        struct value level = ARG(1);
        if (level.type != VALUE_INTEGER)
                vm_panic("the second argument to os.setsockopt() must be an integer (level)");

        struct value option = ARG(2);
        if (level.type != VALUE_INTEGER)
                vm_panic("the third argument to os.setsockopt() must be an integer (option)");

        int o;

        if (argc == 4) {
                struct value v = ARG(3);
                if (v.type != VALUE_INTEGER)
                        vm_panic("the fourth argument to os.setsockopt() must be an integer (opt value)");
                o = v.integer;
        } else {
                o = 1;
        }

        return INTEGER(setsockopt(sock.integer, level.integer, option.integer, &o, sizeof o));
}

struct value
builtin_os_getsockopt(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.getsockopt()", 3);

        struct value sock = ARG(0);
        if (sock.type != VALUE_INTEGER)
                vm_panic("the first argument to os.getsockopt() must be an integer (socket fd)");

        struct value level = ARG(1);
        if (level.type != VALUE_INTEGER)
                vm_panic("the second argument to os.getsockopt() must be an integer (level)");

        struct value option = ARG(2);
        if (level.type != VALUE_INTEGER)
                vm_panic("the third argument to os.getsockopt() must be an integer (option)");

        int o;
        socklen_t n = sizeof o;

        if (getsockopt(sock.integer, level.integer, option.integer, &o, &n) == 0) {
                return INTEGER(o);
        } else {
                return NIL;
        }
}

struct value
builtin_os_getnameinfo(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.getnameinfo()", 2);

        struct sockaddr *addr;
        socklen_t alen;

        switch (ARG(0).type) {
        case VALUE_PTR:
                addr = ARG(0).ptr;
                alen = sizeof (struct sockaddr_storage);
                break;
        case VALUE_BLOB:
                addr = (void *)ARG(0).blob->items;
                alen = ARG(0).blob->count;
                break;
        default:
                vm_panic("os.getnameinfo(): invalid address argument: %s", value_show(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                vm_panic("os.getnameinfo(): invalid flags argument: %s", value_show(&ARG(1)));
        }

        char host[128];
        char serv[32];

        int r = getnameinfo(addr, alen, host, sizeof host, serv, sizeof serv, ARG(1).integer);

        if (r == 0) {
                struct value v = value_tuple(2);
                v.items[0] = STRING_CLONE(host, strlen(host));
                v.items[1] = STRING_CLONE(serv, strlen(serv));
                return v;
        }

        return INTEGER(r);
}

struct value
builtin_os_getpeername(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.getpeername()", 1);

        if (ARG(0).type != VALUE_INTEGER) {
                vm_panic("os.getpeername(): expected integer but got: %s", value_show(&ARG(0)));
        }

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        ReleaseLock(true);
        int r = getpeername(ARG(0).integer, (void *)&addr, &addr_size);
        TakeLock();

        if (r < 0) {
                return NIL;
        }

        struct blob *b = value_blob_new();
        vec_push_n_unchecked(*b, &addr, min(addr_size, sizeof addr));

        return BLOB(b);
}

struct value
builtin_os_getsockname(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.getsockname()", 1);

        if (ARG(0).type != VALUE_INTEGER) {
                vm_panic("os.getsockname(): expected integer but got: %s", value_show(&ARG(0)));
        }

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        ReleaseLock(true);
        int r = getsockname(ARG(0).integer, (void *)&addr, &addr_size);
        TakeLock();

        if (r < 0) {
                return NIL;
        }

        struct blob *b = value_blob_new();
        vec_push_n_unchecked(*b, &addr, min(addr_size, sizeof addr));

        return BLOB(b);
}

struct value
builtin_os_shutdown(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.shutdown()", 2);

        struct value fd = ARG(0);
        struct value how = ARG(1);

        if (fd.type != VALUE_INTEGER || how.type != VALUE_INTEGER)
                vm_panic("the arguments to os.shutdown() must be integers");

        return INTEGER(shutdown(fd.integer, how.integer));
}

struct value
builtin_os_listen(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.listen()", 2);

        struct value sockfd = ARG(0);
        struct value backlog = ARG(1);

        if (sockfd.type != VALUE_INTEGER || backlog.type != VALUE_INTEGER)
                vm_panic("the arguments to os.listen() must be integers");

        return INTEGER(listen(sockfd.integer, backlog.integer));
}

struct value
builtin_os_connect(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.connect()", 2);

        struct value sockfd = ARG(0);
        struct value addr = ARG(1);

        if (sockfd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.connect() must be an integer");

        if (addr.type != VALUE_TUPLE)
                vm_panic("the second argument to os.connect() must be a tuple");

        struct value *v = tuple_get(&addr, "family");
        if (v == NULL || v->type != VALUE_INTEGER)
                vm_panic("missing or invalid address family in dict passed to os.connect()");

        struct sockaddr_un un_addr;
        struct sockaddr_in in_addr;
        struct in_addr ia;

        struct value *sockaddr = tuple_get(&addr, "address");
        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                return INTEGER(connect(sockfd.integer, (struct sockaddr *)sockaddr->blob->items, sockaddr->blob->count));
        } else switch (v->integer) {
                case AF_UNIX:
                        memset(&un_addr, 0, sizeof un_addr);
                        un_addr.sun_family = AF_UNIX;
                        v = tuple_get(&addr, "path");
                        if (v == NULL || v->type != VALUE_STRING)
                                vm_panic("missing or invalid path in dict passed to os.connect()");
                        memcpy(un_addr.sun_path, v->string, min(v->bytes, sizeof un_addr.sun_path));
                        return INTEGER(connect(sockfd.integer, (struct sockaddr *)&un_addr, sizeof un_addr));
                case AF_INET:
                        memset(&in_addr, 0, sizeof in_addr);
                        in_addr.sin_family = AF_INET;
                        v = tuple_get(&addr, "address");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                vm_panic("missing or invalid address in dict passed to os.connect()");
                        ia.s_addr = htonl(v->integer);
                        in_addr.sin_addr = ia;
                        v = tuple_get(&addr, "port");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                vm_panic("missing or invalid port in dict passed to os.connect()");
                        unsigned short p = htons(v->integer);
                        memcpy(&in_addr.sin_port, &p, sizeof in_addr.sin_port);
                        return INTEGER(connect(sockfd.integer, (struct sockaddr *)&in_addr, sizeof in_addr));
                default:
                        vm_panic("invalid arguments to os.connect()");
        }
}

struct value
builtin_os_bind(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.bind()", 2);

        struct value sockfd = ARG(0);
        struct value addr = ARG(1);

        if (sockfd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.bind() must be an integer");

        if (addr.type != VALUE_TUPLE)
                vm_panic("the second argument to os.bind() must be a named tuple");

        struct value *v = tuple_get(&addr, "family");
        if (v == NULL || v->type != VALUE_INTEGER)
                vm_panic("missing or invalid address family in address passed to os.bind()");

        struct sockaddr_un un_addr;
        struct sockaddr_in in_addr;
        struct in_addr ia;

        struct value *sockaddr = tuple_get(&addr, "address");
        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                return INTEGER(bind(sockfd.integer, (struct sockaddr *)sockaddr->blob->items, sockaddr->blob->count));
        } else switch (v->integer) {
                case AF_UNIX:
                        memset(&un_addr, 0, sizeof un_addr);
                        un_addr.sun_family = AF_UNIX;
                        v = tuple_get(&addr, "path");
                        if (v == NULL || v->type != VALUE_STRING)
                                vm_panic("missing or invalid path in tuple passed to os.bind()");
                        memcpy(un_addr.sun_path, v->string, min(v->bytes, sizeof un_addr.sun_path));
                        return INTEGER(bind(sockfd.integer, (struct sockaddr *)&un_addr, sizeof un_addr));
                case AF_INET:
                        memset(&in_addr, 0, sizeof in_addr);
                        in_addr.sin_family = AF_INET;
                        v = tuple_get(&addr, "address");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                vm_panic("missing or invalid address in tuple passed to os.bind()");
                        ia.s_addr = htonl(v->integer);
                        in_addr.sin_addr = ia;
                        v = tuple_get(&addr, "port");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                vm_panic("missing or invalid port in tuple passed to os.bind()");
                        unsigned short p = htons(v->integer);
                        memcpy(&in_addr.sin_port, &p, sizeof in_addr.sin_port);
                        return INTEGER(bind(sockfd.integer, (struct sockaddr *)&in_addr, sizeof in_addr));
                default:
                        vm_panic("invalid arguments to os.bind()");
        }
}

struct value
builtin_os_getaddrinfo(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.getaddrinfo()", 5, 6);

        struct value host = ARG(0);
        if (host.type != VALUE_STRING && host.type != VALUE_NIL)
                vm_panic("the first argument to os.getaddrinfo() (node) must be a string or nil");

        struct value port = ARG(1);
        if (port.type != VALUE_STRING && port.type != VALUE_INTEGER && port.type != VALUE_NIL)
                vm_panic("the second argument to os.getaddrinfo() (service) must be a string, an integer, or nil");

        if (host.type == VALUE_NIL && port.type == VALUE_NIL) {
                vm_panic("os.getaddrinfo(): the first and second arguments (node and service) cannot both be nil");
        }

        struct value family = ARG(2);
        if (family.type != VALUE_INTEGER)
                vm_panic("the third argument to os.getaddrinfo() (family) must be an integer");

        struct value type = ARG(3);
        if (type.type != VALUE_INTEGER)
                vm_panic("the fourth argument to os.getaddrinfo() (type) must be an integer");

        struct value protocol = ARG(4);
        if (protocol.type != VALUE_INTEGER)
                vm_panic("the fifth argument to os.getaddrinfo() (protocol) must be an integer");

        // Default to the flags used when hints == NULL in glibc getaddrinfo()
        int flags = AI_V4MAPPED | AI_ADDRCONFIG;
        if (argc == 6 && ARG(5).type != VALUE_NIL) {
                if (ARG(5).type != VALUE_INTEGER)
                        vm_panic("the sixth argument to os.getaddrinfo() (flags) must be an integer");
                flags = ARG(5).integer;
        }

        char const *node;
        char const *service;

        B.count = 0;

        if (port.type == VALUE_INTEGER) {
                sprintf(buffer, "%hu", (unsigned short)port.integer);
                port = STRING_NOGC(buffer, strlen(buffer));
        }

        if (host.type != VALUE_NIL) {
                vec_push_n(B, host.string, host.bytes);
                vec_push(B, '\0');

                vec_push_n(B, port.string, port.bytes);
                vec_push(B, '\0');

                node = B.items;
                service = B.items + host.bytes + 1;
        } else if (port.type == VALUE_NIL) {
                vec_push_n(B, host.string, host.bytes);
                vec_push(B, '\0');

                node = B.items;
                service = NULL;
        } else {
                vec_push_n(B, port.string, port.bytes);
                vec_push(B, '\0');

                node = NULL;
                service = B.items;
        }

        struct value results = ARRAY(value_array_new());
        gc_push(&results);

        struct addrinfo *res;
        struct addrinfo hints;

        memset(&hints, 0, sizeof hints);
        hints.ai_flags = flags;
        hints.ai_family = family.integer;
        hints.ai_socktype = type.integer;
        hints.ai_protocol = protocol.integer;

        int r = getaddrinfo(node, service, &hints, &res);
        if (r == 0) {
                for (struct addrinfo *it = res; it != NULL; it = it->ai_next) {
                        struct blob *b = value_blob_new();

                        struct value entry = value_named_tuple(
                                "family",    INTEGER(it->ai_family),
                                "type",      INTEGER(it->ai_socktype),
                                "protocol",  INTEGER(it->ai_protocol),
                                "address",   BLOB(b),
                                "canonname", NIL,
                                NULL
                        );

                        NOGC(entry.items);
                        NOGC(entry.names);

                        value_array_push(results.array, entry);

                        OKGC(entry.items);
                        OKGC(entry.names);

                        vec_push_n(*b, (char *)it->ai_addr, it->ai_addrlen);

                        if (it->ai_canonname != NULL) {
                                entry.items[4] = STRING_CLONE(it->ai_canonname, strlen(it->ai_canonname));
                        }
                }

                gc_pop();

                freeaddrinfo(res);

                results.tags = gettag(NULL, "Ok");
                results.type |= VALUE_TAGGED;

                return results;

        } else {
                return (struct value) {
                        .type = VALUE_INTEGER | VALUE_TAGGED,
                        .integer = r,
                        .tags = gettag(NULL, "Err")
                };
        }
}

struct value
builtin_os_gai_strerror(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.gai_strerror()", 1);

        if (ARG(0).type != VALUE_INTEGER) {
                vm_panic("os.gai_strerror(): expected integer but got: %s", value_show(&ARG(0)));
        }

        char const *msg = gai_strerror(ARG(0).integer);

        return STRING_NOGC(msg, strlen(msg));
}

struct value
builtin_os_accept(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.accept()", 1);

        struct value sockfd = ARG(0);

        if (sockfd.type != VALUE_INTEGER)
                vm_panic("the argument to os.accept() must be an integer");

        struct sockaddr a;
        socklen_t n = sizeof a;

        ReleaseLock(true);
        int r = accept(sockfd.integer, &a, &n);
        TakeLock();
        if (r == -1)
                return NIL;

        struct blob *b = value_blob_new();
        vec_push_n(*b, (char *)&a, n);

        return value_named_tuple(
                "fd",   INTEGER(r),
                "addr", BLOB(b),
                NULL
        );
}

struct value
builtin_os_recvfrom(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.recvfrom()", 3, 4);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.recvfrom() must be an integer");

        struct value buffer;
        struct value size;
        struct value flags;

        if (argc == 3) {
                buffer = BLOB(value_blob_new());
                size = ARG(1);
                flags = ARG(2);
        } else {
                buffer = ARG(1);
                size = ARG(2);
                flags = ARG(3);
        }

        if (buffer.type != VALUE_BLOB)
                vm_panic("the buffer argument to os.recvfrom() must be a blob");

        if (size.type != VALUE_INTEGER || size.integer < 0)
                vm_panic("the size argument to os.recvfrom() must be a non-negative integer");

        if (flags.type != VALUE_INTEGER)
                vm_panic("the flags argument to os.recvfrom() must be an integer");

        NOGC(buffer.blob);

        vec_reserve(*buffer.blob, size.integer);

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        ReleaseLock(true);
        ssize_t r = recvfrom(fd.integer, buffer.blob->items, size.integer, flags.integer, (void *)&addr, &addr_size);
        TakeLock();
        if (r < 0) {
                OKGC(buffer.blob);
                return NIL;
        }

        buffer.blob->count = r;

        struct blob *b = value_blob_new();
        NOGC(b);
        vec_push_n(*b, &addr, min(addr_size, sizeof addr));

        struct value result = value_tuple(2);

        result.items[0] = buffer;
        result.items[1] = BLOB(b);

        OKGC(b);
        OKGC(buffer.blob);

        return result;
}

struct value
builtin_os_sendto(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.sendto()", 3, 4);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.sendto() must be an integer (fd)");

        struct value buffer = ARG(1);
        if (buffer.type != VALUE_BLOB && buffer.type != VALUE_STRING) {
                vm_panic(
                        "os.sendto(): expected Blob or String as second argument but got: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        value_show(&buffer),
                        TERM(0)
                );
        }

        struct value flags = ARG(2);
        if (flags.type != VALUE_INTEGER)
                vm_panic("the third argument to os.sendto() must be an integer (flags)");

        struct value addr = ARG(3);
        if (addr.type != VALUE_BLOB)
                vm_panic("the fourth argument to os.sendto() must be a blob (sockaddr)");

        ReleaseLock(true);
        ssize_t r = (buffer.type == VALUE_BLOB)
                  ? sendto(fd.integer, buffer.blob->items, buffer.blob->count, flags.integer, (void *)addr.blob->items, addr.blob->count)
                  : sendto(fd.integer, buffer.string, buffer.bytes, flags.integer, (void *)addr.blob->items, addr.blob->count);
        TakeLock();

        return INTEGER(r);
}

struct value
builtin_os_poll(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.poll()", 2);

        struct value fds = ARG(0);
        struct value timeout = ARG(1);

        if (fds.type != VALUE_ARRAY)
                vm_panic("the first argument to os.poll() must be an array");

        if (timeout.type != VALUE_INTEGER)
                vm_panic("the second argument to os.poll() must be an integer");

        static _Thread_local vec(struct pollfd) pfds;
        pfds.count = 0;

        vec_reserve(pfds, fds.array->count);

        struct value *v;
        for (int i = 0; i < fds.array->count; ++i) {
                if (fds.array->items[i].type != VALUE_TUPLE)
                        vm_panic("non-tuple in fds array passed to os.poll()");
                v = tuple_get(&fds.array->items[i], "fd");
                if (v == NULL || v->type != VALUE_INTEGER)
                        vm_panic("all tuples in the fds array passed to os.poll() must have an integer value under the key 'fd'");
                pfds.items[i].fd = v->integer;
                v = tuple_get(&fds.array->items[i], "events");
                if (v != NULL && v->type == VALUE_INTEGER)
                        pfds.items[i].events = v->integer;
                else
                        pfds.items[i].events = POLLIN;
        }

        pfds.count = fds.array->count;

        ReleaseLock(true);
        int ret = poll(pfds.items, pfds.count, timeout.integer);
        TakeLock();

        if (ret <= 0)
                return INTEGER(ret);

        for (int i = 0; i < fds.array->count; ++i) {
                fds.array->items[i] = value_named_tuple(
                        "fd",      *tuple_get(&fds.array->items[i], "fd"),
                        "events",  *tuple_get(&fds.array->items[i], "events"),
                        "revents", INTEGER(pfds.items[i].revents),
                        NULL
                );
        }

        return INTEGER(ret);
}

struct value
builtin_os_epoll_create(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.epoll_create()", 1);

        struct value flags = ARG(0);
        if (flags.type != VALUE_INTEGER)
                vm_panic("the argument to os.epoll_create() must be an integer");

        return INTEGER(epoll_create1(flags.integer));
}

struct value
builtin_os_epoll_ctl(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.epoll_ctl()", 4);

        struct value efd = ARG(0);
        if (efd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.epoll_ctl() must be an integer");

        struct value op = ARG(1);
        if (op.type != VALUE_INTEGER)
                vm_panic("the second argument to os.epoll_ctl() must be an integer");

        struct value fd = ARG(2);
        if (fd.type != VALUE_INTEGER)
                vm_panic("the third argument to os.epoll_ctl() must be an integer");

        struct value events = ARG(3);
        if (events.type != VALUE_INTEGER)
                vm_panic("the fourth argument to os.epoll_ctl() must be an integer");

        struct epoll_event ev = {
                .events = events.integer,
                .data = { .fd = fd.integer }
        };

        return INTEGER(epoll_ctl(efd.integer, op.integer, fd.integer, &ev));
}

struct value
builtin_os_epoll_wait(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.epoll_wait()", 2);

        struct value efd = ARG(0);
        if (efd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.epoll_wait() must be an integer (epoll fd)");

        struct value timeout = ARG(1);
        if (timeout.type != VALUE_INTEGER)
                vm_panic("the second argument to os.epoll_wait() must be an integer (timeout in ms)");

        struct epoll_event events[32];

        ReleaseLock(true);
        int n = epoll_wait(efd.integer, events, sizeof events / sizeof events[0], timeout.integer);
        TakeLock();

        if (n == -1)
                return NIL;

        struct array *result = value_array_new();

        gc_push(&ARRAY(result));

        for (int i = 0; i < n; ++i) {
                struct value ev = value_tuple(2);
                NOGC(ev.items);
                ev.items[0] = INTEGER(events[i].data.fd);
                ev.items[1] = INTEGER(events[i].events);
                value_array_push(result, ev);
                OKGC(ev.items);
        }

        gc_pop();

        return ARRAY(result);
}

struct value
builtin_os_waitpid(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.waitpid()", 1, 2);

        struct value pid = ARG(0);

        int flags = 0;
        if (argc == 2) {
                struct value f = ARG(1);
                if (f.type != VALUE_INTEGER) goto Bad;
                flags = f.integer;
        } else {
        }

        if (pid.type != VALUE_INTEGER) {
Bad:
                vm_panic("both arguments to os.waitpid() must be integers");
        }

        int status;
        int ret = waitpid(pid.integer, &status, flags);

        if (ret <= 0)
                return INTEGER(ret);

        return PAIR(INTEGER(ret), INTEGER(status));
}

#define WAITMACRO(name) \
        struct value \
        builtin_os_ ## name(int argc, struct value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 1); \
        \
                struct value status = ARG(0); \
                if (status.type != VALUE_INTEGER) \
                        vm_panic("the argument to os." #name "() must be an integer"); \
        \
                int s = status.integer; \
        \
                return INTEGER(name(s)); \
        }

WAITMACRO(WIFEXITED)
WAITMACRO(WEXITSTATUS)
WAITMACRO(WIFSIGNALED)
WAITMACRO(WTERMSIG)
WAITMACRO(WIFSTOPPED)
WAITMACRO(WSTOPSIG)
#ifdef WIFCONTINUED
WAITMACRO(WIFCONTINUED)
#endif
#ifdef WCOREDUMP
WAITMACRO(WCOREDUMP)
#endif

#define GETID(name) \
        struct value \
        builtin_os_ ## name (int argc, struct value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 0); \
                return INTEGER(name()); \
        }

#define SETID(name) \
        struct value \
        builtin_os_ ## name (int argc, struct value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 1); \
                struct value id = ARG(0); \
                if (id.type != VALUE_INTEGER) \
                        vm_panic("the argument to os." #name "() must be an integer"); \
                return INTEGER(name(id.integer)); \
        }

GETID(getpid)
GETID(getppid)
GETID(getuid)
GETID(geteuid)
GETID(getgid)
GETID(getegid)
SETID(setuid)
SETID(seteuid)
SETID(setgid)
SETID(setegid)

noreturn struct value
builtin_os_exit(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.exit()", 1);

        struct value status = ARG(0);
        if (status.type != VALUE_INTEGER)
                vm_panic("the argument to os.exit() must be an integer");

        exit(status.integer);
}

struct value
builtin_os_exec(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.exec()", 1);

        struct value cmd = ARG(0);
        if (cmd.type != VALUE_ARRAY)
                vm_panic("the argument to os.exec() must be an array");

        if (cmd.array->count == 0)
                vm_panic("empty array passed to os.exec()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        vm_panic("non-string in array passed to os.exec()");

        vec(char *) argv;
        vec_init(argv);

        for (int i = 0; i < cmd.array->count; ++i) {
                char *arg = gc_alloc(cmd.array->items[i].bytes + 1);
                memcpy(arg, cmd.array->items[i].string, cmd.array->items[i].bytes);
                arg[cmd.array->items[i].bytes] = '\0';
                vec_push(argv, arg);
        }

        vec_push(argv, NULL);

        return INTEGER(execvp(argv.items[0], argv.items));
}

struct value
builtin_os_signal(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.signal()", 1, 2);

        struct value num = ARG(0);

        if (num.type != VALUE_INTEGER)
                vm_panic("the first argument to os.signal() must be an integer");

        if (argc == 2) {
                struct value f = ARG(1);

                struct sigaction act = {0};

                if (f.type == VALUE_NIL) {
                        vm_del_sigfn(num.integer);
                        act.sa_handler = SIG_DFL;
                } else if (CALLABLE(f)) {
                        act.sa_flags = SA_SIGINFO;
                        act.sa_sigaction = vm_do_signal;
                } else {
                        vm_panic("the second argument to os.signal() must be callable");
                }

                int r = sigaction(num.integer, &act, NULL);
                if (r == 0)
                        vm_set_sigfn(num.integer, &f);

                return INTEGER(r);
        } else {
                return vm_get_sigfn(num.integer);
        }

}

struct value
builtin_os_kill(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.kill()", 2);

        struct value pid = ARG(0);
        struct value sig = ARG(1);

        if (pid.type != VALUE_INTEGER || sig.type != VALUE_INTEGER)
                vm_panic("both arguments to os.kill() must be integers");

        return INTEGER(kill(pid.integer, sig.integer));
}

static struct value
timespec_tuple(struct timespec const *ts)
{
        return value_named_tuple(
                "tv_sec",  INTEGER(ts->tv_sec),
                "tv_nsec", INTEGER(ts->tv_nsec),
                NULL
        );
}

static struct timespec
tuple_timespec(char const *func, struct value const *v)
{
        struct value *sec = tuple_get(v, "tv_sec");

        if (sec == NULL || sec->type != VALUE_INTEGER) {
                vm_panic(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        value_show(v),
                        TERM(0),
                        TERM(92),
                        "tv_sec",
                        TERM(0)
                );
        }

        struct value *nsec = tuple_get(v, "tv_nsec");

        if (nsec == NULL || nsec->type != VALUE_INTEGER) {
                vm_panic(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        value_show(v),
                        TERM(0),
                        TERM(92),
                        "tv_nsec",
                        TERM(0)
                );
        }

        return (struct timespec) {
                .tv_sec = sec->integer,
                .tv_nsec = nsec->integer
        };
}

struct value
builtin_os_sleep(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.usleep()", 1);

        struct timespec dur;
        struct timespec rem = {0};

        clockid_t clk = CLOCK_REALTIME;
        int flags = 0;

        bool us = false;

        struct value *abs = NAMED("abs");

        if (abs != NULL && abs->type == VALUE_BOOLEAN && abs->boolean) {
                flags = TIMER_ABSTIME;
        }

        struct value *clock = NAMED("clock");

        if (clock != NULL && clock->type == VALUE_INTEGER) {
                clk = clock->integer;
        }

        struct value *usec = NAMED("usec");

        if (usec != NULL && usec->type == VALUE_BOOLEAN) {
                us = usec->boolean;
        }

        struct value duration = ARG(0);
        if (duration.type == VALUE_INTEGER) {
                if (us) {
                        dur.tv_sec = duration.integer / 1000000;
                        dur.tv_nsec = (duration.integer % 1000000) * 1000ULL;
                } else {
                        dur.tv_sec = duration.integer;
                        dur.tv_nsec = 0;
                }
        } else if (duration.type == VALUE_REAL) {
                if (us) {
                        dur.tv_sec = floor(duration.real / 1000000);
                        dur.tv_nsec = (duration.real - dur.tv_sec * 1000000) * 1000ULL;
                } else {
                        dur.tv_sec = floor(duration.real);
                        dur.tv_nsec = (duration.real - dur.tv_sec) * 1000000000ULL;
                }
        } else if (duration.type == VALUE_TUPLE) {
                dur = tuple_timespec("os.sleep()", &duration);
        } else {
                vm_panic("the argument to os.sleep() must be an integer or a float");
        }

        int ret = clock_nanosleep(clk, flags, &dur, &rem);

        switch (ret) {
        case 0:
                return NIL;
        case EINTR:
                return timespec_tuple(&rem);
        default:
                vm_panic("os.sleep(): invalid argument: clock_nanosleep() returned EINVAL");
        }
}

struct value
builtin_os_usleep(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.usleep()", 1);

        struct value duration = ARG(0);
        if (duration.type != VALUE_INTEGER)
                vm_panic("the argument to os.usleep() must be an integer");

        if (duration.integer < 0)
                vm_panic("negative argument passed to os.usleep()");

        return INTEGER(usleep(duration.integer));
}

struct value
builtin_os_listdir(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.listdir()", 1);

        struct value dir = ARG(0);
        if (dir.type != VALUE_STRING)
                vm_panic("the argument to os.listdir() must be a string");

        B.count = 0;
        vec_push_n(B, dir.string, dir.bytes);
        vec_push(B, '\0');

        DIR *d = opendir(B.items);
        if (d == NULL)
                return NIL;


        struct array *files = value_array_new();

        struct dirent *e;

        while (e = readdir(d), e != NULL)
                if (strcmp(e->d_name, ".") != 0 && strcmp(e->d_name, "..") != 0)
                        vec_push(*files, STRING_CLONE(e->d_name, strlen(e->d_name)));

        closedir(d);

        return ARRAY(files);
}

struct value
builtin_os_realpath(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.realpath()", 1);

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                vm_panic("the argument to os.realpath() must be a string");

        if (path.bytes >= PATH_MAX)
                return NIL;

        char in[PATH_MAX + 1];
        char out[PATH_MAX + 1];

        memcpy(in, path.string, path.bytes);
        in[path.bytes] = '\0';

        char *resolved = realpath(in, out);

        if (resolved == NULL)
                return NIL;

        return STRING_CLONE(out, strlen(out));
}

struct value
builtin_os_stat(int argc, struct value *kwargs)
{
        ASSERT_ARGC("os.stat()", 1);

        struct stat s;

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                vm_panic("the argument to os.stat() must be a string");

        B.count = 0;
        vec_push_n(B, path.string, path.bytes);
        vec_push(B, '\0');

        int r = stat(B.items, &s);
        if (r != 0)
               return NIL;

        return value_named_tuple(
                "st_dev", INTEGER(s.st_dev),
                "st_ino", INTEGER(s.st_ino),
                "st_mode", INTEGER(s.st_mode),
                "st_nlink", INTEGER(s.st_nlink),
                "st_uid", INTEGER(s.st_uid),
                "st_gid", INTEGER(s.st_gid),
                "st_rdev", INTEGER(s.st_rdev),
                "st_size", INTEGER(s.st_size),
                "st_blocks", INTEGER(s.st_blocks),
                "st_blksize", INTEGER(s.st_blksize),
                "st_atim", timespec_tuple(&s.st_atim),
                "st_mtim", timespec_tuple(&s.st_mtim),
                "st_ctim", timespec_tuple(&s.st_ctim),
                NULL
        );

}

struct value
builtin_os_fcntl(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("os.fcntl()", 2, 3);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                vm_panic("the first argument to os.fcntl() must be an integer");

        struct value cmd = ARG(1);
        if (fd.type != VALUE_INTEGER)
                vm_panic("the second argument to os.fcntl() must be an integer");

        if (argc == 2)
                return INTEGER(fcntl(fd.integer, cmd.integer));

        struct value arg = ARG(2);
        switch (cmd.integer) {
        case F_DUPFD:
#ifdef __APPLE__
        case F_DUPFD_CLOEXEC:
#endif
        case F_SETFD:
        case F_SETFL:
        case F_SETSIG:
        case F_SETOWN:
                if (arg.type != VALUE_INTEGER)
                        vm_panic("expected the third argument to be an integer in call to os.fcntl()");
                return INTEGER(fcntl(fd.integer, cmd.integer, (int) arg.integer));
        }

        vm_panic("os.fcntl() functionality not implemented yet");
}

struct value
builtin_errno_get(int argc, struct value *kwargs)
{
        ASSERT_ARGC("errno.get()", 0);
        return INTEGER(errno);
}

struct value
builtin_errno_str(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("errno.str()", 0, 1);

        int e;

        if (argc == 0) {
                e = errno;
        } else {
                if (ARG(0).type != VALUE_INTEGER)
                        vm_panic("the argument to errno.str() must be an integer");
                e = ARG(0).integer;
        }

        char const *s = strerror(e);

        return STRING_CLONE(s, strlen(s));
}

struct value
builtin_time_gettime(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("time.gettime()", 0, 1);

        clockid_t clk;
        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER)
                        vm_panic("the argument to time.gettime() must be an integer");
                clk = v.integer;
        } else {
                clk = CLOCK_REALTIME;
        }

        struct timespec t = {0};
        clock_gettime(clk, &t);

        return timespec_tuple(&t);
}

struct value
builtin_time_utime(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("time.utime()", 0, 1);

        clockid_t clk;
        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER)
                        vm_panic("the argument to time.utime() must be an integer");
                clk = v.integer;
        } else {
                clk = CLOCK_REALTIME;
        }

        struct timespec t;
        clock_gettime(clk, &t);

        return INTEGER(t.tv_sec * 1000 * 1000 + t.tv_nsec / 1000);
}

struct value
builtin_time_localtime(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("time.localtime()", 0, 1);

        time_t t;

        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER) {
                        vm_panic("the argument to time.localtime() must be an integer");
                }
                t = v.integer;
        } else {
                t = time(NULL);
        }

        struct tm r = {0};
        localtime_r(&t, &r);

        return value_named_tuple(
                "sec",   INTEGER(r.tm_sec),
                "min",   INTEGER(r.tm_min),
                "hour",  INTEGER(r.tm_hour),
                "mday",  INTEGER(r.tm_mday),
                "mon",   INTEGER(r.tm_mon),
                "year",  INTEGER(r.tm_year),
                "wday",  INTEGER(r.tm_wday),
                "yday",  INTEGER(r.tm_yday),
                "isdst", BOOLEAN(r.tm_isdst),
                NULL
        );
}

struct value
builtin_time_strftime(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("time.strftime()", 1, 2);

        struct tm t = {0};

        struct value fmt = ARG(0);
        if (fmt.type != VALUE_STRING) {
                vm_panic("the first argument to time.strftime() must be a string");
        }

        if (argc == 2) {
                struct value v = ARG(1);
                if (v.type == VALUE_INTEGER) {
                        time_t sec = v.integer;
                        localtime_r(&sec, &t);
                } else if (v.type == VALUE_TUPLE) {
                        struct value *vp;
                        if ((vp = tuple_get(&v, "sec")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_sec = vp->integer;
                        if ((vp = tuple_get(&v, "min")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_min = vp->integer;
                        if ((vp = tuple_get(&v, "hour")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_hour = vp->integer;
                        if ((vp = tuple_get(&v, "mday")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_mday = vp->integer;
                        if ((vp = tuple_get(&v, "mon")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_mon = vp->integer;
                        if ((vp = tuple_get(&v, "year")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_year = vp->integer;
                        if ((vp = tuple_get(&v, "wday")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_wday = vp->integer;
                        if ((vp = tuple_get(&v, "yday")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_yday = vp->integer;
                        if ((vp = tuple_get(&v, "isdst")) != NULL && vp->type == VALUE_BOOLEAN)
                                t.tm_isdst = vp->boolean;

                } else {
                        vm_panic("the second argument to time.strftime() must be an integer or named tuple");
                }
        } else {
                time_t sec = time(NULL);
                localtime_r(&sec, &t);
        }

        B.count = 0;
        vec_push_n(B, fmt.string, fmt.bytes);
        vec_push(B, '\0');

        int n = strftime(buffer, sizeof buffer, B.items, &t);

        if (n > 0) {
                return STRING_CLONE(buffer, n);
        } else {
                return NIL;
        }
}

struct value
builtin_time_strptime(int argc, struct value *kwargs)
{

        ASSERT_ARGC("time.strptime()", 2);

        struct value s = ARG(0);
        struct value fmt = ARG(1);

        if (s.type != VALUE_STRING || fmt.type != VALUE_STRING) {
                vm_panic("both arguments to time.strptime() must be strings");
        }

        B.count = 0;

        vec_push_n(B, s.string, s.bytes);
        vec_push(B, '\0');

        vec_push_n(B, fmt.string, fmt.bytes);
        vec_push(B, '\0');

        char const *sp = B.items;
        char const *fp = B.items + s.bytes + 1;

        struct tm r = {0};
        strptime(sp, fp, &r);

        return value_named_tuple(
                "sec",   INTEGER(r.tm_sec),
                "min",   INTEGER(r.tm_min),
                "hour",  INTEGER(r.tm_hour),
                "mday",  INTEGER(r.tm_mday),
                "mon",   INTEGER(r.tm_mon),
                "year",  INTEGER(r.tm_year),
                "wday",  INTEGER(r.tm_wday),
                "yday",  INTEGER(r.tm_yday),
                "isdst", BOOLEAN(r.tm_isdst),
                NULL
        );
}

struct value
builtin_time_time(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("time.time()", 0, 1);

        if (argc == 0) {
                return INTEGER(time(NULL));
        }

        struct tm t = {0};
        struct value v = ARG(0);

        if (v.type != VALUE_TUPLE) {
                vm_panic("the argument to time.time() must be a named tuple");
        }

        struct value *vp;

        if ((vp = tuple_get(&v, "sec")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_sec = vp->integer;
        if ((vp = tuple_get(&v, "min")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_min = vp->integer;
        if ((vp = tuple_get(&v, "hour")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_hour = vp->integer;
        if ((vp = tuple_get(&v, "mday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_mday = vp->integer;
        if ((vp = tuple_get(&v, "mon")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_mon = vp->integer;
        if ((vp = tuple_get(&v, "year")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_year = vp->integer;
        if ((vp = tuple_get(&v, "wday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_wday = vp->integer;
        if ((vp = tuple_get(&v, "yday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_yday = vp->integer;
        if ((vp = tuple_get(&v, "isdst")) != NULL && vp->type == VALUE_BOOLEAN)
                t.tm_isdst = vp->boolean;

        struct value *utc = NAMED("utc");

        return INTEGER(
                  utc != NULL && value_truthy(utc)
                ? timegm(&t)
                : mktime(&t)
        );
}

struct value
builtin_stdio_fileno(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fileno()", 1);

        if (ARG(0).type != VALUE_PTR) {
                vm_panic("the argument to stdio.fileno() must be a pointer");
        }

        return INTEGER(fileno(ARG(0).ptr));
}

struct value
builtin_stdio_fdopen(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("stdio.fdopen()", 1, 2);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                vm_panic("the first argument to stdio.fdopen() must be an integer");

        char mode[16] = "a+";
        if (argc == 2) {
                struct value m = ARG(1);
                if (m.type != VALUE_STRING)
                        vm_panic("the second argument to stdio.fdopen() must be a string");
                if (m.bytes >= sizeof mode)
                        vm_panic("invalid mode string %s passed to stdio.fdopen()", value_show(&m));
                memcpy(mode, m.string, m.bytes);
                mode[m.bytes] = '\0';
        }

        FILE *f = fdopen(fd.integer, mode);
        if (f == NULL)
                return NIL;

        return PTR(f);
}

struct value
builtin_stdio_tmpfile(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.tmpfile()", 0);

        FILE *f = tmpfile();

        return (f == NULL) ? NIL : PTR(f);
}

struct value
builtin_stdio_fgets(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fgets()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.fgets() must be a pointer");

        FILE *fp = f.ptr;

        B.count = 0;

        int c;
        while ((c = fgetc_unlocked(fp)) != EOF && c != '\n') {
                vec_push(B, c);
        }

        if (B.count == 0 && c == EOF)
                return NIL;

        struct value s;

        if (B.count == 0) {
                s = (c == EOF) ? NIL : STRING_EMPTY;
        } else {
                s = STRING_CLONE(B.items, B.count);
        }

        return s;
}

struct value
builtin_stdio_read_signed(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("stdio.readSigned()", 1, 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.readSigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        vm_panic("expected intger as second argument to stdio.readSigned() but got: %s", value_show(&ARG(1)));
                }
                size = ARG(1).integer;
        } else {
                size = sizeof size;
        }

        char b[sizeof (intmax_t)];
        int n = min(sizeof b, size);

        ReleaseLock(true);
        if (fread(b, n, 1, fp) != 1) {
                TakeLock();
                return NIL;
        }
        TakeLock();

        switch (size) {
        case (sizeof (char)):      return INTEGER(*(char *)b);
        case (sizeof (short)):     return INTEGER(*(short *)b);
        case (sizeof (int)):       return INTEGER(*(int *)b);
        case (sizeof (long long)): return INTEGER(*(long long *)b);
        default: return NIL;
        }
}

struct value
builtin_stdio_read_unsigned(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("stdio.readUnsigned()", 1, 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.readUnsigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        vm_panic("expected intger as second argument to stdio.readUnsigned() but got: %s", value_show(&ARG(1)));
                }
                size = ARG(1).integer;
        } else {
                size = sizeof size;
        }

        uintmax_t k = 0;

        if (fread_unlocked(&k, min(size, sizeof k), 1, fp) != 1) {
                return NIL;
        } else {
                return INTEGER(k);
        }
}

struct value
builtin_stdio_read_double(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.readDouble()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.readDouble() must be a pointer");

        double x;
        FILE *fp = f.ptr;

        ReleaseLock(true);

        if (fread_unlocked(&x, sizeof x, 1, fp) == 1) {
                TakeLock();
                return REAL(x);
        } else {
                TakeLock();
                return NIL;
        }
}

struct value
builtin_stdio_read_float(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.readFloat()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.readFloat() must be a pointer");

        float x;
        FILE *fp = f.ptr;

        ReleaseLock(true);

        if (fread_unlocked(&x, sizeof x, 1, fp) == 1) {
                TakeLock();
                return REAL(x);
        } else {
                TakeLock();
                return NIL;
        }
}

struct value
builtin_stdio_fread(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("stdio.fread()", 2, 3);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.fread() must be a pointer");

        struct value n = ARG(1);
        if (n.type != VALUE_INTEGER || n.integer < 0)
                vm_panic("the second argument to stdio.fread() must be a non-negative integer");

        struct blob *b;
        bool existing_blob = (argc == 3) && ARG(2).type != VALUE_NIL;

        if (existing_blob) {
                if (ARG(2).type != VALUE_BLOB) {
                        vm_panic("stdio.fread() expects a blob as the third argument but got: %s", value_show(&ARG(2)));
                }
                b = ARG(2).blob;
        } else {
                b = value_blob_new();
        }

        NOGC(b);

        FILE *fp = f.ptr;
        intmax_t bytes = 0;
        int c;

        ReleaseLock(true);
        while (bytes < n.integer && (c = fgetc_unlocked(fp)) != EOF) {
                vec_push(*b, c);
                bytes += 1;
        }
        TakeLock();

        OKGC(b);

        if (existing_blob) {
                return INTEGER(bytes);
        } else {
                if (b->count == 0 && n.integer > 0 && c == EOF)
                        return NIL;

                return BLOB(b);
        }
}

struct value
builtin_stdio_slurp(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.slurp()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.slurp() must be a pointer");

        FILE *fp = f.ptr;
        int c;

        B.count = 0;

        ReleaseLock(true);
        while ((c = fgetc_unlocked(fp)) != EOF) {
                vec_push(B, c);
        }
        TakeLock();

        if (c == EOF && B.count == 0)
                return NIL;

        struct value s = STRING_CLONE(B.items, B.count);

        return s;
}

struct value
builtin_stdio_fgetc(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fgetc()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.fgetc() must be a pointer");

        ReleaseLock(true);
        int c = fgetc_unlocked(f.ptr);
        TakeLock();

        if (c == EOF)
                return NIL;
        else
                return INTEGER(c);
}

struct value
builtin_stdio_fputc(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fputc()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.fputc() must be a pointer");

        if (ARG(1).type != VALUE_INTEGER) {
                vm_panic("the second argument to stdio.fputc() must be an integer");
        }

        ReleaseLock(true);
        int c = fputc_unlocked((int)ARG(1).integer, f.ptr);
        TakeLock();

        if (c == EOF)
                return NIL;
        else
                return INTEGER(c);
}

struct value
builtin_stdio_fwrite(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fwrite()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.fwrite() must be a pointer");

        struct value s = ARG(1);

        switch (s.type) {
        case VALUE_STRING:
                return INTEGER(fwrite_unlocked(s.string, 1, s.bytes, f.ptr));
        case VALUE_BLOB:
                return INTEGER(fwrite_unlocked(s.blob->items, 1, s.blob->count, f.ptr));
        case VALUE_INTEGER:
                return INTEGER(fputc_unlocked((unsigned char)s.integer, f.ptr));
        default:
                vm_panic("invalid type for second argument passed to stdio.fwrite()");
        }
}

struct value
builtin_stdio_puts(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.puts()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.puts() must be a pointer");

        struct value s = ARG(1);

        errno = 0;
        size_t r;

        switch (s.type) {
        case VALUE_STRING:
                r = fwrite_unlocked(s.string, 1, s.bytes, f.ptr);
                if (r < s.bytes && errno != 0)
                        return NIL;
                break;
        case VALUE_BLOB:
                r = fwrite_unlocked(s.blob->items, 1, s.blob->count, f.ptr);
                if (r < s.blob->count && errno != 0)
                        return NIL;
                break;
        default:
                vm_panic("the second argument to stdio.puts() must be a string or a blob");
        }

        if (fputc_unlocked('\n', f.ptr) == EOF)
                return NIL;

        return INTEGER(r + 1);
}

struct value
builtin_stdio_fflush(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fflush()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.fflush() must be a pointer");

        if (fflush(f.ptr) == EOF)
                return NIL;

        return INTEGER(0);
}

struct value
builtin_stdio_fclose(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fclose()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.fclose() must be a pointer");

        if (fclose(f.ptr) == EOF)
                return NIL;

        return INTEGER(0);
}

struct value
builtin_stdio_clearerr(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.clearerr()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the argument to stdio.clearerr() must be a pointer");

        clearerr(f.ptr);

        return NIL;
}

struct value
builtin_stdio_setvbuf(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.setvbuf()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.setvbuf() must be a pointer");

        struct value mode = ARG(1);
        if (mode.type != VALUE_INTEGER)
                vm_panic("the second argument to stdio.setvbuf() must be an integer");

        return INTEGER(setvbuf(f.ptr, NULL, mode.integer, 0));
}

struct value
builtin_stdio_ftell(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.ftell()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.ftell() must be a pointer");

        return INTEGER(ftell(f.ptr));
}

struct value
builtin_stdio_fseek(int argc, struct value *kwargs)
{
        ASSERT_ARGC("stdio.fseek()", 3);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                vm_panic("the first argument to stdio.fseek() must be a pointer");

        struct value off = ARG(1);
        if (off.type != VALUE_INTEGER)
                vm_panic("the second argument to stdio.fseek() must be an integer");

        struct value whence = ARG(2);
        if (whence.type != VALUE_INTEGER)
                vm_panic("the third argument to stdio.fseek() must be an integer");

        return INTEGER(fseek(f.ptr, off.integer, whence.integer));
}

struct value
builtin_object(int argc, struct value *kwargs)
{
        ASSERT_ARGC("object()", 1);

        struct value class = ARG(0);
        if (class.type != VALUE_CLASS)
                vm_panic("the argument to object() must be a class");

        return OBJECT(object_new(), class.class);
}

struct value
builtin_bind(int argc, struct value *kwargs)
{
        ASSERT_ARGC("bind()", 2);

        struct value f = ARG(0);
        struct value x = ARG(1);

        struct value *this;
        struct value *fp;

        if (f.type == VALUE_METHOD) {
                this = gc_alloc_object(sizeof x, GC_VALUE);
                *this = x;
                return METHOD(f.name, f.method, this);
        }

        if (f.type == VALUE_FUNCTION) {
                this = gc_alloc_object(sizeof x, GC_VALUE);
                *this = x;
                fp = gc_alloc_object(sizeof x, GC_VALUE);
                *fp = f;
                return METHOD(f.name, fp, this);
        }

        return f;
}

struct value
builtin_define_method(int argc, struct value *kwargs)
{
        ASSERT_ARGC("defineMethod()", 3);

        struct value class = ARG(0);
        struct value name = ARG(1);
        struct value f = ARG(2);

        if (class.type != VALUE_CLASS) {
                vm_panic("the first argument to defineMethod() must be a class");
        }

        if (name.type != VALUE_STRING) {
                vm_panic("the second argument to defineMethod() must be a string");
        }

        if (f.type != VALUE_FUNCTION) {
                vm_panic("the third argument to defineMethod() must be a function");
        }

        snprintf(buffer, sizeof buffer - 1, "%*s", (int)name.bytes, name.string);

        class_add_method(class.class, buffer, f);

        return NIL;
}

struct value
builtin_apply(int argc, struct value *kwargs)
{
        if (argc < 2) {
                vm_panic("apply() expects at least 2 arguments but got %d", argc);
        }

        struct value f = ARG(0);
        struct value x = ARG(1);

        if (f.type != VALUE_FUNCTION) {
                vm_panic("the first argument to apply() must be a function, got: %s", value_show(&f));
        }

        struct value m = METHOD(f.name, &f, &x);

        for (int i = 2; i < argc; ++i) {
                vm_push(&ARG(i));
        }

        return vm_call(&m, argc - 2);
}

struct value
builtin_type(int argc, struct value *kwargs)
{
        ASSERT_ARGC("type()", 1);

        struct value v = ARG(0);

        if (v.type == VALUE_TUPLE) {
                int n = v.count;

                if (n == 0) {
                        return v;
                }

                struct value *types = gc_alloc_object(sizeof (struct value[n]), GC_TUPLE);

                NOGC(types);

                for (int i = 0; i < n; ++i) {
                        vm_push(&v.items[i]);
                        types[i] = builtin_type(1, NULL);
                        vm_pop();
                }

                OKGC(types);

                return TUPLE(types, NULL, n, false);
        }

        switch (v.type) {
        case VALUE_INTEGER:  return (struct value) { .type = VALUE_CLASS, .class = CLASS_INT     };
        case VALUE_REAL:     return (struct value) { .type = VALUE_CLASS, .class = CLASS_FLOAT   };
        case VALUE_STRING:   return (struct value) { .type = VALUE_CLASS, .class = CLASS_STRING  };
        case VALUE_ARRAY:    return (struct value) { .type = VALUE_CLASS, .class = CLASS_ARRAY   };
        case VALUE_DICT:     return (struct value) { .type = VALUE_CLASS, .class = CLASS_DICT    };
        case VALUE_BLOB:     return (struct value) { .type = VALUE_CLASS, .class = CLASS_BLOB    };
        case VALUE_OBJECT:   return (struct value) { .type = VALUE_CLASS, .class = v.class       };
        case VALUE_BOOLEAN:  return (struct value) { .type = VALUE_CLASS, .class = CLASS_BOOL    };
        case VALUE_REGEX:    return (struct value) { .type = VALUE_CLASS, .class = CLASS_REGEX   };
        case VALUE_CLASS:    return (struct value) { .type = VALUE_CLASS, .class = CLASS_CLASS   };
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_FUNCTION: return (struct value) { .type = VALUE_CLASS, .class = CLASS_FUNCTION };
        default:
        case VALUE_NIL:      return NIL;
        }
}

struct value
builtin_subclass(int argc, struct value *kwargs)
{
        ASSERT_ARGC("subclass?()", 2);

        struct value sub = ARG(0);
        struct value super = ARG(1);

        if (sub.type != VALUE_CLASS || super.type != VALUE_CLASS) {
                vm_panic("the arguments to subclass?() must be classes");
        }

        return BOOLEAN(class_is_subclass(sub.class, super.class));
}

struct value
builtin_members(int argc, struct value *kwargs)
{
        ASSERT_ARGC("members", 1);

        struct value o = ARG(0);

        struct dict *members = dict_new();

        NOGC(members);

        switch (o.type) {
        case VALUE_OBJECT:
                for (int i = 0; i < TABLE_SIZE; ++i) {
                        for (int v = 0; v < o.object->buckets[i].values.count; ++v) {
                                char const *key = o.object->buckets[i].names.items[v];
                                dict_put_member(members, key, o.object->buckets[i].values.items[v]);
                        }
                }

                break;
        case VALUE_TUPLE:
                for (int i = 0; i < o.count; ++i) {
                        if (o.names != NULL && o.names[i] != NULL) {
                                dict_put_value(members, STRING_CLONE(o.names[i], strlen(o.names[i])), o.items[i]);
                        } else {
                                dict_put_value(members, INTEGER(i), o.items[i]);
                        }
                }

                break;
        default:
                OKGC(members);
                return NIL;
        }

        OKGC(members);

        return DICT(members);
}

struct value
builtin_member(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("member()", 2, 3);

        struct value o = ARG(0);
        struct value name = ARG(1);

        if (o.type != VALUE_OBJECT) {
                vm_panic("the first argument to member() must be an object");
        }

        if (name.type != VALUE_STRING) {
                vm_panic("the second argument to member() must be a string");
        }

        if (name.bytes >= sizeof buffer) {
                // sus
                return NIL;
        }

        memcpy(buffer, name.string, name.bytes);
        buffer[name.bytes] = '\0';

        if (argc == 2) {
                struct value *v = table_look(o.object, buffer);

                if (v == NULL) {
                        return NIL;
                }

                return *v;
        } else {
                static _Thread_local struct table NameTable;

                struct value *np = table_look(&NameTable, buffer);

                table_put(
                        o.object,
                        ((np == NULL) ? table_put(&NameTable, buffer, PTR(sclone(buffer))) : np)->ptr,
                        ARG(2)
                );

                return NIL;
        }
}

struct value
builtin_finalizer(int argc, struct value *kwargs)
{
        ASSERT_ARGC("setFinalizer()", 2);

        if (ARG(0).type != VALUE_OBJECT) {
                vm_panic("the first argument to setFinalizer() must be an object");
        }

        if (!CALLABLE(ARG(1))) {
                vm_panic("the second argument to setFinalizer() must be callable");
        }

        ARG(0).object->finalizer = ARG(1);

        return NIL;
}

struct value
builtin_eval(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ty.eval()", 1);

        struct expression *expr = cexpr(&ARG(0));

        return tyeval(expr);
}

struct value
builtin_lex_peek_char(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ty.lex.peekc()", 0);

        parse_sync_lex();

        char b[128];
        int n = lex_peek_char(b);

        if (n == 0) {
                return NIL;
        }

        return STRING_CLONE(b, n);
}

struct value
builtin_lex_next_char(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ty.lex.getc()", 0);

        parse_sync_lex();

        char b[128];

        if (!lex_next_char(b)) {
                return NIL;
        }

        return STRING_CLONE(b, strlen(b));
}

struct value
builtin_token_peek(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("ty.token.peek()", 0, 1);

        if (argc == 1 && ARG(0).type != VALUE_INTEGER) {
                vm_panic("ty.token.peek(): expected integer but got: %s", value_show(&ARG(0)));
        }

        return parse_get_token(argc == 0 ? 0 : ARG(0).integer);
}

struct value
builtin_token_next(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ty.token.next()", 0);

        struct value v = builtin_token_peek(0, NULL);

        parse_next();

        return v;
}

struct value
builtin_parse_expr(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("ty.parse.expr()", 0, 1);

        int prec;

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        vm_panic("ty.parse.expr(): expected integer but got: %s", value_show(&ARG(0)));
                }
                prec = ARG(0).integer;
        } else {
                prec = 0;
        }

        struct value *resolve = NAMED("resolve");

        return parse_get_expr(prec, resolve != NULL && value_truthy(resolve));
}

struct value
builtin_parse_stmt(int argc, struct value *kwargs)
{
        ASSERT_ARGC_2("ty.parse.stmt()", 0, 1);

        int prec;

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        vm_panic("ty.parse.stmt(): expected integer but got: %s", value_show(&ARG(0)));
                }
                prec = ARG(0).integer;
        } else {
                prec = -1;
        }

        return parse_get_stmt(prec);
}

struct value
builtin_parse_fail(int argc, struct value *kwargs)
{
        ASSERT_ARGC("ty.parse.fail()", 1);

        if (ARG(0).type != VALUE_STRING) {
                vm_panic("ty.parse.fail(): expected string but got: %s", value_show(&ARG(0)));
        }

        parse_fail(ARG(0).string, ARG(0).bytes);

        // Unreachable
}
