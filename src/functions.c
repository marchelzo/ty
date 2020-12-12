#include <inttypes.h>
#include <math.h>
#include <errno.h>
#include <limits.h>
#include <string.h>
#include <stdnoreturn.h>
#include <time.h>

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

#include "tags.h"
#include "value.h"
#include "vm.h"
#include "log.h"
#include "util.h"
#include "json.h"
#include "dict.h"
#include "object.h"
#include "class.h"

static char buffer[1024];

#define ASSERT_ARGC(func, argc) \
        if (args->count != (argc)) { \
                vm_panic(func " expects " #argc " argument(s) but got %zu", args->count); \
        }

#define ASSERT_ARGC_2(func, argc1, argc2) \
        if (args->count != (argc1) && args->count != (argc2)) { \
                vm_panic(func " expects " #argc1 " or " #argc2 " argument(s) but got %zu", args->count); \
        }

#define ASSERT_ARGC_3(func, argc1, argc2, argc3) \
        if (args->count != (argc1) && args->count != (argc2) && args->count != (argc3)) { \
                vm_panic(func " expects " #argc1 ", " #argc2 ", or " #argc3 " argument(s) but got %zu", args->count); \
        }

struct value
builtin_print(value_vector *args)
{
        struct value *f;

        for (int i = 0; i < args->count; ++i) {
                struct value *v = &args->items[i];
                if (i > 0) fputs(", ", stdout);
                if (v->type == VALUE_STRING) {
                        fwrite(v->string, 1, v->bytes, stdout);
                } else {
                        char *s = value_show(&args->items[i]);
                        fputs(s, stdout);
                        free(s);
                }
        }


        putchar('\n');

        return NIL;
}

struct value
builtin_slurp(value_vector *args)
{
        ASSERT_ARGC_2("slurp()", 0, 1);

        char p[PATH_MAX + 1];
        int fd;

        if (args->count == 1) {
                struct value v = args->items[0];

                if (v.type != VALUE_STRING) {
                        vm_panic("slurp() expects a path but got: %s", value_show(&v));
                }

                if (v.bytes >= sizeof p)
                        return NIL;

                memcpy(p, v.string, v.bytes);
                p[v.bytes] = '\0';

                fd = open(p, O_RDONLY);
                if (fd < 0)
                        return NIL;
        } else {
                fd = 0;
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
                int r;
                vec(char) s = {0};

                while ((r = read(fd, p, sizeof p)) > 0) {
                        vec_push_n(s, p, r);
                }
                struct value str = STRING_CLONE(s.items, s.count);
                vec_empty(s);
                return str;
        }

        return NIL;
}

struct value
builtin_die(value_vector *args)
{
        ASSERT_ARGC("die()", 1);

        struct value message = args->items[0];
        if (message.type != VALUE_STRING)
                vm_panic("the argument to die() must be a string");

        vm_panic("%.*s", (int) message.bytes, message.string);
}

struct value
builtin_read(value_vector *args)
{
        ASSERT_ARGC("read()", 0);

        static vec(char) input;
        input.count = 0;

        int c;
        while (c = getchar(), c != EOF && c != '\n')
                vec_push(input, c);

        if (input.count == 0 && c != '\n')
                return NIL;

        return STRING_CLONE(input.items, input.count);
}

struct value
builtin_rand(value_vector *args)
{
        int low, high;

        ASSERT_ARGC_3("rand()", 0, 1, 2);

        if (args->count == 1 && args->items[0].type == VALUE_ARRAY) {
                int n = args->items[0].array->count;
                if (n == 0)
                        return NIL;
                else
                        return args->items[0].array->items[rand() % n];
        }

        for (int i = 0; i < args->count; ++i)
                if (args->items[i].type != VALUE_INTEGER)
                        vm_panic("non-integer passed as argument %d to rand", i + 1);

        switch (args->count) {
        case 0:  low = 0;                      high = RAND_MAX;               break;
        case 1:  low = 0;                      high = args->items[0].integer; break;
        case 2:  low = args->items[0].integer; high = args->items[1].integer; break;
        }

        return INTEGER((rand() % (high - low)) + low);

}

struct value
builtin_abs(value_vector *args)
{
        ASSERT_ARGC("abs()", 1);
        
        struct value x = args->items[0];

        switch (x.type) {
        case VALUE_INTEGER: return INTEGER(llabs(x.integer));
        case VALUE_REAL:    return REAL(fabs(x.real));
        default:
                vm_panic("the argument to abs() must be a number");
        }
}

struct value
builtin_hash(value_vector *args)
{
        ASSERT_ARGC("hash()", 1);
        return INTEGER(value_hash(&args->items[0]));
}

struct value
builtin_float(value_vector *args)
{
        ASSERT_ARGC("float()", 1);

        struct value v = args->items[0];

        switch (v.type) {
        case VALUE_NIL:     return NIL;
        case VALUE_INTEGER: return REAL((float)v.integer);
        case VALUE_REAL:    return v;
        case VALUE_STRING:;
                char buf[128];
                char *end;
                unsigned n = umin(v.bytes, 127);

                memcpy(buf, v.string, n);
                buf[n] = '\0';

                errno = 0;
                float f = strtof(buf, &end);

                if (errno != 0 || *end != '\0')
                        return NIL;

                return REAL(f);
        }

        vm_panic("invalid type passed to float()");
}

struct value
builtin_blob(value_vector *args)
{
        ASSERT_ARGC("blob()", 0);
        return BLOB(value_blob_new());
}

struct value
builtin_int(value_vector *args)
{
        struct value v = INTEGER(0), a, s, b;
        int base;

        char nbuf[64] = {0};

        char const *string = nbuf;

        ASSERT_ARGC_3("int()", 0, 1, 2);

        switch (args->count) {
        case 0: v.integer = 0; return v;
        case 1:                goto coerce;
        case 2:                goto custom_base;
        }

coerce:

        a = args->items[0];
        switch (a.type) {
        case VALUE_INTEGER:                                             return a;
        case VALUE_REAL:    v.integer = a.real;                         return v;
        case VALUE_BOOLEAN: v.integer = a.boolean;                      return v;
        case VALUE_ARRAY:   v.integer = a.array->count;                 return v;
        case VALUE_DICT:    v.integer = a.dict->count;                  return v;
        case VALUE_STRING:  base = 10; memcpy(nbuf, a.string, a.bytes); goto string;
        default:                                                        return NIL;
        }

custom_base:

        s = args->items[0];
        b = args->items[1];

        if (s.type != VALUE_STRING)
                vm_panic("non-string passed as first of two arguments to int()");
        if (b.type != VALUE_INTEGER)
                vm_panic("non-integer passed as second argument to int()");
        if (b.integer < 0 || b.integer == 1 || b.integer > 36)
                vm_panic("invalid base passed to int(): expected 0 or 2..36, but got %d", (int) b.integer);

        base = b.integer;
        memcpy(nbuf, s.string, s.bytes);

        /*
         * The 0b syntax for base-2 integers is not standard C, so the strto* family of
         * functions doesn't recognize it. Thus, we must handle it specially here.
         */
        if (base == 0 && string[0] == '0' && string[1] == 'b') {
                base = 2;
                string += 2;
        }

string:

        errno = 0;

        char *end;
        intmax_t n = strtoimax(string, &end, base);

        if (errno != 0 || *end != '\0')
                return NIL;

        v.integer = n;

        return v;
}

struct value
builtin_str(value_vector *args)
{
        ASSERT_ARGC_2("str()", 0, 1);

        if (args->count == 0)
                return STRING_NOGC(NULL, 0);

        struct value *f;

        struct value arg = args->items[0];
        if (arg.type == VALUE_STRING) {
                return arg;
        } else {
                char *str = value_show(&arg);
                struct value result = STRING_CLONE(str, strlen(str));
                free(str);
                return result;
        }
}

struct value
builtin_bool(value_vector *args)
{
        ASSERT_ARGC("bool()", 1);
        return BOOLEAN(value_truthy(&args->items[0]));
}

struct value
builtin_regex(value_vector *args)
{
        ASSERT_ARGC("regex()", 1);

        struct value pattern = args->items[0];

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

        struct value regex = REGEX(re);
        regex.extra = extra;
        regex.pattern = sclone(buffer);

        return regex;
}

struct value
builtin_min(value_vector *args)
{
        if (args->count < 2)
                vm_panic("min() expects 2 or more arguments, but got %zu", args->count);

        struct value min, v;
        min = args->items[0];

        for (int i = 1; i < args->count; ++i) {
                v = args->items[i];
                if (value_compare(&v, &min) < 0)
                        min = v;
        }

        return min;
}

struct value
builtin_max(value_vector *args)
{
        if (args->count < 2)
                vm_panic("max() expects 2 or more arguments, but got %zu", args->count);

        struct value max, v;
        max = args->items[0];

        for (int i = 1; i < args->count; ++i) {
                v = args->items[i];
                if (value_compare(&v, &max) > 0)
                        max = v;
        }

        return max;
}

struct value
builtin_exp(value_vector *args)
{
        ASSERT_ARGC("math::exp()", 1);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math::exp() must be a float");

        return REAL(expf(x.real));
}

struct value
builtin_log(value_vector *args)
{
        ASSERT_ARGC("math::log()", 1);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math::log() must be a float");

        return REAL(logf(x.real));
}

struct value
builtin_log2(value_vector *args)
{
        ASSERT_ARGC("math::log2()", 1);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math::log2() must be a float");

        return REAL(log2f(x.real));
}

struct value
builtin_pow(value_vector *args)
{
        ASSERT_ARGC("math::pow()", 2);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the first argument to math::pow() must be a float");

        struct value y = args->items[1];
        if (y.type == VALUE_INTEGER)
                y = REAL(y.integer);
        if (y.type != VALUE_REAL)
                vm_panic("the second argument to math::pow() must be a float");

        return REAL(powf(x.real, y.real));
}

struct value
builtin_atan2(value_vector *args)
{
        ASSERT_ARGC("math::atan2()", 2);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the first argument to math::atan2() must be a float");

        struct value y = args->items[1];
        if (y.type == VALUE_INTEGER)
                y = REAL(y.integer);
        if (y.type != VALUE_REAL)
                vm_panic("the second argument to math::atan2() must be a float");

        return REAL(atan2(x.real, y.real));
}

#define MATH_WRAP(func)                                 \
        struct value                                    \
        builtin_ ## func (value_vector *args)           \
        {                                               \
                ASSERT_ARGC("math::" #func "()", 1);    \
                                                        \
                struct value x = args->items[0];        \
                if (x.type == VALUE_INTEGER)            \
                        x = REAL(x.integer);            \
                if (x.type != VALUE_REAL)               \
                        vm_panic("the argument to math::" #func "() must be a float"); \
                                                        \
                return REAL(func ## f (x.real));        \
        }

MATH_WRAP(cos)
MATH_WRAP(sin)
MATH_WRAP(tan)
MATH_WRAP(acos)
MATH_WRAP(asin)
MATH_WRAP(atan)

struct value
builtin_sqrt(value_vector *args)
{
        ASSERT_ARGC("math::sqrt()", 1);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math::sqrt() must be a float");

        return REAL(sqrtf(x.real));
}

struct value
builtin_cbrt(value_vector *args)
{
        ASSERT_ARGC("math::cbrt()", 1);

        struct value x = args->items[0];
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                vm_panic("the argument to math::cbrt() must be a float");

        return REAL(cbrtf(x.real));
}

struct value
builtin_bit_and(value_vector *args)
{
        ASSERT_ARGC("bit::and()", 2);

        struct value a = args->items[0];
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit::and() must be an integer");

        struct value b = args->items[1];
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit::and() must be an integer");

        return INTEGER(a.integer & b.integer);
}

struct value
builtin_bit_or(value_vector *args)
{
        ASSERT_ARGC("bit::or()", 2);

        struct value a = args->items[0];
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit::or() must be an integer");

        struct value b = args->items[1];
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit::or() must be an integer");

        return INTEGER(a.integer | b.integer);
}

struct value
builtin_bit_xor(value_vector *args)
{
        ASSERT_ARGC("bit::xor()", 2);

        struct value a = args->items[0];
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit::xor() must be an integer");

        struct value b = args->items[1];
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit::xor() must be an integer");

        return INTEGER(a.integer ^ b.integer);
}

struct value
builtin_bit_shift_left(value_vector *args)
{
        ASSERT_ARGC("bit::shiftLeft()", 2);

        struct value a = args->items[0];
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit::shiftLeft() must be an integer");

        struct value b = args->items[1];
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit::shiftLeft() must be an integer");

        return INTEGER(a.integer << b.integer);
}

struct value
builtin_bit_shift_right(value_vector *args)
{
        ASSERT_ARGC("bit::shiftRight()", 2);

        struct value a = args->items[0];
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit::shiftRight() must be an integer");

        struct value b = args->items[1];
        if (b.type != VALUE_INTEGER)
                vm_panic("the second argument to bit::shiftRight() must be an integer");

        return INTEGER(a.integer >> b.integer);
}

struct value
builtin_bit_complement(value_vector *args)
{
        ASSERT_ARGC("bit::complement()", 1);

        struct value a = args->items[0];
        if (a.type != VALUE_INTEGER)
                vm_panic("the first argument to bit::complement() must be an integer");

        return INTEGER(~a.integer);
}

struct value
builtin_setenv(value_vector *args)
{
        static vec(char) varbuf;
        static vec(char) valbuf;

        ASSERT_ARGC("setenv()", 2);

        struct value var = args->items[0];
        struct value val = args->items[1];

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
builtin_getenv(value_vector *args)
{
        ASSERT_ARGC("getenv()", 1);

        struct value var = args->items[0];

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
builtin_json_parse(value_vector *args)
{
        ASSERT_ARGC("json::parse()", 1);

        struct value json = args->items[0];
        if (json.type != VALUE_STRING)
                vm_panic("non-string passed to json::parse()");

        return json_parse(json.string, json.bytes);
}

struct value
builtin_json_encode(value_vector *args)
{
        ASSERT_ARGC("json::parse()", 1);
        return json_encode(&args->items[0]);
}

struct value
builtin_os_open(value_vector *args)
{
        ASSERT_ARGC_2("os::open()", 2, 3);

        struct value path = args->items[0];
        if (path.type != VALUE_STRING)
                vm_panic("the path passed to os::open() must be a string");

        static vec(char) pathbuf;
        pathbuf.count = 0;
        vec_push_n(pathbuf, path.string, path.bytes);
        vec_push(pathbuf, '\0');

        unsigned flags = 0;

        struct value flags_array = args->items[1];
        if (flags_array.type != VALUE_ARRAY)
                vm_panic("the second argument to os::open() must be an array");

        for (int i = 0; i < flags_array.array->count; ++i) {
                struct value flag = flags_array.array->items[i];
                if (flag.type != VALUE_INTEGER)
                        vm_panic("non-integer passed as flag to os::open()");
                flags |= (unsigned) flag.integer;
        }

        int fd;

        if (flags & O_CREAT) {
                if (args->count != 3)
                        vm_panic("os::open() called with O_CREAT but no third argument");
                if (args->items[2].type != VALUE_INTEGER)
                        vm_panic("the third argument to os::open() must be an integer");
                fd = open(pathbuf.items, flags, (mode_t) args->items[2].integer);
        } else {
                fd = open(pathbuf.items, flags);
        }


        return INTEGER(fd);
}

struct value
builtin_os_close(value_vector *args)
{
        ASSERT_ARGC("os::close()", 1);

        struct value file = args->items[0];

        if (file.type != VALUE_INTEGER)
                vm_panic("the argument to os::close() must be an integer");

        return INTEGER(close(file.integer));
}

struct value
builtin_os_read(value_vector *args)
{
        ASSERT_ARGC("os::read()", 3);

        struct value file = args->items[0];
        struct value blob = args->items[1];
        struct value n = args->items[2]; 

        if (file.type != VALUE_INTEGER)
                vm_panic("the first argument to os::read() must be an integer");

        if (blob.type != VALUE_BLOB)
                vm_panic("the second argument to os::read() must be a blob");

        if (n.type != VALUE_INTEGER)
                vm_panic("the third argument to os::read() must be an integer");

        if (n.integer < 0)
                vm_panic("the third argument to os::read() must be non-negative");

        vec_reserve(*blob.blob, blob.blob->count + n.integer);

        ssize_t nr = read(file.integer, blob.blob->items + blob.blob->count, n.integer);

        if (nr != -1)
                blob.blob->count += nr;

        return INTEGER(nr);
}

struct value
builtin_os_write(value_vector *args)
{
        ASSERT_ARGC("os::write()", 2);

        struct value file = args->items[0];
        struct value data = args->items[1];

        if (file.type != VALUE_INTEGER)
                vm_panic("the first argument to os::write() must be an integer");

        ssize_t n;

        switch (data.type) {
        case VALUE_BLOB:
                n = write(file.integer, (char *)data.blob->items, data.blob->count);
                break;
        case VALUE_STRING:
                n = write(file.integer, data.string, data.bytes);
                break;
        default:
                vm_panic("invalid argument to os::write()");
        }

        return INTEGER(n);
}

struct value
builtin_os_spawn(value_vector *args)
{
        ASSERT_ARGC("os::spawn()", 1);

        struct value cmd = args->items[0];
        if (cmd.type != VALUE_ARRAY)
                vm_panic("the argument to os::spawn() must be an array");

        if (cmd.array->count == 0)
                vm_panic("empty array passed to os::spawn()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        vm_panic("non-string in array passed to os::spawn()");

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

        if (pipe(err) == -1) {
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
                close(err[0]);
                close(err[1]);
                return NIL;
        }

        pid_t pid = fork();
        switch (pid) {
        case -1:
                close(in[0]);
                close(in[1]);
                close(out[0]);
                close(out[1]);
                close(err[0]);
                close(err[1]);
                close(exc[0]);
                close(exc[1]);
                return NIL;
        case 0:
                close(in[1]);
                close(out[0]);
                close(err[0]);

                if (dup2(in[0], STDIN_FILENO) == -1
                ||  dup2(out[1], STDOUT_FILENO) == -1
                ||  dup2(err[1], STDERR_FILENO) == -1) {
                        write(exc[1], &errno, sizeof errno);
                        exit(EXIT_FAILURE);
                }

                fcntl(exc[1], F_SETFD, FD_CLOEXEC);

                vec(char *) args;
                vec_init(args);

                for (int i = 0; i < cmd.array->count; ++i) {
                        char *arg = alloc(cmd.array->items[i].bytes + 1);
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
                close(err[1]);
                close(exc[1]);

                int status;
                if (read(exc[0], &status, sizeof status) != 0) {
                        errno = status;
                        close(in[1]);
                        close(out[0]);
                        close(err[0]);
                        close(exc[0]);
                        return NIL;
                }

                close(exc[0]);

                struct table *result = object_new();

                table_add(result, "stdin",  INTEGER(in[1]));
                table_add(result, "stdout", INTEGER(out[0]));
                table_add(result, "stderr", INTEGER(err[0]));
                table_add(result, "pid",    INTEGER(pid));

                return OBJECT(result, 0);
        }
}

struct value
builtin_os_fork(value_vector *args)
{
        ASSERT_ARGC("os::fork()", 0);
        return INTEGER(fork());
}

struct value
builtin_os_pipe(value_vector *args)
{
        ASSERT_ARGC("os::pipe()", 0);

        int p[2];

        if (pipe(p) == -1)
                return NIL;

        struct array *fds = value_array_new();

        value_array_push(fds, INTEGER(p[0]));
        value_array_push(fds, INTEGER(p[1]));

        return ARRAY(fds);
}

struct value
builtin_os_dup2(value_vector *args)
{
        ASSERT_ARGC("os::dup2()", 2);

        struct value old = args->items[0];
        struct value new = args->items[1];

        if (old.type != VALUE_INTEGER || new.type != VALUE_INTEGER)
                vm_panic("the arguments to os::dup2() must be integers");

        return INTEGER(dup2(old.integer, new.integer));
}

struct value
builtin_os_socket(value_vector *args)
{
        ASSERT_ARGC("os::socket()", 3);

        struct value domain = args->items[0];
        struct value type = args->items[1];
        struct value protocol = args->items[2];

        if (domain.type != VALUE_INTEGER || type.type != VALUE_INTEGER || protocol.type != VALUE_INTEGER)
                vm_panic("the arguments to os::socket() must be integers");

        return INTEGER(socket(domain.integer, type.integer, protocol.integer));
}

struct value
builtin_os_shutdown(value_vector *args)
{
        ASSERT_ARGC("os::shutdown()", 2);

        struct value fd = args->items[0];
        struct value how = args->items[1];

        if (fd.type != VALUE_INTEGER || how.type != VALUE_INTEGER)
                vm_panic("the arguments to os::shutdown() must be integers");

        return INTEGER(shutdown(fd.integer, how.integer));
}

struct value
builtin_os_listen(value_vector *args)
{
        ASSERT_ARGC("os::listen()", 2);

        struct value sockfd = args->items[0];
        struct value backlog = args->items[1];

        if (sockfd.type != VALUE_INTEGER || backlog.type != VALUE_INTEGER)
                vm_panic("the arguments to os::listen() must be integers");

        return INTEGER(listen(sockfd.integer, backlog.integer));
}

struct value
builtin_os_bind(value_vector *args)
{
        ASSERT_ARGC("os::bind()", 2);

        struct value sockfd = args->items[0];
        struct value addr = args->items[1];

        if (sockfd.type != VALUE_INTEGER)
                vm_panic("the first argument to os::bind() must be an integer");

        if (addr.type != VALUE_DICT)
                vm_panic("the second argument to os::bind() must be a dict");

        struct value *v = dict_get_member(addr.dict, "family");
        if (v == NULL || v->type != VALUE_INTEGER)
                vm_panic("missing or invalid address family in dict passed to os::bind()");

        struct sockaddr_un un_addr;
        struct sockaddr_in in_addr;
        struct in_addr ia;

        struct value *sockaddr = dict_get_member(addr.dict, "address");
        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                return INTEGER(bind(sockfd.integer, (struct sockaddr *)sockaddr->blob->items, sockaddr->blob->count));
        } else switch (v->integer) {
                case AF_UNIX:
                        memset(&un_addr, 0, sizeof un_addr);
                        un_addr.sun_family = AF_UNIX;
                        v = dict_get_member(addr.dict, "path");
                        if (v == NULL || v->type != VALUE_STRING)
                                vm_panic("missing or invalid path in dict passed to os::bind()");
                        memcpy(un_addr.sun_path, v->string, min(v->bytes, sizeof un_addr.sun_path));
                        return INTEGER(bind(sockfd.integer, (struct sockaddr *)&un_addr, sizeof un_addr));
                case AF_INET:
                        memset(&in_addr, 0, sizeof in_addr);
                        in_addr.sin_family = AF_INET;
                        v = dict_get_member(addr.dict, "address");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                vm_panic("missing or invalid address in dict passed to os::bind()");
                        ia.s_addr = htonl(v->integer);
                        in_addr.sin_addr = ia;
                        v = dict_get_member(addr.dict, "port");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                vm_panic("missing or invalid port in dict passed to os::bind()");
                        unsigned short p = htons(v->integer);
                        memcpy(&in_addr.sin_port, &p, sizeof in_addr.sin_port);
                        return INTEGER(bind(sockfd.integer, (struct sockaddr *)&in_addr, sizeof in_addr));
                default:
                        vm_panic("invalid arguments to os::bind()");
        }
}

struct value
builtin_os_getaddrinfo(value_vector *args)
{
        ASSERT_ARGC_2("os::getaddrinfo()", 5, 6);

        struct value host = args->items[0];
        if (host.type != VALUE_STRING)
                vm_panic("the first argument to os::getaddrinfo() must be a string");

        struct value port = args->items[1];
        if (port.type != VALUE_STRING)
                vm_panic("the second argument to os::getaddrinfo() must be a string");

        struct value family = args->items[2];
        if (family.type != VALUE_INTEGER)
                vm_panic("the third argument to os::getaddrinfo() must be an integer");

        struct value type = args->items[3];
        if (type.type != VALUE_INTEGER)
                vm_panic("the fourth argument to os::getaddrinfo() must be an integer");

        struct value protocol = args->items[4];
        if (protocol.type != VALUE_INTEGER)
                vm_panic("the fifth argument to os::getaddrinfo() must be an integer");

        int flags = 0;
        if (args->count == 6) {
                if (args->items[5].type != VALUE_INTEGER)
                        vm_panic("the sixth argument to os::getaddrinfo() must be an integer");
                flags = args->items[5].integer;
        }

        vec(char) node = {0};
        vec_push_n(node, host.string, host.bytes);
        vec_push(node, '\0');

        vec(char) service = {0};
        vec_push_n(service, port.string, port.bytes);
        vec_push(service, '\0');

        struct value results = ARRAY(value_array_new());
        gc_push(&results);

        struct addrinfo *res;
        struct addrinfo hints;

        memset(&hints, 0, sizeof hints);
        hints.ai_flags = flags;
        hints.ai_family = family.integer;
        hints.ai_socktype = type.integer;
        hints.ai_protocol = protocol.integer;

        int r = getaddrinfo(node.items, service.items, &hints, &res);
        if (r == 0) {
                for (struct addrinfo *it = res; it != NULL; it = it->ai_next) {
                        struct value d = DICT(dict_new());
                        value_array_push(results.array, d);
                        dict_put_member(d.dict, "family", INTEGER(it->ai_family));
                        dict_put_member(d.dict, "type", INTEGER(it->ai_socktype));
                        dict_put_member(d.dict, "protocol", INTEGER(it->ai_protocol));
                        struct blob *b = value_blob_new();
                        dict_put_member(d.dict, "address", BLOB(b));
                        vec_push_n(*b, (char *)it->ai_addr, it->ai_addrlen);
                        if (it->ai_canonname != NULL) {
                                dict_put_member(
                                        d.dict,
                                        "canonname",
                                        STRING_CLONE(it->ai_canonname, strlen(it->ai_canonname))
                                );
                        }
                }

                gc_pop();
                freeaddrinfo(res);

                results.tags = tags_lookup("Ok");
                results.type |= VALUE_TAGGED;

                return results;

        } else {
                return (struct value) {
                        .type = VALUE_INTEGER | VALUE_TAGGED,
                        .integer = r,
                        .tags = tags_lookup("Err")
                };
        }
}

struct value
builtin_os_accept(value_vector *args)
{
        ASSERT_ARGC("os::accept()", 1);

        struct value sockfd = args->items[0];

        if (sockfd.type != VALUE_INTEGER)
                vm_panic("the argument to os::listen() must be an integer");

        struct sockaddr a;
        socklen_t n = sizeof a;

        int r = accept(sockfd.integer, &a, &n);
        if (r == -1)
                return NIL;

        struct blob *b = value_blob_new();
        vec_push_n(*b, (char *)&a, n);

        struct array *result = value_array_new();
        NOGC(result);

        value_array_push(result, INTEGER(r));
        value_array_push(result, BLOB(b));

        return ARRAY(result);
}

struct value
builtin_os_poll(value_vector *args)
{
        ASSERT_ARGC("os::poll()", 2);

        struct value fds = args->items[0];
        struct value timeout = args->items[1];

        if (fds.type != VALUE_ARRAY)
                vm_panic("the first argument to os::poll() must be an array");

        if (timeout.type != VALUE_INTEGER)
                vm_panic("the second argument to os::poll() must be an integer");

        static vec(struct pollfd) pfds;
        pfds.count = 0;

        vec_reserve(pfds, fds.array->count);

        struct value *v;
        for (int i = 0; i < fds.array->count; ++i) {
                if (fds.array->items[i].type != VALUE_DICT)
                        vm_panic("non-dict in fds array passed to os::poll()");
                v = dict_get_member(fds.array->items[i].dict, "fd");
                if (v == NULL || v->type != VALUE_INTEGER)
                        vm_panic("all dicts in the fds array passed to os::poll() must have an integer value under the key 'fd'");
                pfds.items[i].fd = v->integer;
                v = dict_get_member(fds.array->items[i].dict, "events");
                if (v != NULL && v->type == VALUE_INTEGER)
                        pfds.items[i].events = v->integer;
                else
                        pfds.items[i].events = POLLIN;
        }

        pfds.count = fds.array->count;

        int ret = poll(pfds.items, pfds.count, timeout.integer);
        if (ret <= 0)
                return INTEGER(ret);

        for (int i = 0; i < fds.array->count; ++i)
                dict_put_member(fds.array->items[i].dict, "revents", INTEGER(pfds.items[i].revents));

        return INTEGER(ret);
}

struct value
builtin_os_waitpid(value_vector *args)
{
        ASSERT_ARGC_2("os::waitpid()", 1, 2);

        struct value pid = args->items[0];

        int flags = 0;
        if (args->count == 2) {
                struct value f = args->items[1];
                if (f.type != VALUE_INTEGER) goto Bad;
                flags = f.integer;
        } else {
        }

        if (pid.type != VALUE_INTEGER) {
Bad:
                vm_panic("both arguments to os::waitpid() must be integers");
        }

        int status;
        int ret = waitpid(pid.integer, &status, flags);

        if (ret <= 0)
                return INTEGER(ret);

        struct array *result = value_array_new();
        NOGC(result);

        value_array_push(result, INTEGER(ret));
        value_array_push(result, INTEGER(status));

        OKGC(result);

        return ARRAY(result);
}

#define WAITMACRO(name) \
        struct value \
        builtin_os_ ## name(value_vector *args) \
        { \
                ASSERT_ARGC("os::" #name, 1); \
        \
                struct value status = args->items[0]; \
                if (status.type != VALUE_INTEGER) \
                        vm_panic("the argument to os::" #name "() must be an integer"); \
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
        builtin_os_ ## name (value_vector *args) \
        { \
                ASSERT_ARGC("os::" #name, 0); \
                return INTEGER(name()); \
        }

#define SETID(name) \
        struct value \
        builtin_os_ ## name (value_vector *args) \
        { \
                ASSERT_ARGC("os::" #name, 1); \
                struct value id = args->items[0]; \
                if (id.type != VALUE_INTEGER) \
                        vm_panic("the argument to os::" #name "() must be an integer"); \
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

struct value
builtin_os_utime(value_vector *args)
{
        ASSERT_ARGC("os::utime()", 0);

        struct timeval t;
        gettimeofday(&t, NULL);

        return INTEGER(t.tv_usec + t.tv_sec * (INTMAX_C(1000000)));
}

noreturn struct value
builtin_os_exit(value_vector *args)
{
        ASSERT_ARGC("os::exit()", 1);

        struct value status = args->items[0];
        if (status.type != VALUE_INTEGER)
                vm_panic("the argument to os::exit() must be an integer");

        exit(status.integer);
}

struct value
builtin_os_exec(value_vector *args)
{
        ASSERT_ARGC("os::exec()", 1);

        struct value cmd = args->items[0];
        if (cmd.type != VALUE_ARRAY)
                vm_panic("the argument to os::exec() must be an array");

        if (cmd.array->count == 0)
                vm_panic("empty array passed to os::exec()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        vm_panic("non-string in array passed to os::exec()");

        vec(char *) argv;
        vec_init(argv);

        for (int i = 0; i < cmd.array->count; ++i) {
                char *arg = alloc(cmd.array->items[i].bytes + 1);
                memcpy(arg, cmd.array->items[i].string, cmd.array->items[i].bytes);
                arg[cmd.array->items[i].bytes] = '\0';
                vec_push(argv, arg);
        }

        vec_push(argv, NULL);

        return INTEGER(execvp(argv.items[0], argv.items));
}

struct value
builtin_os_kill(value_vector *args)
{
        ASSERT_ARGC("os::kill()", 2);

        struct value pid = args->items[0];
        struct value sig = args->items[1];

        if (pid.type != VALUE_INTEGER || sig.type != VALUE_INTEGER)
                vm_panic("both arguments to os::kill() must be integers");

        return INTEGER(kill(pid.integer, sig.integer));
}

struct value
builtin_os_connect(value_vector *args)
{
        static vec(char) host;
        static vec(char) port;

        host.count = 0;
        port.count = 0;

        ASSERT_ARGC("os::connect()", 2);

        struct value h = args->items[0];
        if (h.type != VALUE_STRING)
                vm_panic("the first argument to os::connect() must be a string");

        vec_push_n(host, h.string, h.bytes);
        vec_push(host, '\0');

        struct value p = args->items[1];
        switch (p.type) {
        case VALUE_STRING:
                vec_push_n(port, p.string, p.bytes);
                vec_push(port, '\0');
                break;
        case VALUE_INTEGER:
                vec_reserve(port, 16);
                snprintf(port.items, 16, "%d", (int) p.integer);
                break;
        default:
                vm_panic("the second argument to os::connect() must be a string or an int");
        }

        struct addrinfo hints, *result;
        int conn;

        memset(&hints, 0, sizeof hints);

        hints.ai_family = AF_INET;
        hints.ai_socktype = SOCK_STREAM;

        if (getaddrinfo(host.items, port.items, &hints, &result) != 0)
                return NIL;
        if ((conn = socket(result->ai_family, result->ai_socktype, result->ai_protocol)) == -1)
                return NIL;
        if (connect(conn, result->ai_addr, result->ai_addrlen) == -1) {
                close(conn);
                return NIL;
        }

        return INTEGER(conn);
}

struct value
builtin_os_usleep(value_vector *args)
{
        ASSERT_ARGC("os::usleep()", 1);

        struct value duration = args->items[0];
        if (duration.type != VALUE_INTEGER)
                vm_panic("the argument to os::usleep() must be an integer");

        if (duration.integer < 0)
                vm_panic("negative argument passed to os::usleep()");

        return INTEGER(usleep(duration.integer));
}

struct value
builtin_os_listdir(value_vector *args)
{
        ASSERT_ARGC("os::listdir()", 1);

        struct value dir = args->items[0];
        if (dir.type != VALUE_STRING)
                vm_panic("the argument to os::listdir() must be a string");

        static vec(char) dirbuf;
        dirbuf.count = 0;
        vec_push_n(dirbuf, dir.string, dir.bytes);
        vec_push(dirbuf, '\0');

        DIR *d = opendir(dirbuf.items);
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
builtin_os_stat(value_vector *args)
{
        ASSERT_ARGC("os::stat()", 1);

        struct stat s;

        struct value path = args->items[0];
        if (path.type != VALUE_STRING)
                vm_panic("the argument to os::stat() must be a string");

       static vec(char) pb;
       pb.count = 0;
       vec_push_n(pb, path.string, path.bytes);
       vec_push(pb, '\0');

       int r = stat(pb.items, &s);
       if (r != 0)
               return NIL;

       struct table *t = object_new();
       table_add(t, "st_dev", INTEGER(s.st_dev));
       table_add(t, "st_ino", INTEGER(s.st_ino));
       table_add(t, "st_mode", INTEGER(s.st_mode));
       table_add(t, "st_nlink", INTEGER(s.st_nlink));
       table_add(t, "st_uid", INTEGER(s.st_uid));
       table_add(t, "st_gid", INTEGER(s.st_gid));
       table_add(t, "st_rdev", INTEGER(s.st_rdev));
       table_add(t, "st_size", INTEGER(s.st_size));
       table_add(t, "st_blocks", INTEGER(s.st_blocks));
       table_add(t, "st_blksize", INTEGER(s.st_blksize));

       struct table *atim = object_new();
       struct table *mtim = object_new();
       struct table *ctim = object_new();

       table_add(atim, "tv_sec", INTEGER(s.st_atim.tv_sec));
       table_add(atim, "tv_nsec", INTEGER(s.st_atim.tv_nsec));

       table_add(mtim, "tv_sec", INTEGER(s.st_mtim.tv_sec));
       table_add(mtim, "tv_nsec", INTEGER(s.st_mtim.tv_nsec));

       table_add(ctim, "tv_sec", INTEGER(s.st_ctim.tv_sec));
       table_add(ctim, "tv_nsec", INTEGER(s.st_ctim.tv_nsec));

       table_add(t, "st_atim", OBJECT(atim, 0));
       table_add(t, "st_mtim", OBJECT(mtim, 0));
       table_add(t, "st_ctim", OBJECT(ctim, 0));

       return OBJECT(t, 0);

}

struct value
builtin_os_fcntl(value_vector *args)
{
        ASSERT_ARGC_2("os::fcntl()", 2, 3);

        struct value fd = args->items[0];
        if (fd.type != VALUE_INTEGER)
                vm_panic("the first argument to os::fcntl() must be an integer");

        struct value cmd = args->items[1];
        if (fd.type != VALUE_INTEGER)
                vm_panic("the second argument to os::fcntl() must be an integer");

        if (args->count == 2)
                return INTEGER(fcntl(fd.integer, cmd.integer));

        struct value arg = args->items[2];
        switch (cmd.integer) {
        case F_DUPFD:
#ifdef __APPLE__
        case F_DUPFD_CLOEXEC:
#endif
        case F_SETFD:
        case F_SETFL:
                if (arg.type != VALUE_INTEGER)
                        vm_panic("the third argument to os::fcntl() must be an integer when it is called with F_DUPFD");
                return INTEGER(fcntl(fd.integer, cmd.integer, (int) arg.integer));
        }

        vm_panic("os::fcntl() functionality not implemented yet");
}

struct value
builtin_errno_get(value_vector *args)
{
        ASSERT_ARGC("errno::get()", 0);
        return INTEGER(errno);
}

struct value
builtin_errno_str(value_vector *args)
{
        ASSERT_ARGC_2("errno::str()", 0, 1);

        int e;

        if (args->count == 0) {
                e = errno;
        } else {
                if (args->items[0].type != VALUE_INTEGER)
                        vm_panic("the argument to errno::str() must be an integer");
                e = args->items[0].integer;
        }

        char const *s = strerror(e);

        return STRING_CLONE(s, strlen(s));
}

struct value
builtin_time_utime(value_vector *args)
{
        ASSERT_ARGC("time::time()", 0);

        struct timespec t;
        clock_gettime(CLOCK_REALTIME, &t);

        return INTEGER(t.tv_sec * 1000 * 1000 + t.tv_nsec / 1000);
}

struct value
builtin_time_localtime(value_vector *args)
{
        ASSERT_ARGC_2("time::localtime()", 0, 1);

        time_t t;

        if (args->count == 1) {
                struct value v = args->items[0];
                if (v.type != VALUE_INTEGER) {
                        vm_panic("the argument to time::localtime() must be an integer");
                }
                t = v.integer;
        } else {
                t = time(NULL);
        }

        struct tm r = {0};
        localtime_r(&t, &r);

        struct table *o = object_new();

        NOGC(o);
        table_add(o, "sec", INTEGER(r.tm_sec));
        table_add(o, "min", INTEGER(r.tm_min));
        table_add(o, "hour", INTEGER(r.tm_hour));
        table_add(o, "mday", INTEGER(r.tm_mday));
        table_add(o, "mon", INTEGER(r.tm_mon));
        table_add(o, "year", INTEGER(r.tm_year));
        table_add(o, "wday", INTEGER(r.tm_wday));
        table_add(o, "yday", INTEGER(r.tm_yday));
        table_add(o, "isdst", BOOLEAN(r.tm_isdst));
        OKGC(o);

        return OBJECT(o, 0);
}

struct value
builtin_time_strftime(value_vector *args)
{
        ASSERT_ARGC_2("time::strftime()", 1, 2);

        struct tm t = {0};

        struct value fmt = args->items[0];
        if (fmt.type != VALUE_STRING) {
                vm_panic("the first argument to time::strftime() must be a string");
        }

        if (args->count == 2) {
                struct value v = args->items[1];
                if (v.type == VALUE_INTEGER) {
                        time_t sec = v.integer;
                        localtime_r(&sec, &t);
                } else if (v.type == VALUE_OBJECT) {
                        struct value *vp;
                        struct table *o = v.object;
                        if ((vp = table_lookup(o, "sec")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_sec = vp->integer;
                        if ((vp = table_lookup(o, "min")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_min = vp->integer;
                        if ((vp = table_lookup(o, "hour")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_hour = vp->integer;
                        if ((vp = table_lookup(o, "mday")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_mday = vp->integer;
                        if ((vp = table_lookup(o, "mon")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_mon = vp->integer;
                        if ((vp = table_lookup(o, "year")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_year = vp->integer;
                        if ((vp = table_lookup(o, "wday")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_wday = vp->integer;
                        if ((vp = table_lookup(o, "yday")) != NULL && vp->type == VALUE_INTEGER)
                                t.tm_yday = vp->integer;
                        if ((vp = table_lookup(o, "isdst")) != NULL && vp->type == VALUE_BOOLEAN)
                                t.tm_isdst = vp->boolean;

                } else {
                        vm_panic("the second argument to time::strftime() must be an integer or object");
                }
        } else {
                time_t sec = time(NULL);
                localtime_r(&sec, &t);
        }

        vec(char) fb;
        vec_init(fb);
        vec_push_n(fb, fmt.string, fmt.bytes);
        vec_push(fb, '\0');
        
        char b[512];
        int n = strftime(b, sizeof b, fb.items, &t);

        vec_empty(fb);

        if (n > 0) {
                return STRING_CLONE(b, n);
        } else {
                return NIL;
        }
}

struct value
builtin_time_strptime(value_vector *args)
{

        ASSERT_ARGC("time::strptime()", 2);

        struct value s = args->items[0];
        struct value fmt = args->items[1];

        if (s.type != VALUE_STRING || fmt.type != VALUE_STRING) {
                vm_panic("both arguments to time::strptime() must be strings");
        }

        vec(char) sb;
        vec(char) fb;

        vec_init(sb);
        vec_init(fb);

        vec_push_n(sb, s.string, s.bytes);
        vec_push_n(fb, fmt.string, fmt.bytes);

        vec_push(sb, '\0');
        vec_push(fb, '\0');
        
        struct tm r = {0};
        strptime(sb.items, fb.items, &r);

        vec_empty(sb);
        vec_empty(fb);
        
        struct table *o = object_new();

        NOGC(o);
        table_add(o, "sec", INTEGER(r.tm_sec));
        table_add(o, "min", INTEGER(r.tm_min));
        table_add(o, "hour", INTEGER(r.tm_hour));
        table_add(o, "mday", INTEGER(r.tm_mday));
        table_add(o, "mon", INTEGER(r.tm_mon));
        table_add(o, "year", INTEGER(r.tm_year));
        table_add(o, "wday", INTEGER(r.tm_wday));
        table_add(o, "yday", INTEGER(r.tm_yday));
        table_add(o, "isdst", BOOLEAN(r.tm_isdst));
        OKGC(o);

        return OBJECT(o, 0);
}

struct value
builtin_time_time(value_vector *args)
{
        ASSERT_ARGC_2("time::time()", 0, 1);

        if (args->count == 0) {
                return INTEGER(time(NULL));
        }

        struct tm t = {0};
        struct value v = args->items[0];

        if (v.type != VALUE_OBJECT) {
                vm_panic("the argument to time::time() must be an object");
        }

        struct value *vp;
        struct table *o = v.object;

        if ((vp = table_lookup(o, "sec")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_sec = vp->integer;
        if ((vp = table_lookup(o, "min")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_min = vp->integer;
        if ((vp = table_lookup(o, "hour")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_hour = vp->integer;
        if ((vp = table_lookup(o, "mday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_mday = vp->integer;
        if ((vp = table_lookup(o, "mon")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_mon = vp->integer;
        if ((vp = table_lookup(o, "year")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_year = vp->integer;
        if ((vp = table_lookup(o, "wday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_wday = vp->integer;
        if ((vp = table_lookup(o, "yday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_yday = vp->integer;
        if ((vp = table_lookup(o, "isdst")) != NULL && vp->type == VALUE_BOOLEAN)
                t.tm_isdst = vp->boolean;

        return INTEGER(mktime(&t));
}
