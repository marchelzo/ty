#include <inttypes.h>
#include <math.h>
#include <errno.h>
#include <limits.h>
#include <string.h>

#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>

#include "tags.h"
#include "value.h"
#include "vm.h"
#include "log.h"
#include "util.h"
#include "json.h"
#include "dict.h"

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
        ASSERT_ARGC("print()", 1);

        if (args->items[0].type == VALUE_STRING) {
                fwrite(args->items[0].string, 1, args->items[0].bytes, stdout);
        } else {
                char *s = value_show(&args->items[0]);
                fputs(s, stdout);
                free(s);
        }

        putchar('\n');

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
builtin_float(value_vector *args)
{
        ASSERT_ARGC("float()", 1);

        struct value v = args->items[0];

        switch (v.type) {
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
        case VALUE_DICT:    v.integer = dict_item_count(a.dict);        return v;
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
                vm_panic("the second argument to os::read() must be non-negative");

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
                        memcpy(arg, cmd.array->items[i].string, cmd.array->items[i].bytes + 1);
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

                struct dict *result = dict_new();
                dict_put_member(result, "stdin",  INTEGER(in[1]));
                dict_put_member(result, "stdout", INTEGER(out[0]));
                dict_put_member(result, "stderr", INTEGER(err[0]));
                dict_put_member(result, "pid",    INTEGER(pid));

                return DICT(result);
        }
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
