#ifdef _WIN32
#include <winsock2.h> // must be included before <windows.h>
#include <ws2tcpip.h>
#endif

#include <inttypes.h>
#include <math.h>
#include <errno.h>
#include <limits.h>
#include <string.h>
#include <stdnoreturn.h>
#include <time.h>
#include <locale.h>
#include <ctype.h>
#include <setjmp.h>

#include "tthread.h"
#include "polyfill_time.h"
#include "polyfill_unistd.h"
#include "polyfill_stdatomic.h"
#include <openssl/md5.h>
#include <openssl/sha.h>
#include <utf8proc.h>
#include <signal.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

#define NOT_ON_WINDOWS(name) zP("%s is not implemented in Windows builds of Ty", #name);

#ifdef __linux__
#include <sys/epoll.h>
#endif

#ifdef __APPLE__
#include <sys/sysctl.h>
#endif

#ifdef _WIN32
#include <windows.h>
#include <io.h>
#define fstat _fstat
typedef struct stat StatStruct;
typedef unsigned short mode_t;
#define fgetc_unlocked _fgetc_nolock
#define fputc_unlocked _fputc_nolock
#define fwrite_unlocked _fwrite_nolock
#define fread_unlocked _fread_nolock
#else
typedef struct stat StatStruct;
#include <termios.h>
#include <sys/mman.h>
#include <dirent.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netdb.h>
#include <sys/wait.h>
#include <netdb.h>
#include <netinet/ip.h>
#include <sys/time.h>
#include <sys/file.h>
#include <poll.h>
#include <sys/mman.h>
#include <pthread.h>
#include <spawn.h>
extern char **environ;
#endif

#include "functions.h"
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

#ifdef __APPLE__
#define fputc_unlocked fputc
#define fgetc_unlocked fgetc
#define fwrite_unlocked fwrite
#define fread_unlocked fread
#endif

static _Thread_local char buffer[1024 * 1024 * 4];
static _Thread_local vec(char) B;
static _Atomic(uint64_t) tid = 1;

#define TDB_MUST_BE(x) if (1) {         \
        if (!TDB_IS(x)) zP(             \
                "%s(): tdb must be %s", \
                __func__,               \
                #x                      \
        );                              \
} else ((void)0)

#define TDB_MUST_NOT_BE(x) if (1) {         \
        if (TDB_IS(x)) zP(                  \
                "%s(): error: "             \
                "tdb is %s",                \
                __func__,                   \
                #x                          \
        );                                  \
} else ((void)0)


#define ASSERT_ARGC(func, ac) if (argc != (ac)) {       \
        if (argc != (ac)) zP(                           \
                func                                    \
                " expects "                             \
                #ac                                     \
                " argument(s) but got %d",              \
                argc                                    \
        );                                              \
} else ((void)0)

#define ASSERT_ARGC_2(func, ac1, ac2) \
        if (argc != (ac1) && argc != (ac2)) { \
                zP(func " expects " #ac1 " or " #ac2 " argument(s) but got %d", argc); \
        }

#define ASSERT_ARGC_3(func, ac1, ac2, ac3) \
        if (argc != (ac1) && argc != (ac2) && argc != (ac3)) { \
                zP(func " expects " #ac1 ", " #ac2 ", or " #ac3 " argument(s) but got %d", argc); \
        }

#define EVAL_PROLOGUE "(do {"
#define EVAL_EPILOGUE "})"


inline static void
GetCurrentTimespec(struct timespec* ts)
{
#ifdef _WIN32
        FILETIME ft;
        GetSystemTimeAsFileTime(&ft);
        uint64_t totalUs = (((uint64_t)ft.dwHighDateTime << 32) + ft.dwLowDateTime - 0x19DB1DED53E8000ULL) / 10ULL;
        ts->tv_sec = totalUs / 1000000ULL;
        ts->tv_nsec = (totalUs % 1000000ULL) * 1000ULL;
#else
        clock_gettime(CLOCK_REALTIME, ts);
#endif
}

static intmax_t
doprint(Ty *ty, int argc, struct value *kwargs, FILE *f)
{
        Value *sep = NAMED("sep");

        if (sep != NULL && sep->type != VALUE_STRING) {
                zP(
                        "print(): %s%ssep%s must be a string",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        Value *end = NAMED("end");

        if (end != NULL && end->type != VALUE_STRING) {
                zP(
                        "print(): %s%send%s must be a string",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        Value *flush = NAMED("flush");
        bool do_flush = flush != NULL && value_truthy(ty, flush);

        lGv(true);
        flockfile(f);

        intmax_t written = 0;

        for (int i = 0; i < argc; ++i) {
                Value *v = &ARG(i);

                if (i > 0) {
                        if (sep != NULL) {
                                if (fwrite(sep->string, 1, sep->bytes, f) < sep->bytes) {
                                        lTk();
                                        return -1;
                                }
                                written += sep->bytes;
                        } else {
                                if (fputs(", ", stdout) == EOF) {
                                        lTk();
                                        return -1;
                                }
                                written += 2;
                        }
                }

                char const  *s;
                int64_t      n;
                bool need_free = false;

                switch (v->type) {
                case VALUE_STRING:
                        s = v->string;
                        n = v->bytes;
                        break;
                case VALUE_BLOB:
                        s = (char const *)v->blob->items;
                        n = v->blob->count;
                        break;
                case VALUE_PTR:
                        s = v->ptr;
                        n = strlen(v->ptr);
                        break;
                default:
                        lTk();
                        s = value_show_color(ty, &ARG(i));
                        lGv(true);
                        n = strlen(s);
                        need_free = true;
                        break;
                }

                if (fwrite(s, 1, n, f) < n) {
                        if (need_free) {
                                mF((char *)s);
                        }

                        lTk();

                        return -1;
                }

                if (need_free) {
                        mF((char *)s);
                }

                written += n;
        }


        if (end != NULL) {
                if (fwrite(end->string, 1, end->bytes, f) < end->bytes) {
                        lTk();
                        return -1;
                }
                written += end->bytes;
        } else {
                if (fputc('\n', f) == EOF) {
                        lTk();
                        return -1;
                } else {
                        written += 1;
                }
        }

        if (do_flush) {
                fflush(f);
        }

        funlockfile(f);
        lTk();

        return written;
}

BUILTIN_FUNCTION(print)
{
        Value *file = NAMED("file");

        if (file == NULL) {
                return INTEGER(doprint(ty, argc, kwargs, stdout));
        } else if (LIKELY(file->type == VALUE_PTR)) {
                return INTEGER(doprint(ty, argc, kwargs, file->ptr));
        } else {
                zP("print(): bad `file` argument: %s", VSC(file));
        }
}

BUILTIN_FUNCTION(eprint)
{
        return INTEGER(doprint(ty, argc, kwargs, stderr));
}

BUILTIN_FUNCTION(slurp)
{
        ASSERT_ARGC_2("slurp()", 0, 1);

#if defined(_WIN32) && !defined(PATH_MAX)
#define PATH_MAX MAX_PATH
#endif
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

#ifdef _WIN32
                fd = _open(p, _O_RDONLY);
#else
                fd = open(p, O_RDONLY);
#endif
                if (fd < 0)
                        return NIL;

                need_close = true;
        } else if (ARG(0).type == VALUE_INTEGER) {
                fd = ARG(0).integer;
        } else {
                zP("the argument to slurp() must be a path or a file descriptor");
        }

        StatStruct st;
        if (fstat(fd, &st) != 0) {
                close(fd);
                return NIL;
        }

        Value *mmap_arg = NAMED("mmap");

        bool try_mmap = (mmap_arg == NULL)
                     || value_truthy(ty, mmap_arg);

#ifdef _WIN32
#define S_ISLNK(m) 0
#endif
#if !defined(S_ISREG) && defined(S_IFMT) && defined(S_IFREG)
#define S_ISREG(m) (((m) & S_IFMT) == S_IFREG)
#endif
#if !defined(S_ISDIR)
#define S_ISDIR(m) (((m) & S_IFMT) == S_IFDIR)
#endif

#ifndef _WIN32
        size_t n = st.st_size;

        if (
                try_mmap
             && (S_ISREG(st.st_mode) || S_ISLNK(st.st_mode))
             && (n > 0) // If stat() says size==0 skip to read() anyway, e.g. for procfs
        ) {
                void *m = mmap(NULL, n, PROT_READ, MAP_SHARED, fd, 0);
                if (m != MAP_FAILED) {
                        char *s = value_string_alloc(ty, n);
                        memcpy(s, m, n);
                        munmap(m, n);
                        close(fd);
                        return STRING(s, n);
                }
        }
#endif
        if (!S_ISDIR(st.st_mode)) {
                FILE *f = fdopen(fd, "r");
                int r;

                lGv(true);

                B.count = 0;

                while (!feof(f) && (r = fread(buffer, 1, sizeof buffer, f)) > 0) {
                        vvPn(B, buffer, r);
                }

                lTk();

                struct value str = vSs(B.items, B.count);

                if (need_close)
                        fclose(f);

                return str;
        }

        return NIL;
}

BUILTIN_FUNCTION(ident)
{
        ASSERT_ARGC("ident()", 1);

        Value v = ARG(0);

        switch (v.type) {
        case VALUE_ARRAY:   return PTR(v.array);
        case VALUE_DICT:    return PTR(v.dict);
        case VALUE_OBJECT:  return PTR(v.object);
        case VALUE_BLOB:    return PTR(v.blob);
        case VALUE_TUPLE:   return PTR(v.items);
        case VALUE_STRING:  return PAIR(PTR((void *)v.string), INTEGER(v.bytes));
        default:            return v;
        }
}

BUILTIN_FUNCTION(die)
{
        ASSERT_ARGC("die()", 1);

        struct value message = ARG(0);
        if (message.type != VALUE_STRING)
                zP("the argument to die() must be a string");

        zP("%.*s", (int) message.bytes, message.string);
}

BUILTIN_FUNCTION(read)
{
        ASSERT_ARGC("readLine()", 0);

        B.count = 0;

        lGv(true);

        int c;
        while (c = getchar(), c != EOF && c != '\n')
                vvP(B, c);

        lTk();

        if (B.count == 0 && c != '\n')
                return NIL;

        return vSs(B.items, B.count);
}

inline static uint64_t
rotl(uint64_t x, int k)
{
        return (x << k) | (x >> (64 - k));
}

inline static uint64_t
xoshiro256ss(Ty *ty)
{
        uint64_t const result = rotl(ty->prng[1] * 5, 7) * 9;
        uint64_t const t = ty->prng[1] << 17;

        ty->prng[2] ^= ty->prng[0];
        ty->prng[3] ^= ty->prng[1];
        ty->prng[1] ^= ty->prng[2];
        ty->prng[0] ^= ty->prng[3];

        ty->prng[2] ^= t;
        ty->prng[3] = rotl(ty->prng[3], 45);

        return result;
}

BUILTIN_FUNCTION(rand)
{
        int64_t low;
        int64_t high;

        ASSERT_ARGC_3("rand()", 0, 1, 2);

        uint64_t z = xoshiro256ss(ty);

        if (argc == 0) {
                return REAL(z / (double)UINT64_MAX);
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
                        zP("non-integer passed as argument %d to rand", i + 1);

        switch (argc) {
        case 1:  low = 0;              high = ARG(0).integer; break;
        case 2:  low = ARG(0).integer; high = ARG(1).integer; break;
        }

        return INTEGER((z % (high - low)) + low);

}

BUILTIN_FUNCTION(abs)
{
        ASSERT_ARGC("abs()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return INTEGER(llabs(x.integer));
        case VALUE_REAL:    return REAL(fabs(x.real));
        default:
                zP("the argument to abs() must be a number");
        }
}

BUILTIN_FUNCTION(gcd)
{
        ASSERT_ARGC("gcd()", 2);

        struct value t = ARG(0);
        struct value u = ARG(1);

        if (t.type == VALUE_REAL) t = INTEGER(t.real);
        if (u.type == VALUE_REAL) u = INTEGER(u.real);

        if (t.type != VALUE_INTEGER || u.type != VALUE_INTEGER) {
                zP("both arguments to gcd() must be integers");
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

BUILTIN_FUNCTION(lcm)
{
        ASSERT_ARGC("lcm()", 2);

        struct value t = ARG(0);
        struct value u = ARG(1);

        if (t.type == VALUE_REAL) t = INTEGER(t.real);
        if (u.type == VALUE_REAL) u = INTEGER(u.real);

        if (t.type != VALUE_INTEGER || u.type != VALUE_INTEGER) {
                zP("both arguments to lcm() must be integers");
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

BUILTIN_FUNCTION(round)
{
        ASSERT_ARGC("round()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return REAL(x.integer);
        case VALUE_REAL:    return REAL(round(x.real));
        default:
                zP("the argument to round() must be a number");
        }
}

BUILTIN_FUNCTION(iround)
{
        ASSERT_ARGC("iround()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return INTEGER(llround(x.real));
        default:
                zP("the argument to iround() must be a number");
        }
}

BUILTIN_FUNCTION(ceil)
{
        ASSERT_ARGC("ceil()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return INTEGER(ceil(x.real));
        default:
                zP("the argument to ceil() must be a number");
        }
}

BUILTIN_FUNCTION(floor)
{
        ASSERT_ARGC("floor()", 1);

        struct value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return x;
        case VALUE_REAL:    return INTEGER(floor(x.real));
        default:
                zP("the argument to floor() must be a number");
        }
}

BUILTIN_FUNCTION(chr)
{
        ASSERT_ARGC("chr()", 1);

        struct value k = ARG(0);

        if (k.type != VALUE_INTEGER)
                zP("the argument to chr() must be an integer");

        if (!utf8proc_codepoint_valid(k.integer))
                return NIL;

        char b[4];
        int n = utf8proc_encode_char(k.integer, b);

        return vSs(b, n);
}

BUILTIN_FUNCTION(ord)
{
        ASSERT_ARGC("ord()", 1);

        struct value c = ARG(0);

        if (c.type != VALUE_STRING)
                zP("the argument to ord() must be a string");

        int codepoint;
        int n = utf8proc_iterate(c.string, c.bytes, &codepoint);

        if (codepoint == -1 || n < c.bytes)
                return NIL;

        return INTEGER(codepoint);
}

BUILTIN_FUNCTION(hash)
{
        ASSERT_ARGC("hash()", 1);
        return INTEGER(value_hash(ty, &ARG(0)));
}

BUILTIN_FUNCTION(float)
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

        zP("invalid type passed to float()");
}

BUILTIN_FUNCTION(isnan)
{
        ASSERT_ARGC("nan?()", 1);

        if (ARG(0).type != VALUE_REAL) {
                zP("nan?() expects a float but got: %s", value_show(ty, &ARG(0)));
        }

        return BOOLEAN(isnan(ARG(0).real));
}

BUILTIN_FUNCTION(blob)
{
        ASSERT_ARGC("blob()", 0);
        return BLOB(value_blob_new(ty));
}

BUILTIN_FUNCTION(int)
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
        default:
                return NIL;
        case VALUE_INTEGER:                                               return a;
        case VALUE_REAL:    v.integer = a.real;                           return v;
        case VALUE_BOOLEAN: v.integer = a.boolean;                        return v;
        case VALUE_ARRAY:   v.integer = a.array->count;                   return v;
        case VALUE_DICT:    v.integer = a.dict->count;                    return v;
        case VALUE_BLOB:    v.integer = a.blob->count;                    return v;
        case VALUE_PTR:     return INTEGER((uintptr_t)a.ptr);
        case VALUE_STRING:
                base = 0;
                if (a.bytes >= sizeof buffer)
                        goto TooBig;
                memcpy(buffer, a.string, a.bytes);
                buffer[a.bytes] = '\0';
                goto String;
        }

CustomBase:

        s = ARG(0);
        b = ARG(1);

        if (s.type != VALUE_STRING)
                zP("non-string passed as first of two arguments to int()");
        if (b.type != VALUE_INTEGER)
                zP("non-integer passed as second argument to int()");
        if (b.integer < 0 || b.integer == 1 || b.integer > 36)
                zP("invalid base passed to int(): expected 0 or 2..36, but got %"PRIiMAX, b.integer);

        base = b.integer;

        if (s.bytes >= sizeof buffer)
                goto TooBig;

        memcpy(buffer, s.string, s.bytes);
        buffer[s.bytes] = '\0';

String:
        /*
         * The 0b syntax for base-2 integers is not standard C, so the strto* family of
         * functions doesn't recognize it. Thus, we must handle it specially here.
         */
        if (base == 0 && string[0] == '0' && string[1] == 'b') {
                base = 2;
                string += 2;
        }

        errno = 0;

        char *end;
        intmax_t n = strtoimax(string, &end, base);

        if (errno != 0 || *end != '\0' || end == string)
                return NIL;

        return INTEGER(n);

TooBig:
        errno = ERANGE;
        return NIL;
}

BUILTIN_FUNCTION(show)
{
        ASSERT_ARGC("show()", 1);

        struct value arg = ARG(0);
        Value *color = NAMED("color");

        bool use_color = (color == NULL) ? isatty(1) : value_truthy(ty, color);

        char *str = use_color ? value_show_color(ty, &arg) : value_show(ty, &arg);
        struct value result = vSs(str, strlen(str));
        mF(str);

        return result;
}

BUILTIN_FUNCTION(str)
{
        ASSERT_ARGC_2("str()", 0, 1);

        if (argc == 0)
                return STRING_NOGC(NULL, 0);

        struct value arg = ARG(0);
        if (arg.type == VALUE_STRING) {
                return arg;
        } else {
                char *str = value_show(ty, &arg);
                struct value result = vSs(str, strlen(str));
                mF(str);
                return result;
        }
}

inline static void
BufferCString(Value const *s)
{
        size_t n = umin(sizeof buffer - 1, s->bytes);
        memcpy(buffer, s->string, n);
        buffer[n] = '\0';
}

inline static bool
isflag(int c)
{
        return c == '0' ||
               c == '-' ||
               c == '+' ||
               c == ' ' ||
               c == '#' ||
               c == '\'';
}

struct fspec {
        bool alt;
        bool blank;
        bool left;
        bool sep;
        bool sign;
        bool zero;
        char xsep;
        char prec[64];
        char width[64];
};

inline static int
getfmt(char const **s, char const *end, struct fspec *out)
{
        int w = 0;
        int p = 0;

        out->alt    = false;
        out->blank  = false;
        out->left   = false;
        out->sep    = false;
        out->sign   = false;
        out->zero   = false;
        out->xsep   = '\0';

        bool flags = true;

        while (flags && *s < end) {
                switch (**s) {
                case '+':  out->sign  = true; break;
                case '-':  out->left  = true; break;
                case '0':  out->zero  = true; break;
                case '#':  out->alt   = true; break;
                case '\'': out->sep   = true; break;
                case ' ':  out->blank = true; break;
                default:   flags = false; continue;
                }
                *s += 1;
        }

        if (*s < end && **s == '*') {
                if (w + 1 >= sizeof out->width)
                        return '\0';
                out->width[w++] = *(*s)++;
        } else while (*s < end && isdigit(**s)) {
                if (w + 1 >= sizeof out->width)
                        return '\0';
                out->width[w++] = *(*s)++;
        }

        if (*s < end && **s == '.') {
                if (p + 1 >= sizeof out->prec)
                        return '\0';

                out->prec[p++] = *(*s)++;

                while (*s < end && **s == ' ') ++*s;

                if (*s < end && **s == '*') {
                        if (p + 1 >= sizeof out->prec)
                                return '\0';
                        out->prec[p++] = *(*s)++;
                } else while (*s < end && isdigit(**s)) {
                        if (p + 1 >= sizeof out->prec)
                                return '\0';
                        out->prec[p++] = *(*s)++;
                }
        }

        if (**s == ' ' || **s == '_' || **s == ',' || **s == '\'')
                out->xsep = *(*s)++;

        while (*s < end && **s == ' ') ++*s;

        out->width[w] = '\0';
        out->prec[p] = '\0';

        return (*s < end) ? *(*s)++ : '\0';
}

inline static noreturn void
BadFmt(Ty *ty, char const *spec, int n, Value const *v)
{
        zP(
                "fmt(): format specifier %.*s doesn't match value provided: %s",
                n,
                spec,
                VSC(v)
        );
}

inline static intmax_t
int_from(Ty *ty, Value const *v, char const *spec, int n)
{
        switch (v->type) {
        case VALUE_INTEGER: return v->integer;
        case VALUE_REAL:    return v->real;
        case VALUE_BOOLEAN: return v->boolean;
        default: BadFmt(ty, spec, n, v);
        }
}

inline static double
float_from(Ty *ty, Value const *v, char const *spec, int n)
{
        switch (v->type) {
        case VALUE_INTEGER: return v->integer;
        case VALUE_REAL:    return v->real;
        default: BadFmt(ty, spec, n, v);
        }
}

inline static void
utobsx(char *s, uintmax_t z)
{
        int const w = CHAR_BIT * sizeof (uintmax_t);
        uintmax_t m = UINTMAX_C(1) << (w - 1);

        while (m != 0 && (z & m) == 0) { m >>= 1; }
        do { *s++ = '0' + !!(z & m); m >>= 1; } while (m != 0);

        *s = '\0';
}

inline static void
AddThousandsSep(char *s, int c)
{
        char const *start = s;

        while (!isdigit(*s)) ++s;
        while (*s == '0')    ++s;

        char const *in = s;

        char b[512];
        int i = 0;

        int w = strcspn(in, " .,");
        int n = (w + 2) / 3 - 1;

        if (n > 0) switch (w % 3) {
        case 0: do { b[i++] = *in++;
        case 2:      b[i++] = *in++;
        case 1:      b[i++] = *in++;
                     b[i++] = c;
                     s -= (s > start) && (s[-1] == ' ' || s[-1] == '0');
                } while (--n > 0);
        }

        while (*in != '\0') b[i++] = *in++;

        i = min(i, 255);

        ((char *)memcpy(s, b, i))[i] = '\0';
}

BUILTIN_FUNCTION(fmt)
{
        if (argc == 0) {
                return STRING_EMPTY;
        }

        if (ARG(0).type != VALUE_STRING) {
                zP("fmt(): expected string but got: %s", VSC(&ARG(0)));
        }

        char const *fmt = ARG(0).string;
        size_t n = ARG(0).bytes;
        int ai = 0;

        struct fspec spec;

        int len;

        vec(char) cs = {0};
        vec(char) sb = {0};

        void const *p;

        for (size_t i = 0; i < n; ++i) {
                if (fmt[i] == '%') {
                        /* %% is just a literal % like printf() */
                        if (i + 1 < n && fmt[i + 1] == '%') {
                                xvP(cs, '%');
                                i += 1;
                                continue;
                        }

                        char const *start = fmt + i;
                        char const *end = start + 1;

                        int t = getfmt(&end, fmt + n, &spec);
                        int nspec = (int)(end - start);

                        i  = (end - 1) - fmt;

                        if (t == '\0') {
BadFormatSpecifier:
                                zP("fmt(): invalid format specifier: %.*s", nspec, start);
                        }

                        if (spec.width[0] == '*') {
                                if (++ai >= argc) {
                                        goto MissingArgument;
                                }

                                if (ARG(ai).type != VALUE_INTEGER) {
                                        zP(
                                                "fmt(): invalid width for format specifier %.*s: %s",
                                                nspec,
                                                start,
                                                VSC(&ARG(ai))
                                        );
                                }

                                snprintf(spec.width, sizeof spec.width, "%"PRIiMAX, ARG(ai).integer);
                        }

                        if (spec.prec[0] == '*') {
                                if (++ai >= argc) {
                                        goto MissingArgument;
                                }

                                if (ARG(ai).type != VALUE_INTEGER) {
                                        zP(
                                                "fmt(): invalid precision for format specifier %.*s: %s",
                                                nspec,
                                                start,
                                                VSC(&ARG(ai))
                                        );
                                }

                                snprintf(spec.prec, sizeof spec.prec, "%"PRIiMAX, ARG(ai).integer);
                        }

                        if (++ai >= argc) {
MissingArgument:
                                zP(
                                        "fmt(): missing argument %d for format specifier %.*s",
                                        ai + 1,
                                        nspec,
                                        start
                                );
                        }

                        Value arg = ARG(ai);

                        char b[256];
                        char scratch[256];
                        int si = 0;

                        scratch[si++] = '%';

                        if (spec.alt)   scratch[si++] = '#';
                        if (spec.blank) scratch[si++] = ' ';
                        if (spec.sign)  scratch[si++] = '+';
                        if (spec.zero)  scratch[si++] = '0';
                        if (spec.left)  scratch[si++] = '-';

                        int wlen = strlen(spec.width);
                        int plen = strlen(spec.prec);

                        memcpy(scratch + si, spec.width, wlen);
                        si += wlen;

                        memcpy(scratch + si, spec.prec, plen);
                        si += plen;

                        switch (t) {
                        case 'd':
                        case 'i':
                        case 'o':
                        case 'u':
                        case 'x':
                        case 'X':
                                scratch[si++] = 'j';
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                snprintf(
                                        buffer,
                                        sizeof buffer,
                                        scratch,
                                        int_from(ty, &arg, start, nspec)
                                );

                                if (spec.xsep != '\0') {
                                        AddThousandsSep(&buffer[spec.blank], spec.xsep);
                                }

                                break;
                        case 'b':
                                scratch[si++] = 's';
                                scratch[si] = '\0';

                                utobsx(b, (uintmax_t)int_from(ty, &arg, start, nspec));

                                snprintf(
                                        buffer,
                                        sizeof buffer,
                                        scratch,
                                        b
                                );

                                break;
                        case 'f':
                        case 'F':
                        case 'g':
                        case 'G':
                        case 'e':
                        case 'E':
                        case 'a':
                        case 'A':
                                scratch[si++] = 'l';
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                snprintf(
                                        buffer,
                                        sizeof buffer,
                                        scratch,
                                        float_from(ty, &arg, start, nspec)
                                );

                                if (spec.xsep != '\0') {
                                        AddThousandsSep(&buffer[spec.blank], spec.xsep);
                                }

                                break;
                        case 'q':
                                scratch[si++] = 'l';
                                scratch[si++] = 'f';
                                scratch[si++] = '%';
                                scratch[si++] = '%';
                                scratch[si] = '\0';

                                len = snprintf(
                                        buffer,
                                        sizeof buffer,
                                        scratch,
                                        100.0 * float_from(ty, &arg, start, nspec)
                                );

                                if (buffer[0] == '0' || buffer[spec.blank] == ' ') {
                                        xvPn(cs, buffer + 1, len - 1);
                                        continue;
                                }

                                for (int i = len - 1; buffer[i - 1] == ' '; --i) {
                                        SWAP(char, buffer[i], buffer[i - 1]);
                                }

                                if (buffer[len - 1] == ' ') {
                                        buffer[--len] = '\0';
                                }

                                break;
                        case 's':
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                sb.count = 0;

                                switch (arg.type) {
                                case VALUE_STRING:
                                        xvPn(sb, arg.string, arg.bytes);
                                        xvP(sb, '\0');
                                        p = sb.items;
                                        break;
                                case VALUE_BLOB:
                                        xvPn(sb, arg.blob->items, arg.blob->count);
                                        xvP(sb, '\0');
                                        p = sb.items;
                                        break;
                                case VALUE_PTR:
                                        p = arg.ptr;
                                        break;
                                default:
                                        BadFmt(ty, start, nspec, &arg);
                                }

                                snprintf(
                                        buffer,
                                        sizeof buffer,
                                        scratch,
                                        p
                                );

                                break;
                        case 'p':
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                switch (arg.type) {
                                case VALUE_STRING:   p = arg.string; break;
                                case VALUE_BLOB:     p = arg.blob;   break;
                                case VALUE_OBJECT:   p = arg.object; break;
                                case VALUE_PTR:      p = arg.ptr;    break;
                                case VALUE_DICT:     p = arg.dict;   break;
                                case VALUE_ARRAY:    p = arg.array;  break;
                                case VALUE_FUNCTION: p = arg.info;   break;
                                case VALUE_REGEX:    p = arg.regex;  break;
                                default: BadFmt(ty, start, nspec, &arg);
                                }

                                snprintf(
                                        buffer,
                                        sizeof buffer,
                                        scratch,
                                        p
                                );

                                break;
                        default:
                                goto BadFormatSpecifier;
                        }

                        xvPn(cs, buffer, strlen(buffer));
                } else {
                        xvP(cs, fmt[i]);
                }
        }

        Value s = vSs(cs.items, cs.count);

        free(cs.items);
        free(sb.items);

        return s;
}

BUILTIN_FUNCTION(bool)
{
        ASSERT_ARGC("bool()", 1);
        return BOOLEAN(value_truthy(ty, &ARG(0)));
}

BUILTIN_FUNCTION(dict)
{
        ASSERT_ARGC("dict()", 0);
        return DICT(dict_new(ty));
}

BUILTIN_FUNCTION(array)
{
        ASSERT_ARGC("array()", 0);
        return ARRAY(vA());
}

BUILTIN_FUNCTION(tuple)
{
        int named = 0;
        Dict *d = (kwargs != NULL) ? kwargs->dict : NULL;

        if (d != NULL) for (int i = 0; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        named += 1;
                }
        }

        Value tuple = vT(argc + named);

        if (named > 0) {
                NOGC(tuple.items);
                tuple.ids = mAo((argc + named) * sizeof (int), GC_ANY);
                OKGC(tuple.items);
        }

        for (int i = 0; i < argc; ++i) {
                tuple.items[i] = ARG(i);
                if (tuple.ids != NULL) {
                        tuple.ids[i] = -1;
                }
        }

        if (d != NULL) for (int i = 0, n = argc; i < d->size; ++i) {
                if (d->keys[i].type != 0) {
                        BufferCString(&d->keys[i]);
                        tuple.items[n] = d->values[i];
                        tuple.ids[n] = intern(&xD.members, buffer)->id;
                        n += 1;
                }
        }

        return tuple;
}

BUILTIN_FUNCTION(regex)
{
        ASSERT_ARGC("regex()", 1);

        struct value pattern = ARG(0);

        if (pattern.type == VALUE_REGEX)
                return pattern;

        if (pattern.type != VALUE_STRING)
                zP("non-string passed to regex()");

        snprintf(buffer, sizeof buffer, "%.*s", (int) pattern.bytes, pattern.string);

        char const *err;
        int off;

        pcre *re = pcre_compile(buffer, 0, &err, &off, NULL);
        if (re == NULL)
                return NIL;

        pcre_extra *extra = pcre_study(re, PCRE_STUDY_EXTRA_NEEDED | PCRE_STUDY_JIT_COMPILE, &err);
        if (extra == NULL)
                return NIL;

        if (JITStack != NULL)
                pcre_assign_jit_stack(extra, NULL, JITStack);

        struct regex *r = mAo(sizeof *r, GC_REGEX);
        r->pcre = re;
        r->extra = extra;
        r->pattern = sclone(ty, buffer);
        r->gc = true;

        return REGEX(r);
}

BUILTIN_FUNCTION(min)
{
        if (argc < 2)
                zP("min() expects 2 or more arguments, but got %d", argc);

        struct value min, v;
        min = ARG(0);

        for (int i = 1; i < argc; ++i) {
                v = ARG(i);
                if (value_compare(ty, &v, &min) < 0)
                        min = v;
        }

        return min;
}

BUILTIN_FUNCTION(max)
{
        if (argc < 2)
                zP("max() expects 2 or more arguments, but got %d", argc);

        struct value max, v;
        max = ARG(0);

        for (int i = 1; i < argc; ++i) {
                v = ARG(i);
                if (value_compare(ty, &v, &max) > 0)
                        max = v;
        }

        return max;
}

BUILTIN_FUNCTION(exp)
{
        ASSERT_ARGC("math.exp()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the argument to math.exp() must be a float");

        return REAL(exp(x.real));
}

BUILTIN_FUNCTION(log)
{
        ASSERT_ARGC("math.log()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the argument to math.log() must be a float");

        return REAL(log(x.real));
}

BUILTIN_FUNCTION(log2)
{
        ASSERT_ARGC("math.log2()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the argument to math.log2() must be a float");

        return REAL(log2(x.real));
}

BUILTIN_FUNCTION(log10)
{
        ASSERT_ARGC("math.log10()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the argument to math.log10() must be a float");

        return REAL(log10(x.real));
}

BUILTIN_FUNCTION(pow)
{
        ASSERT_ARGC("math.pow()", 2);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the first argument to math.pow() must be a float");

        struct value y = ARG(1);
        if (y.type == VALUE_INTEGER)
                y = REAL(y.integer);
        if (y.type != VALUE_REAL)
                zP("the second argument to math.pow() must be a float");

        return REAL(pow(x.real, y.real));
}

BUILTIN_FUNCTION(atan2)
{
        ASSERT_ARGC("math.atan2()", 2);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the first argument to math.atan2() must be a float");

        struct value y = ARG(1);
        if (y.type == VALUE_INTEGER)
                y = REAL(y.integer);
        if (y.type != VALUE_REAL)
                zP("the second argument to math.atan2() must be a float");

        return REAL(atan2(x.real, y.real));
}

#define MATH_WRAP(func)                                 \
        struct value                                    \
        builtin_ ## func (Ty *ty, int argc, struct value *kwargs)           \
        {                                               \
                ASSERT_ARGC("math." #func "()", 1);    \
                                                        \
                struct value x = ARG(0);        \
                if (x.type == VALUE_INTEGER)            \
                        x = REAL(x.integer);            \
                if (x.type != VALUE_REAL)               \
                        zP("the argument to math." #func "() must be a float"); \
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

BUILTIN_FUNCTION(sqrt)
{
        ASSERT_ARGC("math.sqrt()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the argument to math.sqrt() must be a float");

        return REAL(sqrt(x.real));
}

BUILTIN_FUNCTION(cbrt)
{
        ASSERT_ARGC("math.cbrt()", 1);

        struct value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.integer);
        if (x.type != VALUE_REAL)
                zP("the argument to math.cbrt() must be a float");

        return REAL(cbrt(x.real));
}

BUILTIN_FUNCTION(bit_and)
{
        ASSERT_ARGC("bit.and()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.and() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.and() must be an integer");

        return INTEGER((uintmax_t)a.integer & (uintmax_t)b.integer);
}

BUILTIN_FUNCTION(bit_or)
{
        ASSERT_ARGC("bit.or()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.or() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.or() must be an integer");

        return INTEGER((uintmax_t)a.integer | (uintmax_t)b.integer);
}

BUILTIN_FUNCTION(bit_xor)
{
        ASSERT_ARGC("bit.xor()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.xor() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.xor() must be an integer");

        return INTEGER((uintmax_t)a.integer ^ (uintmax_t)b.integer);
}

BUILTIN_FUNCTION(bit_shift_left)
{
        ASSERT_ARGC("bit.shiftLeft()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.shiftLeft() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.shiftLeft() must be an integer");

        return INTEGER((uintmax_t)a.integer << (uintmax_t)b.integer);
}

BUILTIN_FUNCTION(bit_shift_right)
{
        ASSERT_ARGC("bit.shiftRight()", 2);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.shiftRight() must be an integer");

        struct value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.shiftRight() must be an integer");

        return INTEGER((uintmax_t)a.integer >> (uintmax_t)b.integer);
}

BUILTIN_FUNCTION(bit_complement)
{
        ASSERT_ARGC("bit.complement()", 1);

        struct value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.complement() must be an integer");

        return INTEGER(~(uintmax_t)a.integer);
}

BUILTIN_FUNCTION(setenv)
{
        static _Thread_local vec(char) varbuf;
        static _Thread_local vec(char) valbuf;

        ASSERT_ARGC("setenv()", 2);

        struct value var = ARG(0);
        struct value val = ARG(1);

        if (var.type != VALUE_STRING || val.type != VALUE_STRING)
                zP("both arguments to setenv() must be strings");

        vvPn(varbuf, var.string, var.bytes);
        vvP(varbuf, '\0');

        vvPn(valbuf, val.string, val.bytes);
        vvP(valbuf, '\0');

#ifdef _WIN32
        SetEnvironmentVariableA(varbuf.items, valbuf.items);
#else
        setenv(varbuf.items, valbuf.items, 1);
#endif

        varbuf.count = 0;
        valbuf.count = 0;

        return NIL;
}

BUILTIN_FUNCTION(getenv)
{
        ASSERT_ARGC("getenv()", 1);

        struct value var = ARG(0);

        if (var.type != VALUE_STRING)
                zP("non-string passed to getenv()");

        char buffer[256];

        if (var.bytes >= sizeof buffer)
                zP("argument to getenv() is too long: '%.10s..'", var.string);

        memcpy(buffer, var.string, var.bytes);
        buffer[var.bytes] = '\0';

        char const *val = getenv(buffer);

        if (val == NULL)
                return NIL;
        else
                return STRING_NOGC(val, strlen(val));
}

BUILTIN_FUNCTION(locale_setlocale)
{
        ASSERT_ARGC("locale.setlocale()", 2);

        if (ARG(0).type != VALUE_INTEGER) {
                zP("locale.setlocale(): expected integer but got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_STRING) {
                zP("locale.setlocale(): expected string but got: %s", VSC(&ARG(0)));
        }

        size_t n = min(ARG(1).bytes, sizeof buffer - 1);
        memcpy(buffer, ARG(1).string, n);
        buffer[n] = '\0';

        setlocale(ARG(0).integer, buffer);

        return NIL;
}

BUILTIN_FUNCTION(json_parse)
{
        ASSERT_ARGC("json.parse(ty)", 1);

        struct value json = ARG(0);
        if (json.type != VALUE_STRING)
                zP("non-string passed to json.parse(ty)");

        return json_parse(ty, json.string, json.bytes);
}

BUILTIN_FUNCTION(json_encode)
{
        ASSERT_ARGC("json.parse(ty)", 1);
        return json_encode(ty, &ARG(0));
}

BUILTIN_FUNCTION(sha256)
{
        ASSERT_ARGC("sha256", 1);

        struct value s = ARG(0);
        unsigned char digest[SHA256_DIGEST_LENGTH];

        if (s.type == VALUE_STRING) {
                SHA256((unsigned char const *)s.string, s.bytes, digest);
        } else if (s.type == VALUE_BLOB) {
                SHA256(s.blob->items, s.blob->count, digest);
        }

        struct blob *b = value_blob_new(ty);
        vvPn(*b, digest, sizeof digest);

        return BLOB(b);
}

BUILTIN_FUNCTION(sha1)
{
        ASSERT_ARGC("sha1", 1);

        struct value s = ARG(0);
        unsigned char digest[SHA_DIGEST_LENGTH];

        if (s.type == VALUE_STRING) {
                SHA1((unsigned char const *)s.string, s.bytes, digest);
        } else if (s.type == VALUE_BLOB) {
                SHA1(s.blob->items, s.blob->count, digest);
        } else {
                zP("md5(): invalid argument: %s", VSC(&s));
        }

        GC_STOP();
        struct blob *b = value_blob_new(ty);
        vvPn(*b, digest, sizeof digest);
        GC_RESUME();

        return BLOB(b);
}

BUILTIN_FUNCTION(md5)
{
        ASSERT_ARGC("md5", 1);

        struct value s = ARG(0);
        unsigned char digest[MD5_DIGEST_LENGTH];

        if (s.type == VALUE_STRING) {
                MD5((unsigned char const *)s.string, s.bytes, digest);
        } else if (s.type == VALUE_BLOB) {
                MD5(s.blob->items, s.blob->count, digest);
        } else {
                zP("md5(): invalid argument: %s", VSC(&s));
        }

        struct blob *b = value_blob_new(ty);
        vvPn(*b, digest, sizeof digest);

        return BLOB(b);
}

static bool
b64dec(Ty *ty, char const *s, size_t n)
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
                vvP(B, (s1 << 2) | (s2 >> 4));
                vvP(B, ((s2 & 0x0F) << 4) | (s3 >> 2));
                vvP(B, ((s3 & 0x03) << 6) | s4);
        }

        memset(g, 0, sizeof g);
        memcpy(g, s + 4*d.quot, d.rem);

        switch (d.rem) {
        case 3:
                s1 = table[g[0]];
                s2 = table[g[1]];
                s3 = table[g[2]];
                vvP(B, (s1 << 2) | (s2 >> 4));
                vvP(B, ((s2 & 0x0F) << 4) | (s3 >> 2));
                break;
        case 2:
                s1 = table[g[0]];
                s2 = table[g[1]];
                vvP(B, (s1 << 2) | (s2 >> 4));
                break;
        case 1:
                s1 = table[g[0]];
                vvP(B, s1 << 2);
                break;
        }

        return true;
}

static void
b64enc(Ty *ty, char const *s, size_t n)
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
                vvP(B, table[g[0] >> 2]);
                vvP(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                vvP(B, table[((g[1] & 0x0F) << 2) | (g[2] >> 6)]);
                vvP(B, table[g[2] & 0x3F]);
        }

        memset(g, 0, sizeof g);
        memcpy(g, s + 3*d.quot, d.rem);

        switch (d.rem) {
        case 2:
                vvP(B, table[g[0] >> 2]);
                vvP(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                vvP(B, table[((g[1] & 0x0F) << 2) | (g[2] >> 6)]);
                vvP(B, '=');
                break;
        case 1:
                vvP(B, table[g[0] >> 2]);
                vvP(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                vvP(B, '=');
                vvP(B, '=');
                break;
        }
}

BUILTIN_FUNCTION(base64_encode)
{
        ASSERT_ARGC_2("base64.encode()", 1, 2);

        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("base64.encode(): the second argument must be an integer");
                }

                size_t n = ARG(1).integer;

                switch (ARG(0).type) {
                case VALUE_PTR:
                        b64enc(ty, ARG(0).ptr, n);
                        break;
                default:
                        goto Bad;
                }
        } else {
                switch (ARG(0).type) {
                case VALUE_STRING:
                        b64enc(ty, ARG(0).string, ARG(0).bytes);
                        break;
                case VALUE_BLOB:
                        b64enc(ty, (char *)ARG(0).blob->items, ARG(0).blob->count);
                        break;
                default:
                        goto Bad;
                }
        }

        return vSs(B.items, B.count);

Bad:
        zP("base64.encode(): invalid argument(s)");

}

BUILTIN_FUNCTION(base64_decode)
{
        ASSERT_ARGC("base64.decode()", 1);

        if (ARG(0).type != VALUE_STRING) {
                zP("base64.decode(): argument must be a string");
        }

        if (!b64dec(ty, ARG(0).string, ARG(0).bytes)) {
                return NIL;
        }

        struct blob *b = value_blob_new(ty);

        NOGC(b);
        vvPn(*b, B.items, B.count);
        OKGC(b);

        return BLOB(b);
}

BUILTIN_FUNCTION(os_umask)
{
        ASSERT_ARGC("os.umask()", 1);

        struct value mask = ARG(0);
        if (mask.type != VALUE_INTEGER) {
                zP("the argument to os.umask() must be an integer");
        }

        return INTEGER(umask(mask.integer));
}

BUILTIN_FUNCTION(os_open)
{
        ASSERT_ARGC_2("os.open()", 2, 3);

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                zP("the path passed to os.open() must be a string");

        B.count = 0;

        vvPn(B, path.string, path.bytes);
        vvP(B, '\0');

        struct value flags = ARG(1);
        if (flags.type != VALUE_INTEGER)
                zP("the second argument to os.open() must be an integer (flags)");

        int fd;

        if (flags.integer & O_CREAT) {
                if (argc != 3)
                        zP("os.open() called with O_CREAT but no third argument");
                if (ARG(2).type != VALUE_INTEGER)
                        zP("the third argument to os.open() must be an integer");
                fd = open(B.items, flags.integer, (mode_t) ARG(2).integer);
        } else {
                fd = open(B.items, flags.integer);
        }


        return INTEGER(fd);
}

BUILTIN_FUNCTION(os_close)
{
        ASSERT_ARGC("os.close()", 1);

        struct value file = ARG(0);

        if (file.type != VALUE_INTEGER)
                zP("the argument to os.close() must be an integer");

        return INTEGER(close(file.integer));
}

static char *
make_temp_dir(char *template)
{
#ifdef _WIN32
    char tempPath[MAX_PATH];
    char tempFile[MAX_PATH];

    // Get the path to the temporary folder
    if (GetTempPath(MAX_PATH, tempPath) == 0)
    {
        return NULL;
    }

    // Generate a temporary file name
    if (GetTempFileName(tempPath, "tmp", 0, tempFile) == 0)
    {
        return NULL;
    }

    // Remove the temporary file created by GetTempFileName
    DeleteFile(tempFile);

    // Create a directory with the temporary file name
    if (CreateDirectory(tempFile, NULL) == 0)
    {
        return NULL;
    }

    // Copy the resulting directory name into the template
    strcpy(template, tempFile);
    return template;
#else
    if (mkdtemp(template) == NULL)
    {
        return NULL;
    }
    return template;
#endif
}

BUILTIN_FUNCTION(os_mkdtemp)
{
        char template[PATH_MAX + 1] = {0};

        if (argc > 1) {
                zP("os.mkdtemp() expects 0 or 1 arguments but got %d", argc);
        }

        if (argc == 1 && ARG(0).type != VALUE_NIL) {
                struct value s = ARG(0);
                if (s.type != VALUE_STRING)
                        zP("the first argument to os.mktemp() must be a string");
                /* -8 to make room for the .XXXXXX suffix and NUL byte */
                memcpy(template, s.string, min(s.bytes, sizeof template - 8));
        } else {
                strcpy(template, "tmp");
        }

        strcat(template, ".XXXXXX");

        if (make_temp_dir(template) == NULL) {
                return NIL;
        }

        return vSs(template, strlen(template));
}

static int
make_temp_file(char *template, int flags)
{
    int fd;

#ifdef _WIN32
    if (_mktemp_s(template, strlen(template) + 1) != 0)
    {
        return -1;
    }

    fd = _open(template, flags | _O_CREAT | _O_EXCL, _S_IREAD | _S_IWRITE);
    if (fd == -1)
    {
        return -1;
    }
#else
    if (flags != -1)
    {
        fd = mkostemp(template, flags);
    }
    else
    {
        fd = mkstemp(template);
    }
#endif

    return fd;
}

BUILTIN_FUNCTION(os_mktemp)
{
        char template[PATH_MAX + 1] = {0};

        if (argc > 2) {
                zP("os.mktemp() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (argc >= 1 && ARG(0).type != VALUE_NIL) {
                struct value s = ARG(0);
                if (s.type != VALUE_STRING)
                        zP("the first argument to os.mktemp() must be a string");
                /* -8 to make room for the .XXXXXX suffix and NUL byte */
                memcpy(template, s.string, min(s.bytes, sizeof template - 8));
        } else {
                strcpy(template, "tmp");
        }

        strcat(template, ".XXXXXX");

        int fd;

        if (argc == 2)
        {
                struct value flags = ARG(1);
                if (flags.type != VALUE_INTEGER)
                        zP("the second argument to os.mktemp() must be an integer");
                fd = make_temp_file(template, flags.integer);
        }
        else
        {
                fd = make_temp_file(template, -1);
        }

        if (fd == -1) {
                return NIL;
        }

        struct value pair = vT(2);

        NOGC(pair.items);

        pair.items[0] = INTEGER(fd);
        pair.items[1] = vSs(template, strlen(template));

        OKGC(pair.items);

        return pair;
}

BUILTIN_FUNCTION(os_opendir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.opendir()");
#else
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
                zP("the argument to os.opendir() must be a path or a file descriptor");
        }

        if (d == NULL)
                return NIL;

        return PTR(d);
#endif
}

BUILTIN_FUNCTION(os_readdir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.readdir()");
#else
        ASSERT_ARGC("os.readdir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                zP("the argument to os.readdir() must be a pointer");

        struct dirent *entry = readdir(d.ptr);
        if (entry == NULL)
                return NIL;

        Value name = vSs(entry->d_name, strlen(entry->d_name));

        NOGC(name.string);

        Value result = vTn(
                "d_ino", INTEGER(entry->d_ino),
                "d_reclen", INTEGER(entry->d_reclen),
                "d_type", INTEGER(entry->d_type),
                "d_name", name
        );

        OKGC(name.string);

        return result;
#endif
}

BUILTIN_FUNCTION(os_rewinddir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.rewinddir()");
#else
        ASSERT_ARGC("os.rewinddir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                zP("the argument to os.rewinddir() must be a pointer");

        rewinddir(d.ptr);

        return NIL;
#endif
}

BUILTIN_FUNCTION(os_seekdir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.seekdir()");
#else
        ASSERT_ARGC("os.seekdir()", 2);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                zP("the first argument to os.seekdir() must be a pointer");

        struct value off = ARG(1);
        if (off.type != VALUE_INTEGER)
                zP("the second argument to os.seekdir() must be an integer");

        seekdir(d.ptr, off.integer);

        return NIL;
#endif
}

BUILTIN_FUNCTION(os_telldir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.telldir()");
#else
        ASSERT_ARGC("os.telldir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                zP("the argument to os.telldir() must be a pointer");

        return INTEGER(telldir(d.ptr));
#endif
}

BUILTIN_FUNCTION(os_closedir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.closedir()");
#else
        ASSERT_ARGC("os.closedir()", 1);

        struct value d = ARG(0);

        if (d.type != VALUE_PTR)
                zP("the argument to os.closedir() must be a pointer");

        return INTEGER(closedir(d.ptr));
#endif
}

BUILTIN_FUNCTION(os_getcwd)
{
        ASSERT_ARGC("os.getcwd()", 0);

        if (getcwd(buffer, sizeof buffer) == NULL)
                return NIL;

        return vSs(buffer, strlen(buffer));
}

BUILTIN_FUNCTION(os_unlink)
{
        ASSERT_ARGC("os.unlink()", 1);

        struct value path = ARG(0);

        if (path.type != VALUE_STRING)
                zP("the argument to os.unlink() must be a string");

        if (path.bytes >= sizeof buffer) {
                errno = ENOENT;
                return INTEGER(-1);
        }

        memcpy(buffer, path.string, path.bytes);
        buffer[path.bytes] = '\0';

        return INTEGER(unlink(buffer));
}

BUILTIN_FUNCTION(os_link)
{
        ASSERT_ARGC("os.symlink()", 2);

        struct value old = ARG(0);
        struct value new = ARG(1);

        switch (old.type) {
        case VALUE_STRING:
                break;
        case VALUE_BLOB:
                old = STRING_NOGC((char *)old.blob->items, old.blob->count);
                break;
        case VALUE_PTR:
                old = STRING_NOGC(old.ptr, strlen(old.ptr));
                break;
        default:
                zP("os.link(): invalid argument: %s", VSC(&old));
        }

        switch (new.type) {
        case VALUE_STRING:
                break;
        case VALUE_BLOB:
                new = STRING_NOGC((char *)new.blob->items, new.blob->count);
                break;
        case VALUE_PTR:
                new = STRING_NOGC(new.ptr, strlen(new.ptr));
                break;
        default:
                zP("os.link(): invalid argument: %s", VSC(&new));
        }


        if (old.bytes + new.bytes + 2 > sizeof buffer) {
                errno = ENAMETOOLONG;
                return INTEGER(-1);
        }

        memcpy(buffer, old.string, old.bytes);
        buffer[old.bytes] = '\0';

        memcpy(buffer + old.bytes + 1, new.string, new.bytes);
        buffer[old.bytes + 1 + new.bytes] = '\0';

#ifdef _WIN32
        return INTEGER(!CreateHardLinkA(buffer, buffer + old.bytes + 1, NULL));
#else
        return INTEGER(link(buffer, buffer + old.bytes + 1));
#endif
}

BUILTIN_FUNCTION(os_symlink)
{
        ASSERT_ARGC("os.symlink()", 2);

        struct value old = ARG(0);
        struct value new = ARG(1);

        switch (old.type) {
        case VALUE_STRING:
                break;
        case VALUE_BLOB:
                old = STRING_NOGC((char *)old.blob->items, old.blob->count);
                break;
        case VALUE_PTR:
                old = STRING_NOGC(old.ptr, strlen(old.ptr));
                break;
        default:
                zP("os.symlink(): invalid argument: %s", VSC(&old));
        }

        switch (new.type) {
        case VALUE_STRING:
                break;
        case VALUE_BLOB:
                new = STRING_NOGC((char *)new.blob->items, new.blob->count);
                break;
        case VALUE_PTR:
                new = STRING_NOGC(new.ptr, strlen(new.ptr));
                break;
        default:
                zP("os.symlink(): invalid argument: %s", VSC(&new));
        }


        if (old.bytes + new.bytes + 2 > sizeof buffer) {
                errno = ENAMETOOLONG;
                return INTEGER(-1);
        }

        memcpy(buffer, old.string, old.bytes);
        buffer[old.bytes] = '\0';

        memcpy(buffer + old.bytes + 1, new.string, new.bytes);
        buffer[old.bytes + 1 + new.bytes] = '\0';

#ifdef _WIN32
        return INTEGER(!CreateSymbolicLinkA(buffer, buffer + old.bytes + 1, 0));
#else
        return INTEGER(symlink(buffer, buffer + old.bytes + 1));
#endif
}

BUILTIN_FUNCTION(os_rename)
{
        ASSERT_ARGC("os.rename()", 2);

        struct value old = ARG(0);
        struct value new = ARG(1);

        if (old.type != VALUE_STRING) {
                zP("os.rename(): expected string but got: %s", VSC(&old));
        }

        if (new.type != VALUE_STRING) {
                zP("os.rename(): expected string but got: %s", VSC(&new));
        }

        if (old.bytes + new.bytes + 2 > sizeof buffer) {
                errno = ENAMETOOLONG;
                return INTEGER(-1);
        }

        memcpy(buffer, old.string, old.bytes);
        buffer[old.bytes] = '\0';

        memcpy(buffer + old.bytes + 1, new.string, new.bytes);
        buffer[old.bytes + 1 + new.bytes] = '\0';

        return INTEGER(rename(buffer, buffer + old.bytes + 1));
}

BUILTIN_FUNCTION(os_mkdir)
{
        ASSERT_ARGC_2("os.mkdir()", 1, 2);

        struct value path = ARG(0);

        if (path.type != VALUE_STRING) {
                zP("os.mkdir(): expected string as first argument but got: %s", VSC(&ARG(0)));
        }

        mode_t mode = 0777;

        if (argc == 2 && ARG(1).type != VALUE_NIL) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("os.mkdir(): expected integer as second argument but got: %s", VSC(&ARG(1)));
                } else {
                        mode = ARG(1).integer;
                }
        }

        B.count = 0;
        vvPn(B, path.string, path.bytes);
        vvP(B, '\0');

#ifdef _WIN32
        return INTEGER(mkdir(B.items));
#else
        return INTEGER(mkdir(B.items, mode));
#endif
}

BUILTIN_FUNCTION(os_rmdir)
{
        ASSERT_ARGC("os.rmdir()", 1);

        struct value path = ARG(0);

        if (path.type != VALUE_STRING) {
                zP("os.rmdir(): expected string as first argument but got: %s", VSC(&ARG(0)));
        }

        B.count = 0;
        vvPn(B, path.string, path.bytes);
        vvP(B, '\0');

        return INTEGER(rmdir(B.items));
}

BUILTIN_FUNCTION(os_chown)
{
        ASSERT_ARGC("os.chown()", 3);

#ifdef _WIN32
        NOT_ON_WINDOWS("os.chown()");
#else

        size_t n;
        char const *path;

        switch (ARG(0).type) {
        case VALUE_STRING:
                n = ARG(0).bytes;
                path = ARG(0).string;
                break;
        case VALUE_BLOB:
                n = ARG(0).blob->count;
                path = (char const *)ARG(0).blob->items;
                break;
        case VALUE_PTR:
                n = strlen(ARG(0).ptr);
                path = ARG(0).ptr;
                break;
        default:
                zP("os.chown(): expected path but got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("os.chown(): expected integer but got: %s", VSC(&ARG(1)));
        }

        if (ARG(2).type != VALUE_INTEGER) {
                zP("os.chown(): expected integer but got: %s", VSC(&ARG(2)));
        }

        if (n >= sizeof buffer) {
                errno = ENOENT;
                return INTEGER(-1);
        }

        memcpy(buffer, path, n);
        buffer[n] = '\0';

        return INTEGER(chown(buffer, ARG(1).integer, ARG(2).integer));
#endif
}

BUILTIN_FUNCTION(os_chmod)
{
        ASSERT_ARGC("os.chmod()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.chmod()");
#else

        size_t n;
        char const *path;

        switch (ARG(0).type) {
        case VALUE_STRING:
                n = ARG(0).bytes;
                path = ARG(0).string;
                break;
        case VALUE_BLOB:
                n = ARG(0).blob->count;
                path = (char const *)ARG(0).blob->items;
                break;
        case VALUE_PTR:
                n = strlen(ARG(0).ptr);
                path = ARG(0).ptr;
                break;
        default:
                zP("os.chmod(): expected path but got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("os.chmod(): expected integer but got: %s", VSC(&ARG(1)));
        }

        if (n >= sizeof buffer) {
                errno = ENOENT;
                return INTEGER(-1);
        }

        memcpy(buffer, path, n);
        buffer[n] = '\0';

        return INTEGER(chmod(buffer, ARG(1).integer));
#endif
}

BUILTIN_FUNCTION(os_chdir)
{
        ASSERT_ARGC("os.chdir()", 1);

        Value dir = ARG(0);

        if (dir.type == VALUE_STRING) {
                if (dir.bytes >= sizeof buffer) {
                        errno = ENOENT;
                        return INTEGER(-1);
                }

                memcpy(buffer, dir.string, dir.bytes);
                buffer[dir.bytes] = '\0';

                return INTEGER(chdir(buffer));
#ifndef _WIN32
        } else if (dir.type == VALUE_INTEGER) {
                return INTEGER(fchdir(dir.integer));
#endif
        } else {
                zP("os.chdir(): expected path (String) or file descriptor (Int) but got: %s", VSC(&dir));
        }


}

BUILTIN_FUNCTION(os_read)
{
        ASSERT_ARGC_2("os.read()", 2, 3);

        struct value file = ARG(0);

        struct value blob;
        struct value n;

        if (argc == 3) {
                blob = ARG(1);
                n = ARG(2);
        } else {
                blob = BLOB(value_blob_new(ty));
                n = ARG(1);
        }

        if (file.type != VALUE_INTEGER)
                zP("the first argument to os.read() must be an integer");

        if (blob.type != VALUE_BLOB)
                zP("the second argument to os.read() must be a blob");

        if (n.type != VALUE_INTEGER)
                zP("the third argument to os.read() must be an integer");

        if (n.integer < 0)
                zP("the third argument to os.read() must be non-negative");

        NOGC(blob.blob);
        vec_reserve(*blob.blob, blob.blob->count + n.integer);

        Value *all = NAMED("all");
        bool read_all = all != NULL && value_truthy(ty, all);

        ssize_t n_read = 0;
        while (n_read < n.integer) {
                lGv(true);
                ssize_t r = read(
                        file.integer,
                        blob.blob->items + blob.blob->count + n_read,
                        n.integer
                );
                lTk();

                if (r <= 0) {
                        if (n_read == 0) {
                                n_read = r;
                        }
                        break;
                }

                n_read += r;

                if (!read_all) {
                        break;
                }
        }

        OKGC(blob.blob);

        if (n_read > 0)
                blob.blob->count += n_read;

        if (argc == 3)
                return INTEGER(n_read);
        else if (n_read > 0)
                return blob;
        else
                return NIL;
}

BUILTIN_FUNCTION(os_write)
{
        ASSERT_ARGC_2("os.write()", 2, 3);

        struct value file = ARG(0);
        struct value data = ARG(1);

        if (file.type != VALUE_INTEGER)
                zP("the first argument to os.write() must be an integer");

        ssize_t n;
        void const *p;
        unsigned char c;

        switch (data.type) {
        case VALUE_BLOB:
                p = data.blob->items;
                n = data.blob->count;
                break;
        case VALUE_STRING:
                p = data.string;
                n = data.bytes;
                break;
        case VALUE_INTEGER:
                c = data.integer;
                p = &c;
                n = 1;
                break;
        case VALUE_PTR:
                if (argc != 3 || ARG(2).type != VALUE_INTEGER) {
                        zP("os.write(): expected integer as third argument");
                }
                p = data.ptr;
                n = ARG(2).integer;
                break;
        default:
                zP("invalid argument to os.write()");
        }

        struct value *all = NAMED("all");
        bool write_all = all != NULL && value_truthy(ty, all);

        lGv(true);

        size_t off = 0;

        while (n > 0) {
                ssize_t r = write(file.integer, ((unsigned char const *)p) + off, n);
                if (r < 0) {
                        lTk();
                        return INTEGER(r);
                }
                if (r == 0) {
                        break;
                }

                n -= r;
                off += r;

                if (!write_all) {
                        break;
                }
        }

        lTk();

        return INTEGER(off);
}

BUILTIN_FUNCTION(os_fsync)
{
        ASSERT_ARGC("os.fsync()", 1);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER) {
                zP("os.fsync(): expected integer but got: %s", VSC(&fd));
        }

#ifdef _WIN32
        return INTEGER(_commit(fd.integer));
#else
        return INTEGER(fsync(fd.integer));
#endif
}

BUILTIN_FUNCTION(os_sync)
{
        ASSERT_ARGC("os.sync()", 0);

#ifndef _WIN32
        sync();
#endif

        return NIL;
}

#ifdef _WIN32
// Paraphrased from https://github.com/python/cpython/blob/main/Lib/subprocess.py (list2cmdline)
char *
make_cmdline(Array *args)
{
        vec(char) result = {0};

        for (int i = 0; i < args->count; ++i) {
                char const *arg = args->items[i].string;
                int n = args->items[i].bytes;
                int n_bs = 0;
                bool need_quote = memchr(arg, ' ', n) || memchr(arg, '\t', n) || (n == 0);

                if (i > 0)
                        vec_nogc_push(result, ' ');

                if (need_quote)
                        vec_nogc_push(result, '"');

                for (int j = 0; j < n; ++j) switch (arg[j]) {
                case '\\':
                        n_bs += 1;
                        break;
                case '"':
                        n_bs *= 2;
                        while (n_bs --> 0)
                                vec_nogc_push(result, '\\');
                        n_bs = 0;
                        vec_nogc_push(result, '\\');
                        vec_nogc_push(result, '"');
                        break;
                default:
                        while (n_bs --> 0)
                                vec_nogc_push(result, '\\');
                        n_bs = 0;
                        vec_nogc_push(result, arg[j]);

                }

                if (need_quote)
                        n_bs *= 2;

                while (n_bs --> 0)
                        vec_nogc_push(result, '\\');

                if (need_quote)
                        vec_nogc_push(result, '"');
        }

        vec_nogc_push(result, '\0');

        return result.items;
}

BUILTIN_FUNCTION(os_spawn)
{
        ASSERT_ARGC("os.spawn()", 1);

        struct value cmd = ARG(0);
        if (cmd.type != VALUE_ARRAY)
                zP("the argument to os.spawn() must be an array");

        if (cmd.array->count == 0)
                zP("empty array passed to os.spawn()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        zP("non-string in array passed to os.spawn()");

        struct value *detached = NAMED("detach");
        struct value *combine = NAMED("combineOutput");
        struct value *share_stderr = NAMED("shareStderr");
        struct value *share_stdout = NAMED("shareStdout");
        struct value *share_stdin = NAMED("shareStdin");

        if (detached != NULL && !value_truthy(ty, detached)) detached = NULL;
        if (combine != NULL && !value_truthy(ty, combine)) combine = NULL;
        if (share_stderr != NULL && !value_truthy(ty, share_stderr)) share_stderr = NULL;
        if (share_stdout != NULL && !value_truthy(ty, share_stdout)) share_stdout = NULL;
        if (share_stdin != NULL && !value_truthy(ty, share_stdin)) share_stdin = NULL;

        HANDLE hChildStdInRead = NULL;
        HANDLE hChildStdInWrite = NULL;
        HANDLE hChildStdOutRead = NULL;
        HANDLE hChildStdOutWrite = NULL;
        HANDLE hChildStdErrRead = NULL;
        HANDLE hChildStdErrWrite = NULL;

        SECURITY_ATTRIBUTES saAttr;
        saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
        saAttr.bInheritHandle = TRUE;
        saAttr.lpSecurityDescriptor = NULL;

        if (!share_stdin) {
                if (!CreatePipe(&hChildStdInRead, &hChildStdInWrite, &saAttr, 0))
                        return NIL; // Handle error
        }

        if (!share_stdout) {
                if (!CreatePipe(&hChildStdOutRead, &hChildStdOutWrite, &saAttr, 0))
                        return NIL; // Handle error
        }

        if (!share_stderr && !combine) {
                if (!CreatePipe(&hChildStdErrRead, &hChildStdErrWrite, &saAttr, 0))
                        return NIL; // Handle error
        }

        // Prepare the list of handles to be inherited
        HANDLE inheritHandles[3] = {0};
        int inheritHandleCount = 0;
        if (hChildStdInRead) inheritHandles[inheritHandleCount++] = hChildStdInRead;
        if (hChildStdOutWrite) inheritHandles[inheritHandleCount++] = hChildStdOutWrite;
        if (hChildStdErrWrite) inheritHandles[inheritHandleCount++] = hChildStdErrWrite;

        // Set up the process attribute list
        SIZE_T attributeListSize = 0;
        InitializeProcThreadAttributeList(NULL, 1, 0, &attributeListSize);
        LPPROC_THREAD_ATTRIBUTE_LIST lpAttributeList = mrealloc(NULL, attributeListSize);
        InitializeProcThreadAttributeList(lpAttributeList, 1, 0, &attributeListSize);

        // Update the attribute list with the handles to inherit
        if (!UpdateProcThreadAttribute(lpAttributeList,
                                0,
                                PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
                                inheritHandles,
                                inheritHandleCount * sizeof(HANDLE),
                                NULL,
                                NULL)) {
                // Handle error
                free(lpAttributeList);
                printf("It's over\n");
                return NIL;
        }

        STARTUPINFOEX siStartInfo = {0};
        siStartInfo.StartupInfo.cb = sizeof (STARTUPINFOEX);
        siStartInfo.lpAttributeList = lpAttributeList;

        siStartInfo.StartupInfo.hStdError = share_stderr ? GetStdHandle(STD_ERROR_HANDLE) : hChildStdErrWrite;
        siStartInfo.StartupInfo.hStdOutput = share_stdout ? GetStdHandle(STD_OUTPUT_HANDLE) : hChildStdOutWrite;
        siStartInfo.StartupInfo.hStdInput = share_stdin ? GetStdHandle(STD_INPUT_HANDLE) : hChildStdInRead;
        siStartInfo.StartupInfo.dwFlags |= STARTF_USESTDHANDLES;

        PROCESS_INFORMATION piProcInfo;
        ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

        char *cmdline = make_cmdline(cmd.array);

        bool bSuccess = CreateProcessA(
                NULL,
                cmdline,
                NULL,
                NULL,
                TRUE,
                EXTENDED_STARTUPINFO_PRESENT | (detached ? CREATE_NEW_PROCESS_GROUP : 0),
                NULL,
                NULL,
                &siStartInfo.StartupInfo,
                &piProcInfo
        );

        DeleteProcThreadAttributeList(lpAttributeList);
        free(lpAttributeList);
        free(cmdline);

        if (!bSuccess) {
                // Handle error
                DWORD error = GetLastError();
                char* errorMessage = NULL;
                FormatMessage(
                                FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM,
                                NULL,
                                error,
                                0,
                                (LPSTR)&errorMessage,
                                0,
                                NULL
                             );
                printf("CreateProcess failed with error %d: %s\n", error, errorMessage);
                LocalFree(errorMessage);
                return NIL;
        }

        // Close handles to the child process and its primary thread
        CloseHandle(piProcInfo.hThread);

        if (hChildStdInRead != NULL) CloseHandle(hChildStdInRead);
        if (hChildStdOutWrite != NULL) CloseHandle(hChildStdOutWrite);
        if (hChildStdErrWrite != NULL) CloseHandle(hChildStdErrWrite);

        int stdin_fd = -1, stdout_fd = -1, stderr_fd = -1;

        if (!share_stdin) {
                stdin_fd = _open_osfhandle((intptr_t)hChildStdInWrite, _O_WRONLY);
                if (stdin_fd == -1) {
                        // Handle error
                        return NIL;
                }
        }

        if (!share_stdout) {
                stdout_fd = _open_osfhandle((intptr_t)hChildStdOutRead, _O_RDONLY);
                if (stdout_fd == -1) {
                        // Handle error
                        return NIL;
                }
        }

        if (!share_stderr && !combine) {
                stderr_fd = _open_osfhandle((intptr_t)hChildStdErrRead, _O_RDONLY);
                if (stderr_fd == -1) {
                        // Handle error
                        return NIL;
                }
        }

        // Prepare return value
        Value vStdin = share_stdin ? INTEGER(0) : INTEGER(stdin_fd);
        Value vStdout = share_stdout ? INTEGER(1) : INTEGER(stdout_fd);
        Value vStderr = combine ? vStdout : (share_stderr ? INTEGER(2) : INTEGER(stderr_fd));

        return vTn(
                "stdin",    vStdin,
                "stdout",   vStdout,
                "stderr",   vStderr,
                "hStdin",   PTR((void *)_get_osfhandle(vStdin.integer)),
                "hStdout",  PTR((void *)_get_osfhandle(vStdout.integer)),
                "hStderr",  PTR((void *)_get_osfhandle(vStderr.integer)),
                "pid",      INTEGER(piProcInfo.dwProcessId),
                "handle",   PTR((void *)piProcInfo.hProcess)
        );
}
#else
BUILTIN_FUNCTION(os_spawn)
{
        ASSERT_ARGC("os.spawn()", 1);

        struct value cmd = ARG(0);
        if (cmd.type != VALUE_ARRAY)
                zP("os.spawn(): expected array but got: %s", VSC(&cmd));

        if (cmd.array->count == 0)
                zP("os.spawn(): argv empty");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        zP("os.spawn(): non-string present in argv: %s", VSC(&cmd));

        Value      *combine = NAMED("combineOutput");
        Value *share_stderr = NAMED("shareStderr");
        Value *share_stdout = NAMED("shareStdout");
        Value  *share_stdin = NAMED("shareStdin");
        Value       *detach = NAMED("detach");

        if      (combine != NULL && !value_truthy(ty, combine))           combine = NULL;
        if (share_stderr != NULL && !value_truthy(ty, share_stderr)) share_stderr = NULL;
        if (share_stdout != NULL && !value_truthy(ty, share_stdout)) share_stdout = NULL;
        if  (share_stdin != NULL && !value_truthy(ty, share_stdin))   share_stdin = NULL;
        if       (detach != NULL && !value_truthy(ty, detach))             detach = NULL;

        int in[2], out[2], err[2];
        int nToClose = 0;
        int aToClose[6];

/* ========================================================================= */
#define CloseOnError(fd) do { aToClose[nToClose++] = (fd); } while (0)
#define Cleanup()                                  \
        do {                                       \
                TyMutexUnlock(&spawn_lock);        \
                for (int i = 0; i < nToClose; ++i) \
                        close(aToClose[i]);        \
        } while (0)
/* ========================================================================= */

        static TyMutex spawn_lock;
        static atomic_bool init = false;
        bool expected = false;

        if (atomic_compare_exchange_weak(&init, &expected, true)) {
                TyMutexInit(&spawn_lock);
                init = true;
        }

        TyMutexLock(&spawn_lock);

        if (!share_stdin  && pipe(in)  == -1)             { Cleanup(); return NIL; }
        if (!share_stdout && pipe(out) == -1)             { Cleanup(); return NIL; }
        if (!share_stderr && !combine && pipe(err) == -1) { Cleanup(); return NIL; }

        if (!share_stdin)              {  CloseOnError(in[0]);  CloseOnError(in[1]); }
        if (!share_stdout)             { CloseOnError(out[0]); CloseOnError(out[1]); }
        if (!share_stderr && !combine) { CloseOnError(err[0]); CloseOnError(err[1]); }

        posix_spawn_file_actions_t actions;
        posix_spawn_file_actions_init(&actions);

        if (!share_stdin) {
                posix_spawn_file_actions_addclose(&actions, in[1]);
                posix_spawn_file_actions_adddup2(&actions, in[0], STDIN_FILENO);
                posix_spawn_file_actions_addclose(&actions, in[0]);
        }

        if (!share_stdout) {
                posix_spawn_file_actions_addclose(&actions, out[0]);
                posix_spawn_file_actions_adddup2(&actions, out[1], STDOUT_FILENO);
                posix_spawn_file_actions_addclose(&actions, out[1]);
        }

        if (!share_stderr) {
                int errfd = combine ? STDOUT_FILENO : err[1];
                posix_spawn_file_actions_adddup2(&actions, errfd, STDERR_FILENO);
                if (!combine) {
                        posix_spawn_file_actions_addclose(&actions, err[0]);
                        posix_spawn_file_actions_addclose(&actions, err[1]);
                }
        }

        posix_spawnattr_t attr;
        posix_spawnattr_init(&attr);

        if (detach) {
                posix_spawnattr_setpgroup(&attr, 0);
                posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETPGROUP);
        }

        vec(char *) args = {0};

        for (int i = 0; i < cmd.array->count; ++i) {
                char *arg = mrealloc(NULL, cmd.array->items[i].bytes + 1);
                memcpy(arg, cmd.array->items[i].string, cmd.array->items[i].bytes);
                arg[cmd.array->items[i].bytes] = '\0';
                xvP(args, arg);
        }

        xvP(args, NULL);

        pid_t pid;
        int status = posix_spawnp(&pid, args.items[0], &actions, &attr, args.items, environ);

        posix_spawn_file_actions_destroy(&actions);
        posix_spawnattr_destroy(&attr);

        for (int i = 0; args.items[i] != NULL; ++i) {
                free(args.items[i]);
        }

        free(args.items);

        if (status != 0) {
                Cleanup();
                return NIL;
        }

        TyMutexUnlock(&spawn_lock);

        if              (!share_stdin) close(in[0]);
        if             (!share_stdout) close(out[1]);
        if (!share_stderr && !combine) close(err[1]);

        Value  vStdin =  share_stdin ? INTEGER(0) : INTEGER(in[1]);
        Value vStdout = share_stdout ? INTEGER(1) : INTEGER(out[0]);
        Value vStderr =      combine ? vStdout
                                     : share_stderr ? INTEGER(2) : INTEGER(err[0]);

#undef CloseOnError
#undef Cleanup

        return vTn(
                "stdin",   vStdin,
                "stdout",  vStdout,
                "stderr",  vStderr,
                "pid",     INTEGER(pid)
        );
}
#endif

BUILTIN_FUNCTION(thread_join)
{
        if (argc == 0 || ARG(0).type != VALUE_THREAD) {
                zP("non-thread passed to thread.join(): %s", VSC(&ARG(0)));
        }

        if (argc == 1 || ARG(1).type == VALUE_NIL || (ARG(1).type == VALUE_INTEGER && ARG(1).integer == -1)) {
                lGv(true);
                TyThreadJoin(ARG(0).thread->t);
                lTk();
                return ARG(0).thread->v;
        } else if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("thread.join(): invalid timeout argument: %s", VSC(&ARG(1)));
                }

                Thread* t = ARG(0).thread;
                int64_t timeoutMs = ARG(1).integer;

                lGv(true);
                TyMutexLock(&t->mutex);
                while (t->alive) {
                        if (!TyCondVarTimedWaitRelative(&t->cond, &t->mutex, timeoutMs)) {
                                TyMutexUnlock(&t->mutex);
                                lTk();
                                return None;
                        }
                }

                TyMutexUnlock(&t->mutex);
                TyThreadJoin(t->t);
                lTk();

                return Some(ty, t->v);
        } else {
                zP("thread.join(): expected 2 arguments but got %d", argc);
        }
}

BUILTIN_FUNCTION(thread_detach)
{
        if (argc != 1) {
                zP("thread.detach() expects one argument but got %d", argc);
        }

        if (ARG(0).type != VALUE_THREAD) {
                zP("non-thread passed to thread.detach(): %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyThreadDetach(ARG(0).thread->t));
}

BUILTIN_FUNCTION(thread_mutex)
{
        TyMutex *p = mAo(sizeof *p, GC_ANY);
        TyMutexInit(p);
        return GCPTR(p, p);
}

BUILTIN_FUNCTION(thread_cond)
{
        TyCondVar *p = mAo(sizeof *p, GC_ANY);
        TyCondVarInit(p);
        return GCPTR(p, p);
}

BUILTIN_FUNCTION(thread_cond_wait)
{
        ASSERT_ARGC_2("thread.waitCond()", 2, 3);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.waitCond() expects a pointer as its first argument but got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_PTR) {
                zP("thread.waitCond() expects a pointer as its second argument but got: %s", VSC(&ARG(1)));
        }

        int r;

        lGv(true);

        int64_t usec = -1;
        if (argc == 3) {
                if (ARG(2).type != VALUE_INTEGER) {
                        zP("thread.waitCond() expects an integer as its third argument but got: %s", VSC(&ARG(2)));
                }
                usec = ARG(2).integer;
        }

        if (usec < 0) {
                r = TyCondVarWait(ARG(0).ptr, ARG(1).ptr);
        } else {
                r = TyCondVarTimedWaitRelative(ARG(0).ptr, ARG(1).ptr, usec / 1000);
        }

        lTk();

        return INTEGER(r);
}

BUILTIN_FUNCTION(thread_cond_signal)
{
        ASSERT_ARGC("thread.signalCond()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.signalCond() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyCondVarSignal(ARG(0).ptr));
}

BUILTIN_FUNCTION(thread_cond_broadcast)
{
        ASSERT_ARGC("thread.broadcastCond()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.broadcastCond() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyCondVarBroadcast(ARG(0).ptr));
}

BUILTIN_FUNCTION(thread_cond_destroy)
{
        ASSERT_ARGC("thread.destroyCond()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.destroyCond() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyCondVarDestroy(ARG(0).ptr));
}

BUILTIN_FUNCTION(thread_mutex_destroy)
{
        ASSERT_ARGC("thread.destroyMutex()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.destroyMutex() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyMutexDestroy(ARG(0).ptr));
}

BUILTIN_FUNCTION(thread_lock)
{
        ASSERT_ARGC("thread.lock()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.lock() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        lGv(true);
        int r = TyMutexLock(ARG(0).ptr);
        lTk();

        return INTEGER(r);
}

BUILTIN_FUNCTION(thread_trylock)
{
        ASSERT_ARGC("thread.tryLock()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.tryLock() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyMutexTryLock(ARG(0).ptr));
}

BUILTIN_FUNCTION(thread_unlock)
{
        ASSERT_ARGC("thread.unlock()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.unlock() expects a pointer but got: %s", VSC(&ARG(0)));
        }

        return BOOLEAN(TyMutexUnlock(ARG(0).ptr));
}

BUILTIN_FUNCTION(thread_create)
{
        if (argc == 0) {
                zP("thread.create() expects at least one argument");
        }

        if (!CALLABLE(ARG(0))) {
                zP("non-callable value passed to thread.create(): %s", VSC(&ARG(0)));
        }

        Value *ctx = mA((argc + 1) * sizeof (Value));
        Thread *t = mAo(sizeof *t, GC_THREAD);

        NOGC(t);
        t->i = tid++;
        t->v = NONE;

        for (int i = 0; i < argc; ++i) {
                ctx[i] = ARG(i);
        }

        ctx[argc] = NONE;

        Value *isolated = NAMED("isolated");

        NewThread(ty, t, ctx, NAMED("name"), isolated != NULL && value_truthy(ty, isolated));

        return THREAD(t);
}


BUILTIN_FUNCTION(thread_channel)
{
        ASSERT_ARGC("thread.channel()", 0);

        Channel *c = mAo(sizeof *c, GC_ANY);

        c->open = true;
        vec_init(c->q);
        TyCondVarInit(&c->c);
        TyMutexInit(&c->m);

        return GCPTR(c, c);
}

BUILTIN_FUNCTION(thread_send)
{
        ASSERT_ARGC("thread.send()", 2);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.send(): expected pointer to channel but got: %s", VSC(&ARG(0)));
        }

        Channel *chan = ARG(0).ptr;
        ChanVal cv = { .v = ARG(1) };

        Forget(ty, &cv.v, (AllocList *)&cv.as);

        lGv(true);
        TyMutexLock(&chan->m);
        lTk();
        vvP(chan->q, cv);
        TyMutexUnlock(&chan->m);
        TyCondVarSignal(&chan->c);

        return NIL;
}



BUILTIN_FUNCTION(thread_recv)
{
        ASSERT_ARGC_2("thread.recv()", 1, 2);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.recv(): expected pointer to channel but got: %s", VSC(&ARG(0)));
        }

        Channel *chan = ARG(0).ptr;

        lGv(true);
        TyMutexLock(&chan->m);

        if (argc == 1) {
                while (chan->open && chan->q.count == 0) {
                        TyCondVarWait(&chan->c, &chan->m);
                }
        } else {
                struct value t = ARG(1);
                if (t.type != VALUE_INTEGER) {
                        zP("thread.recv(): expected integer but got: %s", VSC(&t));
                }
                while (chan->open && chan->q.count == 0) {
                        if (!TyCondVarTimedWaitRelative(&chan->c, &chan->m, t.integer)) {
                                break;
                        }
                }
        }

        lTk();

        if (chan->q.count == 0) {
                TyMutexUnlock(&chan->m);
                return None;
        }

        ChanVal v = chan->q.items[0];

        vvXi(chan->q, 0);

        TyMutexUnlock(&chan->m);

        GCTakeOwnership(ty, (AllocList *)&v.as);

        return Some(ty, v.v);
}

BUILTIN_FUNCTION(thread_close)
{
        ASSERT_ARGC("thread.close()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("thread.close(): expected pointer to channel but got: %s", VSC(&ARG(0)));
        }

        Channel *chan = ARG(0).ptr;

        lGv(true);
        TyMutexLock(&chan->m);
        lTk();
        chan->open = false;
        TyMutexUnlock(&chan->m);

        return NIL;
}

BUILTIN_FUNCTION(thread_kill)
{
        ASSERT_ARGC("thread.kill()", 2);

        struct value t = ARG(0);

        if (t.type != VALUE_THREAD) {
                zP("thread.kill() expects a thread as the first argument but got: %s", VSC(&t));
        }

        struct value sig = ARG(1);

        if (sig.type != VALUE_INTEGER) {
                zP("thread.kill(): expected integer as second argument but got: %s", VSC(&sig));
        }

        return BOOLEAN(TyThreadKill(t.thread->t, sig.integer));
}

BUILTIN_FUNCTION(thread_setname)
{
        ASSERT_ARGC("thread.setName()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("thread.setName()");
#else
        struct value name = ARG(0);
        char const *pname;
        int n;

        switch (name.type) {
        case VALUE_STRING:
                n = min(sizeof buffer - 1, name.bytes);
                memcpy(buffer, name.string, n);
                buffer[n] = '\0';
                pname = buffer;
                break;
        case VALUE_BLOB:
                n = min(sizeof buffer - 1, name.blob->count);
                memcpy(buffer, name.blob->items, n);
                buffer[n] = '\0';
                pname = buffer;
                break;
        case VALUE_PTR:
                pname = name.ptr;
                break;
        default:
                zP("thread.setName(): expected string but got: %s", VSC(&name));
        }

#ifdef __APPLE__
        pthread_setname_np(pname);
#elif __linux__
        pthread_setname_np(pthread_self(), pname);
#endif
        return NIL;
#endif
}

BUILTIN_FUNCTION(thread_getname)
{
        ASSERT_ARGC("thread.getName()", 0);

#ifdef _WIN32
        NOT_ON_WINDOWS("thread.getName()");
#else
        int r = pthread_getname_np(pthread_self(), buffer, sizeof buffer);
        if (r != 0) {
                return NIL;
        }

        return vSs(buffer, strlen(buffer));
#endif
}

BUILTIN_FUNCTION(thread_id)
{
        ASSERT_ARGC_2("thread.id()", 0, 1);

        if (argc == 0 || ARG(0).type == VALUE_NIL) {
                return INTEGER(MyThreadId(ty));
        } else if (ARG(0).type == VALUE_PTR) {
                return INTEGER(((Thread *)ARG(0).ptr)->i);
        } else {
                zP("thread.id(): expected thread pointer but got: %s", VSC(&ARG(0)));
        }
}

BUILTIN_FUNCTION(thread_self)
{
        ASSERT_ARGC("thread.self()", 0);
        return PTR((void *)TyThreadSelf());
}

BUILTIN_FUNCTION(os_fork)
{
        ASSERT_ARGC("os.fork()", 0);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.fork()");
#else
        return INTEGER(fork());
#endif
}

BUILTIN_FUNCTION(os_pipe)
{
        ASSERT_ARGC("os.pipe()", 0);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.pipe()");
#else

        int p[2];

        if (pipe(p) == -1)
                return NIL;

        struct value fds = vT(2);

        fds.items[0] = INTEGER(p[0]);
        fds.items[1] = INTEGER(p[1]);

        return fds;
#endif
}

BUILTIN_FUNCTION(os_dup)
{
        ASSERT_ARGC("os.dup()", 1);

        struct value old = ARG(0);

        if (old.type != VALUE_INTEGER)
                zP("os.dup(): argument must be an integer");

        return INTEGER(dup(old.integer));
}

BUILTIN_FUNCTION(os_dup2)
{
        ASSERT_ARGC("os.dup2()", 2);

        struct value old = ARG(0);
        struct value new = ARG(1);

        if (old.type != VALUE_INTEGER || new.type != VALUE_INTEGER)
                zP("the arguments to os.dup2() must be integers");

        return INTEGER(dup2(old.integer, new.integer));
}

BUILTIN_FUNCTION(os_socket)
{
        ASSERT_ARGC("os.socket()", 3);

        struct value domain = ARG(0);
        struct value type = ARG(1);
        struct value protocol = ARG(2);

        if (domain.type != VALUE_INTEGER || type.type != VALUE_INTEGER || protocol.type != VALUE_INTEGER)
                zP("the arguments to os.socket() must be integers");

        return INTEGER(socket(domain.integer, type.integer, protocol.integer));
}

BUILTIN_FUNCTION(os_setsockopt)
{
        ASSERT_ARGC_2("os.setsockopt()", 3, 4);

        struct value sock = ARG(0);
        if (sock.type != VALUE_INTEGER)
                zP("the first argument to os.setsockopt() must be an integer (socket fd)");

        struct value level = ARG(1);
        if (level.type != VALUE_INTEGER)
                zP("the second argument to os.setsockopt() must be an integer (level)");

        struct value option = ARG(2);
        if (level.type != VALUE_INTEGER)
                zP("the third argument to os.setsockopt() must be an integer (option)");

        int o;

        if (argc == 4) {
                struct value v = ARG(3);
                if (v.type != VALUE_INTEGER)
                        zP("the fourth argument to os.setsockopt() must be an integer (opt value)");
                o = v.integer;
        } else {
                o = 1;
        }

        return INTEGER(setsockopt(sock.integer, level.integer, option.integer, &o, sizeof o));
}

BUILTIN_FUNCTION(os_getsockopt)
{
        ASSERT_ARGC("os.getsockopt()", 3);

        struct value sock = ARG(0);
        if (sock.type != VALUE_INTEGER)
                zP("the first argument to os.getsockopt() must be an integer (socket fd)");

        struct value level = ARG(1);
        if (level.type != VALUE_INTEGER)
                zP("the second argument to os.getsockopt() must be an integer (level)");

        struct value option = ARG(2);
        if (level.type != VALUE_INTEGER)
                zP("the third argument to os.getsockopt() must be an integer (option)");

        int o;
        socklen_t n = sizeof o;

        if (getsockopt(sock.integer, level.integer, option.integer, &o, &n) == 0) {
                return INTEGER(o);
        } else {
                return NIL;
        }
}

BUILTIN_FUNCTION(os_getnameinfo)
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
                zP("os.getnameinfo(): invalid address argument: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("os.getnameinfo(): invalid flags argument: %s", VSC(&ARG(1)));
        }

        char host[128];
        char serv[32];

        int r = getnameinfo(addr, alen, host, sizeof host, serv, sizeof serv, ARG(1).integer);

        if (r == 0) {
                struct value v = vT(2);
                v.items[0] = vSs(host, strlen(host));
                v.items[1] = vSs(serv, strlen(serv));
                return v;
        }

        return INTEGER(r);
}

BUILTIN_FUNCTION(os_getpeername)
{
        ASSERT_ARGC("os.getpeername()", 1);

        if (ARG(0).type != VALUE_INTEGER) {
                zP("os.getpeername(): expected integer but got: %s", VSC(&ARG(0)));
        }

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        lGv(true);
        int r = getpeername(ARG(0).integer, (void *)&addr, &addr_size);
        lTk();

        if (r < 0) {
                return NIL;
        }

        struct blob *b = value_blob_new(ty);
        vec_push_n_unchecked(*b, &addr, min(addr_size, sizeof addr));

        return BLOB(b);
}

BUILTIN_FUNCTION(os_getsockname)
{
        ASSERT_ARGC("os.getsockname()", 1);

        if (ARG(0).type != VALUE_INTEGER) {
                zP("os.getsockname(): expected integer but got: %s", VSC(&ARG(0)));
        }

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        lGv(true);
        int r = getsockname(ARG(0).integer, (void *)&addr, &addr_size);
        lTk();

        if (r < 0) {
                return NIL;
        }

        struct blob *b = value_blob_new(ty);
        vec_push_n_unchecked(*b, &addr, min(addr_size, sizeof addr));

        return BLOB(b);
}

BUILTIN_FUNCTION(os_shutdown)
{
        ASSERT_ARGC("os.shutdown()", 2);

        struct value fd = ARG(0);
        struct value how = ARG(1);

        if (fd.type != VALUE_INTEGER || how.type != VALUE_INTEGER)
                zP("the arguments to os.shutdown() must be integers");

        return INTEGER(shutdown(fd.integer, how.integer));
}

BUILTIN_FUNCTION(os_listen)
{
        ASSERT_ARGC("os.listen()", 2);

        struct value sockfd = ARG(0);
        struct value backlog = ARG(1);

        if (sockfd.type != VALUE_INTEGER || backlog.type != VALUE_INTEGER)
                zP("the arguments to os.listen() must be integers");

        return INTEGER(listen(sockfd.integer, backlog.integer));
}

BUILTIN_FUNCTION(os_connect)
{
        ASSERT_ARGC("os.connect()", 2);

        struct value sockfd = ARG(0);
        struct value addr = ARG(1);

        if (sockfd.type != VALUE_INTEGER)
                zP("the first argument to os.connect() must be an integer");

        if (addr.type != VALUE_TUPLE)
                zP("the second argument to os.connect() must be a tuple");

        struct value *v = tuple_get(&addr, "family");
        if (v == NULL || v->type != VALUE_INTEGER)
                zP("missing or invalid address family in dict passed to os.connect()");

#ifndef _WIN32
        struct sockaddr_un un_addr;
#endif
        struct sockaddr_in in_addr;
        struct in_addr ia;

        struct value *sockaddr = tuple_get(&addr, "address");
        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                return INTEGER(connect(sockfd.integer, (struct sockaddr *)sockaddr->blob->items, sockaddr->blob->count));
        } else switch (v->integer) {
#ifndef _WIN32
                case AF_UNIX:
                        memset(&un_addr, 0, sizeof un_addr);
                        un_addr.sun_family = AF_UNIX;
                        v = tuple_get(&addr, "path");
                        if (v == NULL || v->type != VALUE_STRING)
                                zP("missing or invalid path in dict passed to os.connect()");
                        memcpy(un_addr.sun_path, v->string, min(v->bytes, sizeof un_addr.sun_path));
                        return INTEGER(connect(sockfd.integer, (struct sockaddr *)&un_addr, sizeof un_addr));
#endif
                case AF_INET:
                        memset(&in_addr, 0, sizeof in_addr);
                        in_addr.sin_family = AF_INET;
                        v = tuple_get(&addr, "address");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                zP("missing or invalid address in dict passed to os.connect()");
                        ia.s_addr = htonl(v->integer);
                        in_addr.sin_addr = ia;
                        v = tuple_get(&addr, "port");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                zP("missing or invalid port in dict passed to os.connect()");
                        unsigned short p = htons(v->integer);
                        memcpy(&in_addr.sin_port, &p, sizeof in_addr.sin_port);
                        return INTEGER(connect(sockfd.integer, (struct sockaddr *)&in_addr, sizeof in_addr));
                default:
                        zP("invalid arguments to os.connect()");
        }
}

BUILTIN_FUNCTION(os_bind)
{
        ASSERT_ARGC("os.bind()", 2);

        struct value sockfd = ARG(0);
        struct value addr = ARG(1);

        if (sockfd.type != VALUE_INTEGER)
                zP("the first argument to os.bind() must be an integer");

        if (addr.type != VALUE_TUPLE)
                zP("the second argument to os.bind() must be a named tuple");

        struct value *v = tuple_get(&addr, "family");
        if (v == NULL || v->type != VALUE_INTEGER)
                zP("missing or invalid address family in address passed to os.bind()");

#ifndef _WIN32
        struct sockaddr_un un_addr;
#endif
        struct sockaddr_in in_addr;
        struct in_addr ia;

        struct value *sockaddr = tuple_get(&addr, "address");
        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                return INTEGER(bind(sockfd.integer, (struct sockaddr *)sockaddr->blob->items, sockaddr->blob->count));
        } else switch (v->integer) {
#ifndef _WIN32
                case AF_UNIX:
                        memset(&un_addr, 0, sizeof un_addr);
                        un_addr.sun_family = AF_UNIX;
                        v = tuple_get(&addr, "path");
                        if (v == NULL || v->type != VALUE_STRING)
                                zP("missing or invalid path in tuple passed to os.bind()");
                        memcpy(un_addr.sun_path, v->string, min(v->bytes, sizeof un_addr.sun_path));
                        return INTEGER(bind(sockfd.integer, (struct sockaddr *)&un_addr, sizeof un_addr));
#endif
                case AF_INET:
                        memset(&in_addr, 0, sizeof in_addr);
                        in_addr.sin_family = AF_INET;
                        v = tuple_get(&addr, "address");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                zP("missing or invalid address in tuple passed to os.bind()");
                        ia.s_addr = htonl(v->integer);
                        in_addr.sin_addr = ia;
                        v = tuple_get(&addr, "port");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                zP("missing or invalid port in tuple passed to os.bind()");
                        unsigned short p = htons(v->integer);
                        memcpy(&in_addr.sin_port, &p, sizeof in_addr.sin_port);
                        return INTEGER(bind(sockfd.integer, (struct sockaddr *)&in_addr, sizeof in_addr));
                default:
                        zP("invalid arguments to os.bind()");
        }
}

BUILTIN_FUNCTION(os_getaddrinfo)
{
        ASSERT_ARGC_2("os.getaddrinfo()", 5, 6);

        struct value host = ARG(0);
        if (host.type != VALUE_STRING && host.type != VALUE_NIL)
                zP("the first argument to os.getaddrinfo() (node) must be a string or nil");

        struct value port = ARG(1);
        if (port.type != VALUE_STRING && port.type != VALUE_INTEGER && port.type != VALUE_NIL)
                zP("the second argument to os.getaddrinfo() (service) must be a string, an integer, or nil");

        if (host.type == VALUE_NIL && port.type == VALUE_NIL) {
                zP("os.getaddrinfo(): the first and second arguments (node and service) cannot both be nil");
        }

        struct value family = ARG(2);
        if (family.type != VALUE_INTEGER)
                zP("the third argument to os.getaddrinfo() (family) must be an integer");

        struct value type = ARG(3);
        if (type.type != VALUE_INTEGER)
                zP("the fourth argument to os.getaddrinfo() (type) must be an integer");

        struct value protocol = ARG(4);
        if (protocol.type != VALUE_INTEGER)
                zP("the fifth argument to os.getaddrinfo() (protocol) must be an integer");

        // Default to the flags used when hints == NULL in glibc getaddrinfo()
        int flags = AI_V4MAPPED | AI_ADDRCONFIG;
        if (argc == 6 && ARG(5).type != VALUE_NIL) {
                if (ARG(5).type != VALUE_INTEGER)
                        zP("the sixth argument to os.getaddrinfo() (flags) must be an integer");
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
                vvPn(B, host.string, host.bytes);
                vvP(B, '\0');

                vvPn(B, port.string, port.bytes);
                vvP(B, '\0');

                node = B.items;
                service = B.items + host.bytes + 1;
        } else if (port.type == VALUE_NIL) {
                vvPn(B, host.string, host.bytes);
                vvP(B, '\0');

                node = B.items;
                service = NULL;
        } else {
                vvPn(B, port.string, port.bytes);
                vvP(B, '\0');

                node = NULL;
                service = B.items;
        }

        struct value results = ARRAY(vA());
        gP(&results);

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
                        struct blob *b = value_blob_new(ty);

                        NOGC(b);

                        Value entry = vTn(
                                "family",    INTEGER(it->ai_family),
                                "type",      INTEGER(it->ai_socktype),
                                "protocol",  INTEGER(it->ai_protocol),
                                "address",   BLOB(b),
                                "canonname", NIL
                        );

                        NOGC(entry.items);
                        NOGC(entry.ids);

                        vAp(results.array, entry);

                        OKGC(entry.items);
                        OKGC(entry.ids);
                        OKGC(b);

                        vvPn(*b, (char *)it->ai_addr, it->ai_addrlen);

                        if (it->ai_canonname != NULL) {
                                entry.items[4] = vSs(it->ai_canonname, strlen(it->ai_canonname));
                        }
                }

                gX();

                freeaddrinfo(res);

                return Ok(ty, results);

        } else {
                return Err(ty, INTEGER(r));
        }
}

BUILTIN_FUNCTION(os_gai_strerror)
{
        ASSERT_ARGC("os.gai_strerror()", 1);

        if (ARG(0).type != VALUE_INTEGER) {
                zP("os.gai_strerror(): expected integer but got: %s", VSC(&ARG(0)));
        }

        char const *msg = gai_strerror(ARG(0).integer);

        return STRING_NOGC(msg, strlen(msg));
}

BUILTIN_FUNCTION(os_accept)
{
        ASSERT_ARGC("os.accept()", 1);

        struct value sockfd = ARG(0);

        if (sockfd.type != VALUE_INTEGER)
                zP("the argument to os.accept() must be an integer");

        struct sockaddr a;
        socklen_t n = sizeof a;

        lGv(true);
        int r = accept(sockfd.integer, &a, &n);
        lTk();
        if (r == -1)
                return NIL;

        struct blob *b = value_blob_new(ty);
        NOGC(b);

        vvPn(*b, (char *)&a, n);

        struct value v = vTn(
                "fd",   INTEGER(r),
                "addr", BLOB(b)
        );

        OKGC(b);

        return v;
}

BUILTIN_FUNCTION(os_recvfrom)
{
        ASSERT_ARGC_2("os.recvfrom()", 3, 4);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("the first argument to os.recvfrom() must be an integer");

        struct value buffer;
        struct value size;
        struct value flags;

        if (argc == 3) {
                buffer = BLOB(value_blob_new(ty));
                size = ARG(1);
                flags = ARG(2);
        } else {
                buffer = ARG(1);
                size = ARG(2);
                flags = ARG(3);
        }

        if (buffer.type != VALUE_BLOB)
                zP("the buffer argument to os.recvfrom() must be a blob");

        if (size.type != VALUE_INTEGER || size.integer < 0)
                zP("the size argument to os.recvfrom() must be a non-negative integer");

        if (flags.type != VALUE_INTEGER)
                zP("the flags argument to os.recvfrom() must be an integer");

        NOGC(buffer.blob);

        vec_reserve(*buffer.blob, size.integer);

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        lGv(true);
        ssize_t r = recvfrom(fd.integer, buffer.blob->items, size.integer, flags.integer, (void *)&addr, &addr_size);
        lTk();
        if (r < 0) {
                OKGC(buffer.blob);
                return NIL;
        }

        buffer.blob->count = r;

        struct blob *b = value_blob_new(ty);
        NOGC(b);
        vvPn(*b, &addr, min(addr_size, sizeof addr));

        struct value result = vT(2);

        result.items[0] = buffer;
        result.items[1] = BLOB(b);

        OKGC(b);
        OKGC(buffer.blob);

        return result;
}

BUILTIN_FUNCTION(os_sendto)
{
        ASSERT_ARGC_2("os.sendto()", 3, 4);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("the first argument to os.sendto() must be an integer (fd)");

        struct value buffer = ARG(1);
        if (buffer.type != VALUE_BLOB && buffer.type != VALUE_STRING) {
                zP(
                        "os.sendto(): expected Blob or String as second argument but got: %s%s%s%s",
                        TERM(1),
                        TERM(93),
                        VSC(&buffer),
                        TERM(0)
                );
        }

        struct value flags = ARG(2);
        if (flags.type != VALUE_INTEGER)
                zP("the third argument to os.sendto() must be an integer (flags)");

        struct value addr = ARG(3);
        if (addr.type != VALUE_BLOB)
                zP("the fourth argument to os.sendto() must be a blob (sockaddr)");

        lGv(true);
        ssize_t r = (buffer.type == VALUE_BLOB)
                  ? sendto(fd.integer, buffer.blob->items, buffer.blob->count, flags.integer, (void *)addr.blob->items, addr.blob->count)
                  : sendto(fd.integer, buffer.string, buffer.bytes, flags.integer, (void *)addr.blob->items, addr.blob->count);
        lTk();

        return INTEGER(r);
}

BUILTIN_FUNCTION(os_poll)
{
        ASSERT_ARGC("os.poll()", 2);

        struct value fds = ARG(0);
        struct value timeout = ARG(1);

        if (fds.type != VALUE_ARRAY)
                zP("the first argument to os.poll() must be an array");

        if (timeout.type != VALUE_INTEGER)
                zP("the second argument to os.poll() must be an integer");

        static _Thread_local vec(struct pollfd) pfds;
        pfds.count = 0;

        vec_reserve(pfds, fds.array->count);

        struct value *v;
        for (int i = 0; i < fds.array->count; ++i) {
                if (fds.array->items[i].type != VALUE_TUPLE)
                        zP("non-tuple in fds array passed to os.poll()");
                v = tuple_get(&fds.array->items[i], "fd");
                if (v == NULL || v->type != VALUE_INTEGER)
                        zP("all tuples in the fds array passed to os.poll() must have an integer value under the key 'fd'");
                pfds.items[i].fd = v->integer;
                v = tuple_get(&fds.array->items[i], "events");
                if (v != NULL && v->type == VALUE_INTEGER)
                        pfds.items[i].events = v->integer;
                else
                        pfds.items[i].events = POLLIN;
        }

        pfds.count = fds.array->count;

        lGv(true);
#ifdef _WIN32
        int ret = WSAPoll(pfds.items, pfds.count, timeout.integer);
#else
        int ret = poll(pfds.items, pfds.count, timeout.integer);
#endif
        lTk();

        if (ret < 0)
                return INTEGER(ret);

        for (int i = 0; i < fds.array->count; ++i) {
                fds.array->items[i] = vTn(
                        "fd",      *tuple_get(&fds.array->items[i], "fd"),
                        "events",  *tuple_get(&fds.array->items[i], "events"),
                        "revents", INTEGER(pfds.items[i].revents)
                );
        }

        return INTEGER(ret);
}

#ifdef __linux__
BUILTIN_FUNCTION(os_epoll_create)
{
        ASSERT_ARGC("os.epoll_create()", 1);

        struct value flags = ARG(0);
        if (flags.type != VALUE_INTEGER)
                zP("the argument to os.epoll_create() must be an integer");

        return INTEGER(epoll_create1(flags.integer));
}

BUILTIN_FUNCTION(os_epoll_ctl)
{
        ASSERT_ARGC("os.epoll_ctl()", 4);

        struct value efd = ARG(0);
        if (efd.type != VALUE_INTEGER)
                zP("the first argument to os.epoll_ctl() must be an integer");

        struct value op = ARG(1);
        if (op.type != VALUE_INTEGER)
                zP("the second argument to os.epoll_ctl() must be an integer");

        struct value fd = ARG(2);
        if (fd.type != VALUE_INTEGER)
                zP("the third argument to os.epoll_ctl() must be an integer");

        struct value events = ARG(3);
        if (events.type != VALUE_INTEGER)
                zP("the fourth argument to os.epoll_ctl() must be an integer");

        struct epoll_event ev = {
                .events = events.integer,
                .data = { .fd = fd.integer }
        };

        return INTEGER(epoll_ctl(efd.integer, op.integer, fd.integer, &ev));
}

BUILTIN_FUNCTION(os_epoll_wait)
{
        ASSERT_ARGC("os.epoll_wait()", 2);

        struct value efd = ARG(0);
        if (efd.type != VALUE_INTEGER)
                zP("the first argument to os.epoll_wait() must be an integer (epoll fd)");

        struct value timeout = ARG(1);
        if (timeout.type != VALUE_INTEGER)
                zP("the second argument to os.epoll_wait() must be an integer (timeout in ms)");

        struct epoll_event events[32];

        lGv(true);
        int n = epoll_wait(efd.integer, events, sizeof events / sizeof events[0], timeout.integer);
        lTk();

        if (n == -1)
                return NIL;

        struct array *result = vA();

        gP(&ARRAY(result));

        for (int i = 0; i < n; ++i) {
                struct value ev = vT(2);
                NOGC(ev.items);
                ev.items[0] = INTEGER(events[i].data.fd);
                ev.items[1] = INTEGER(events[i].events);
                vAp(result, ev);
                OKGC(ev.items);
        }

        gX();

        return ARRAY(result);
}
#endif

BUILTIN_FUNCTION(os_waitpid)
{
        ASSERT_ARGC_2("os.waitpid()", 1, 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.waitpid()");
#else

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
                zP("both arguments to os.waitpid() must be integers");
        }

        int status;
        int ret = waitpid(pid.integer, &status, flags);

        if (ret <= 0)
                return INTEGER(ret);

        return PAIR(INTEGER(ret), INTEGER(status));
#endif
}

#ifdef _WIN32
#define WAITMACRO(name) \
        struct value \
        builtin_os_ ## name(Ty *ty, int argc, struct value *kwargs) \
        { \
                NOT_ON_WINDOWS("os." #name); \
        }
#else
#define WAITMACRO(name) \
        struct value \
        builtin_os_ ## name(Ty *ty, int argc, struct value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 1); \
        \
                struct value status = ARG(0); \
                if (status.type != VALUE_INTEGER) \
                        zP("the argument to os." #name "() must be an integer"); \
        \
                int s = status.integer; \
        \
                return INTEGER(name(s)); \
        }
#endif

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

#ifdef _WIN32
#define GETID(name) \
        struct value \
        builtin_os_ ## name (Ty *ty, int argc, struct value *kwargs) \
        { \
                NOT_ON_WINDOWS("os." #name); \
        }
#define SETID(name) \
        struct value \
        builtin_os_ ## name (Ty *ty, int argc, struct value *kwargs) \
        { \
                NOT_ON_WINDOWS("os." #name); \
        }
#else
#define GETID(name) \
        struct value \
        builtin_os_ ## name (Ty *ty, int argc, struct value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 0); \
                return INTEGER(name()); \
        }

#define SETID(name) \
        struct value \
        builtin_os_ ## name (Ty *ty, int argc, struct value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 1); \
                struct value id = ARG(0); \
                if (id.type != VALUE_INTEGER) \
                        zP("the argument to os." #name "() must be an integer"); \
                return INTEGER(name(id.integer)); \
        }
#endif

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

noreturn BUILTIN_FUNCTION(os_exit)
{
        ASSERT_ARGC("os.exit()", 1);

        struct value status = ARG(0);
        if (status.type != VALUE_INTEGER)
                zP("the argument to os.exit() must be an integer");

        exit(status.integer);
}

BUILTIN_FUNCTION(os_exec)
{
        ASSERT_ARGC("os.exec()", 1);

        struct value cmd = ARG(0);
        if (cmd.type != VALUE_ARRAY)
                zP("the argument to os.exec() must be an array");

        if (cmd.array->count == 0)
                zP("empty array passed to os.exec()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        zP("non-string in array passed to os.exec()");

        vec(char *) argv;
        vec_init(argv);

        for (int i = 0; i < cmd.array->count; ++i) {
                char *arg = mA(cmd.array->items[i].bytes + 1);
                memcpy(arg, cmd.array->items[i].string, cmd.array->items[i].bytes);
                arg[cmd.array->items[i].bytes] = '\0';
                vvP(argv, arg);
        }

        vvP(argv, NULL);

        return INTEGER(execvp(argv.items[0], argv.items));
}

BUILTIN_FUNCTION(os_signal)
{
        ASSERT_ARGC_2("os.signal()", 1, 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.signal()");
#else

        struct value num = ARG(0);

        if (num.type != VALUE_INTEGER)
                zP("the first argument to os.signal() must be an integer");

        if (argc == 2) {
                struct value f = ARG(1);

                struct sigaction act = {0};

                if (f.type == VALUE_NIL) {
                        vm_del_sigfn(ty, num.integer);
                        act.sa_handler = SIG_DFL;
                } else if (CALLABLE(f)) {
                        act.sa_flags = SA_SIGINFO;
                        act.sa_sigaction = vm_do_signal;
                } else {
                        zP("the second argument to os.signal() must be callable");
                }

                int r = sigaction(num.integer, &act, NULL);
                if (r == 0)
                        vm_set_sigfn(ty, num.integer, &f);

                return INTEGER(r);
        } else {
                return vm_get_sigfn(ty, num.integer);
        }

#endif
}

BUILTIN_FUNCTION(os_kill)
{
        ASSERT_ARGC("os.kill()", 2);

        struct value pid = ARG(0);
        struct value sig = ARG(1);

        if (pid.type != VALUE_INTEGER || sig.type != VALUE_INTEGER)
                zP("both arguments to os.kill() must be integers");


#ifdef _WIN32
        HANDLE hProc = OpenProcess(PROCESS_ALL_ACCESS, FALSE, pid.integer);
        bool bSuccess = TerminateProcess(hProc, 0);
        int error = GetLastError();
        CloseHandle(hProc);
        return INTEGER(bSuccess ? 0 : error);
#else
        return INTEGER(kill(pid.integer, sig.integer));
#endif
}

static struct value
timespec_tuple(Ty *ty, struct timespec const *ts)
{
        return vTn(
                "tv_sec",  INTEGER(ts->tv_sec),
                "tv_nsec", INTEGER(ts->tv_nsec)
        );
}

static struct timespec
tuple_timespec(Ty *ty, char const *func, struct value const *v)
{
        struct value *sec = tuple_get(v, "tv_sec");

        if (sec == NULL || sec->type != VALUE_INTEGER) {
                zP(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        VSC(v),
                        TERM(0),
                        TERM(92),
                        "tv_sec",
                        TERM(0)
                );
        }

        struct value *nsec = tuple_get(v, "tv_nsec");

        if (nsec == NULL || nsec->type != VALUE_INTEGER) {
                zP(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        VSC(v),
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

#if !defined(__APPLE__)
BUILTIN_FUNCTION(os_sleep)
{
        ASSERT_ARGC("os.sleep()", 1);

        struct timespec dur;
        struct timespec rem = {0};

        clockid_t clk = CLOCK_REALTIME;
        int flags = 0;

        bool us = false;

        struct value *abs = NAMED("abs");

#ifndef _WIN32
        if (abs != NULL && abs->type == VALUE_BOOLEAN && abs->boolean) {
                flags = TIMER_ABSTIME;
        }
#endif

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
                dur = tuple_timespec(ty, "os.sleep()", &duration);
        } else {
                zP("the argument to os.sleep() must be an integer or a float");
        }

        lGv(true);
#ifdef _WIN32
        Sleep(dur.tv_sec * 1000 + dur.tv_nsec / 1000000);
        int ret = 0;
#else
        int ret = clock_nanosleep(clk, flags, &dur, &rem);
#endif
        lTk();

        switch (ret) {
        case 0:
                return NIL;
        case EINTR:
                return timespec_tuple(ty, &rem);
        default:
                zP("os.sleep(): invalid argument: clock_nanosleep() returned EINVAL");
        }
}
#else
BUILTIN_FUNCTION(os_sleep)
{
        ASSERT_ARGC("os.sleep()", 1);

        struct timespec dur;
        struct timespec rem = {0};

        bool us = false;

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
                dur = tuple_timespec(ty, "os.sleep()", &duration);
        } else {
                zP("the argument to os.sleep() must be an integer or a float");
        }

        lGv(true);
        int ret = nanosleep(&dur, &rem);
        lTk();

        switch (ret) {
        case 0:
                return NIL;
        case -1:
                if (errno == EINTR) {
                        return timespec_tuple(ty, &rem);
                } else {
                        zP("os.sleep(): invalid argument: nanosleep() returned EINVAL");
                }
        }
}
#endif

static int
microsleep(int64_t usec)
{
#ifdef _WIN32
        HANDLE timer;
        LARGE_INTEGER ft;

        ft.QuadPart = -(10*usec); // Convert to 100 nanosecond interval, negative value indicates relative time

        timer = CreateWaitableTimer(NULL, TRUE, NULL);
        SetWaitableTimer(timer, &ft, 0, NULL, NULL, 0);
        WaitForSingleObject(timer, INFINITE);
        CloseHandle(timer);
        return 0;
#else
        return usleep(usec);
#endif
}

// https://stackoverflow.com/questions/5801813/c-usleep-is-obsolete-workarounds-for-windows-mingw
BUILTIN_FUNCTION(os_usleep)
{
        ASSERT_ARGC("os.usleep()", 1);

        struct value duration = ARG(0);
        if (duration.type != VALUE_INTEGER)
                zP("the argument to os.usleep() must be an integer");

        if (duration.integer < 0)
                zP("negative argument passed to os.usleep()");

        return INTEGER(microsleep(duration.integer));
}

#ifdef _WIN32
BUILTIN_FUNCTION(os_listdir)
{
        ASSERT_ARGC("os.listdir()", 1);
        struct value dir = ARG(0);
        if (dir.type != VALUE_STRING)
                zP("the argument to os.listdir() must be a string");

        // Prepare the search path
        B.count = 0;
        vvPn(B, dir.string, dir.bytes);
        vvPn(B, "\\*", 2); // Add wildcard for all files
        vvP(B, '\0');

        WIN32_FIND_DATAA findData;
        HANDLE hFind = FindFirstFileA(B.items, &findData);
        if (hFind == INVALID_HANDLE_VALUE)
                return NIL;

        struct array* files = vA();
        struct value vFiles = ARRAY(files);
        gP(&vFiles);

        do {
                if (strcmp(findData.cFileName, ".") != 0 && strcmp(findData.cFileName, "..") != 0) {
                        vvP(*files, vSs(findData.cFileName, strlen(findData.cFileName)));
                }
        } while (FindNextFileA(hFind, &findData) != 0);

        DWORD dwError = GetLastError();
        if (dwError != ERROR_NO_MORE_FILES) {
                // Handle error if needed
        }

        FindClose(hFind);

        gX();

        return vFiles;
}
#else
BUILTIN_FUNCTION(os_listdir)
{
        ASSERT_ARGC("os.listdir()", 1);

        struct value dir = ARG(0);
        if (dir.type != VALUE_STRING)
                zP("the argument to os.listdir() must be a string");

        B.count = 0;
        vvPn(B, dir.string, dir.bytes);
        vvP(B, '\0');

        DIR *d = opendir(B.items);
        if (d == NULL)
                return NIL;


        struct array *files = vA();
        struct value vFiles = ARRAY(files);

        gP(&vFiles);

        struct dirent *e;

        while (e = readdir(d), e != NULL)
                if (strcmp(e->d_name, ".") != 0 && strcmp(e->d_name, "..") != 0)
                        vvP(*files, vSs(e->d_name, strlen(e->d_name)));

        closedir(d);

        gX();

        return vFiles;
}
#endif

static char *
resolve_path(char const *in, char *out)
{
#ifdef _WIN32
    char buffer[MAX_PATH];

    if (GetFullPathName(in, MAX_PATH, buffer, NULL) == 0) {
        return NULL;
    }

    if (GetLongPathName(buffer, out, MAX_PATH) == 0) {
        return NULL;
    }

    return out;
#else
    return realpath(in, out);
#endif
}


BUILTIN_FUNCTION(os_realpath)
{
        ASSERT_ARGC("os.realpath()", 1);

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                zP("the argument to os.realpath() must be a string");

        if (path.bytes >= PATH_MAX)
                return NIL;

        char in[PATH_MAX + 1];
        char out[PATH_MAX + 1];

        memcpy(in, path.string, path.bytes);
        in[path.bytes] = '\0';

        char *resolved = resolve_path(in, out);

        if (resolved == NULL)
                return NIL;

        return vSs(out, strlen(out));
}

BUILTIN_FUNCTION(os_ftruncate)
{
        ASSERT_ARGC("os.ftruncate()", 2);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("os.ftruncate(): expected integer as first argument but got: %s", VSC(&fd));

        struct value size = ARG(1);
        if (size.type != VALUE_INTEGER)
                zP("os.truncate(): expected integer as second argumnet but got: %s", VSC(&size));

        return INTEGER(ftruncate(fd.integer, size.integer));
}

static int
truncate_file(const char* filename, size_t size)
{
#ifdef _WIN32
    HANDLE hFile = CreateFile(
        filename,
        GENERIC_WRITE,
        0,
        NULL,
        OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL,
        NULL);

    if (hFile == INVALID_HANDLE_VALUE)
    {
        return -1;
    }

    LARGE_INTEGER li;
    li.QuadPart = size;

    if (!SetFilePointerEx(hFile, li, NULL, FILE_BEGIN)) {
        CloseHandle(hFile);
        return -1;
    }

    if (!SetEndOfFile(hFile)) {
        CloseHandle(hFile);
        return -1;
    }

    CloseHandle(hFile);

    return 0;
#else
    return truncate(filename, size);
#endif
}

BUILTIN_FUNCTION(os_truncate)
{
        ASSERT_ARGC("os.truncate()", 2);

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                zP("the first argument to os.truncate() must be a string");

        B.count = 0;
        vvPn(B, path.string, path.bytes);
        vvP(B, '\0');

        struct value size = ARG(1);
        if (size.type != VALUE_INTEGER)
                zP("os.truncate(): expected integer as second argumnet but got: %s", VSC(&size));

        return INTEGER(truncate_file(B.items, size.integer));
}

inline static Value
xstatv(int ret, StatStruct const *st)
{
        if (ret != 0)
               return NIL;

        return value_named_tuple(
                ty,
                "st_dev", INTEGER(st->st_dev),
                "st_ino", INTEGER(st->st_ino),
                "st_mode", INTEGER(st->st_mode),
                "st_nlink", INTEGER(st->st_nlink),
                "st_uid", INTEGER(st->st_uid),
                "st_gid", INTEGER(st->st_gid),
                "st_rdev", INTEGER(st->st_rdev),
                "st_size", INTEGER(st->st_size),
#ifndef _WIN32
                "st_blocks", INTEGER(st->st_blocks),
                "st_blksize", INTEGER(st->st_blksize),
#endif
#ifdef __APPLE__
                "st_atim", timespec_tuple(ty, &st->st_atimespec),
                "st_mtim", timespec_tuple(ty, &st->st_mtimespec),
                "st_ctim", timespec_tuple(ty, &st->st_ctimespec),
#elif defined(__linux__)
                "st_atim", timespec_tuple(ty, &st->st_atim),
                "st_mtim", timespec_tuple(ty, &st->st_mtim),
                "st_ctim", timespec_tuple(ty, &st->st_ctim),
#elif defined(_WIN32)
                "st_atim", INTEGER(st->st_atime),
                "st_mtim", INTEGER(st->st_mtime),
                "st_ctim", INTEGER(st->st_ctime),
#endif
                NULL
        );
}


BUILTIN_FUNCTION(os_fstat)
{
        ASSERT_ARGC("os.fstat()", 1);

        StatStruct s;

        Value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("os.fstat(): expected a file descriptor (Int) but got: %s", VSC(&fd));

        return xstatv(fstat(fd.integer, &s), &s);
}

BUILTIN_FUNCTION(os_lstat)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.lstat()");
#else
        ASSERT_ARGC("os.lstat()", 1);

        StatStruct s;

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                zP("the argument to os.lstat() must be a string");

        B.count = 0;
        vvPn(B, path.string, path.bytes);
        vvP(B, '\0');

        return xstatv(lstat(B.items, &s), &s);
#endif
}

BUILTIN_FUNCTION(os_stat)
{
        ASSERT_ARGC("os.stat()", 1);

        StatStruct s;

        struct value path = ARG(0);
        if (path.type != VALUE_STRING)
                zP("the argument to os.stat() must be a string");

        B.count = 0;
        vvPn(B, path.string, path.bytes);
        vvP(B, '\0');

        return xstatv(stat(B.items, &s), &s);
}

static int
lock_file(int fd, int operation)
{
#ifdef _WIN32

#define   LOCK_SH   1    /* shared lock */
#define   LOCK_EX   2    /* exclusive lock */
#define   LOCK_NB   4    /* don't block when locking */
#define   LOCK_UN   8    /* unlock */
        HANDLE hFile = (HANDLE)_get_osfhandle(fd);
        if (hFile == INVALID_HANDLE_VALUE)
        {
                return -1;
        }

        OVERLAPPED overlapped = {0};
        DWORD flags = 0;

        if (operation & LOCK_SH)
        {
                flags |= LOCKFILE_EXCLUSIVE_LOCK;
        }

        if (operation & LOCK_NB)
        {
                flags |= LOCKFILE_FAIL_IMMEDIATELY;
        }

        if (!LockFileEx(hFile, flags, 0, MAXDWORD, MAXDWORD, &overlapped))
        {
                return -1;
        }

        return 0;
#else
        return flock(fd, operation);
#endif
}


BUILTIN_FUNCTION(os_flock)
{
        ASSERT_ARGC("os.flock()", 2);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("the first argument to os.fcntl() must be an integer");

        struct value cmd = ARG(1);
        if (cmd.type != VALUE_INTEGER)
                zP("the second argument to os.fcntl() must be an integer");

        return INTEGER(lock_file(fd.integer, cmd.integer));
}

BUILTIN_FUNCTION(os_fcntl)
{
        ASSERT_ARGC_2("os.fcntl()", 2, 3);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.fcntl()")
#else

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("the first argument to os.fcntl() must be an integer");

        struct value cmd = ARG(1);
        if (cmd.type != VALUE_INTEGER)
                zP("the second argument to os.fcntl() must be an integer");

        if (argc == 2)
                return INTEGER(fcntl(fd.integer, cmd.integer));

        struct value arg = ARG(2);
        switch (cmd.integer) {
        case F_DUPFD:
        case F_SETFD:
        case F_SETFL:
        case F_SETOWN:
#ifdef __APPLE__
        case F_DUPFD_CLOEXEC:
#else
        case F_SETSIG:
#endif
                if (arg.type != VALUE_INTEGER)
                        zP("expected the third argument to be an integer in call to os.fcntl()");
                return INTEGER(fcntl(fd.integer, cmd.integer, (int) arg.integer));
        }

        zP("os.fcntl() functionality not implemented yet");
#endif
}

BUILTIN_FUNCTION(os_cpu_count)
{
        int nCPU;
#ifdef _WIN32
        SYSTEM_INFO sysinfo;
        GetSystemInfo(&sysinfo);
        nCPU = sysinfo.dwNumberOfProcessors;
#elif defined(__APPLE__) || defined(__MACH__)
        int mib[2];
        size_t len = sizeof nCPU;

        mib[0] = CTL_HW;
        mib[1] = HW_NCPU;

        if (sysctl(mib, 2, &nCPU, &len, NULL, 0) != 0) {
                nCPU = -1;
        }
#elif defined(__linux__)
        nCPU = sysconf(_SC_NPROCESSORS_ONLN);
#else
        nCPU = -1;
#endif
        return (nCPU <= 0) ? NIL : INTEGER(nCPU);
}

BUILTIN_FUNCTION(os_isatty)
{
        if (ARG(0).type != VALUE_INTEGER) {
                zP("os.isatty(): expected integer but got: %s", VSC(&ARG(0)));
        }

        return INTEGER(isatty(ARG(0).integer));
}

BUILTIN_FUNCTION(termios_tcgetattr)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcgetattr()");
#else
        if (ARG(0).type != VALUE_INTEGER) {
                zP("termios.tcgetattr(): expected integer but got: %s", VSC(&ARG(0)));
        }

        struct termios t;

        if (tcgetattr(ARG(0).integer, &t) != 0) {
                return NIL;
        }

        struct blob *cc = value_blob_new(ty);
        NOGC(cc);

        for (int i = 0; i < sizeof t.c_cc; ++i) {
                vvP(*cc, t.c_cc[i]);
        }

        Value v = vTn(
                "iflag", INTEGER(t.c_iflag),
                "oflag", INTEGER(t.c_oflag),
                "cflag", INTEGER(t.c_cflag),
                "lflag", INTEGER(t.c_lflag),
                "ispeed", INTEGER(t.c_ispeed),
                "ospeed", INTEGER(t.c_ospeed),
                "cc", BLOB(cc)
        );

        OKGC(cc);

        return v;
#endif
}

BUILTIN_FUNCTION(termios_tcsetattr)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcsetattr()");
#else
        if (ARG(0).type != VALUE_INTEGER) {
                zP("termios.tcsetattr(): expected integer but got: %s", VSC(&ARG(0)));
        }

        struct termios t;

        if (tcgetattr(ARG(0).integer, &t) != 0) {
                return BOOLEAN(false);
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("termios.tcsetattr(_, flags, _): expected integer but got: %s", VSC(&ARG(1)));
        }

        if (ARG(2).type != VALUE_TUPLE) {
                zP("termios.tcsetattr(_, _, t): expected tuple but got: %s", VSC(&ARG(2)));
        }

        struct value *iflag = tuple_get(&ARG(2), "iflag");
        struct value *oflag = tuple_get(&ARG(2), "oflag");
        struct value *cflag = tuple_get(&ARG(2), "cflag");
        struct value *lflag = tuple_get(&ARG(2), "lflag");
        struct value *ispeed = tuple_get(&ARG(2), "ispeed");
        struct value *ospeed = tuple_get(&ARG(2), "ospeed");
        struct value *cc = tuple_get(&ARG(2), "cc");

        if (iflag != NULL && iflag->type == VALUE_INTEGER) { t.c_iflag = iflag->integer; }
        if (oflag != NULL && oflag->type == VALUE_INTEGER) { t.c_oflag = oflag->integer; }
        if (cflag != NULL && cflag->type == VALUE_INTEGER) { t.c_cflag = cflag->integer; }
        if (lflag != NULL && lflag->type == VALUE_INTEGER) { t.c_lflag = lflag->integer; }
        if (ispeed != NULL && ispeed->type == VALUE_INTEGER) { t.c_ispeed = ispeed->integer; }
        if (ospeed != NULL && ospeed->type == VALUE_INTEGER) { t.c_ospeed = ospeed->integer; }

        if (cc != NULL && cc->type == VALUE_BLOB) {
                for (int i = 0; i < min(cc->blob->count, sizeof t.c_cc); ++i) {
                        t.c_cc[i] = cc->blob->items[i];
                }
        }

        return BOOLEAN(tcsetattr(ARG(0).integer, ARG(1).integer, &t) == 0);
#endif
}

BUILTIN_FUNCTION(errno_get)
{
        ASSERT_ARGC("errno.get()", 0);
        return INTEGER(errno);
}

BUILTIN_FUNCTION(errno_str)
{
        ASSERT_ARGC_2("errno.str()", 0, 1);

        int e;

        if (argc == 0) {
                e = errno;
        } else {
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the argument to errno.str() must be an integer");
                e = ARG(0).integer;
        }

        char const *s = strerror(e);

        return vSs(s, strlen(s));
}

BUILTIN_FUNCTION(time_gettime)
{
        ASSERT_ARGC_2("time.gettime()", 0, 1);

        clockid_t clk;
        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER)
                        zP("the argument to time.gettime() must be an integer");
                clk = v.integer;
        } else {
                clk = CLOCK_REALTIME;
        }

        struct timespec t = {0};
        clock_gettime(clk, &t);

        return timespec_tuple(ty, &t);
}

BUILTIN_FUNCTION(time_utime)
{
        struct timespec t;
#ifdef _WIN32
        ASSERT_ARGC("time.utime()", 0);
        GetCurrentTimespec(&t);
#else
        ASSERT_ARGC_2("time.utime()", 0, 1);

        clockid_t clk;
        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER)
                        zP("the argument to time.utime() must be an integer");
                clk = v.integer;
        } else {
                clk = CLOCK_REALTIME;
        }

        clock_gettime(clk, &t);
#endif
        return INTEGER((uint64_t)t.tv_sec * 1000 * 1000 + (uint64_t)t.tv_nsec / 1000);
}

BUILTIN_FUNCTION(time_localtime)
{
        ASSERT_ARGC_2("time.localtime()", 0, 1);

        time_t t;

        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER) {
                        zP("the argument to time.localtime() must be an integer");
                }
                t = v.integer;
        } else {
                t = time(NULL);
        }

        struct tm r = {0};
        localtime_r(&t, &r);

        return vTn(
                "sec",   INTEGER(r.tm_sec),
                "min",   INTEGER(r.tm_min),
                "hour",  INTEGER(r.tm_hour),
                "mday",  INTEGER(r.tm_mday),
                "mon",   INTEGER(r.tm_mon),
                "year",  INTEGER(r.tm_year),
                "wday",  INTEGER(r.tm_wday),
                "yday",  INTEGER(r.tm_yday),
                "isdst", BOOLEAN(r.tm_isdst)
        );
}

BUILTIN_FUNCTION(time_gmtime)
{
        ASSERT_ARGC_2("time.gmtime()", 0, 1);

        time_t t;

        if (argc == 1) {
                struct value v = ARG(0);
                if (v.type != VALUE_INTEGER) {
                        zP("the argument to time.gmtime() must be an integer");
                }
                t = v.integer;
        } else {
                t = time(NULL);
        }

        struct tm r = {0};
        gmtime_r(&t, &r);

        return vTn(
                "sec",   INTEGER(r.tm_sec),
                "min",   INTEGER(r.tm_min),
                "hour",  INTEGER(r.tm_hour),
                "mday",  INTEGER(r.tm_mday),
                "mon",   INTEGER(r.tm_mon),
                "year",  INTEGER(r.tm_year),
                "wday",  INTEGER(r.tm_wday),
                "yday",  INTEGER(r.tm_yday),
                "isdst", BOOLEAN(r.tm_isdst)
        );
}

BUILTIN_FUNCTION(time_strftime)
{
        ASSERT_ARGC_2("time.strftime()", 1, 2);

        struct tm t = {0};

        struct value fmt = ARG(0);
        if (fmt.type != VALUE_STRING) {
                zP("the first argument to time.strftime() must be a string");
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
                        zP("the second argument to time.strftime() must be an integer or named tuple");
                }
        } else {
                time_t sec = time(NULL);
                localtime_r(&sec, &t);
        }

        B.count = 0;
        vvPn(B, fmt.string, fmt.bytes);
        vvP(B, '\0');

        int n = strftime(buffer, sizeof buffer, B.items, &t);

        if (n > 0) {
                return vSs(buffer, n);
        } else {
                return NIL;
        }
}

BUILTIN_FUNCTION(time_strptime)
{
        ASSERT_ARGC("time.strptime()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("time.strptime()");
#else

        struct value s = ARG(0);
        struct value fmt = ARG(1);

        if (s.type != VALUE_STRING || fmt.type != VALUE_STRING) {
                zP("both arguments to time.strptime() must be strings");
        }

        B.count = 0;

        vvPn(B, s.string, s.bytes);
        vvP(B, '\0');

        vvPn(B, fmt.string, fmt.bytes);
        vvP(B, '\0');

        char const *sp = B.items;
        char const *fp = B.items + s.bytes + 1;

        struct tm r = {0};
        strptime(sp, fp, &r);

        return vTn(
                "sec",   INTEGER(r.tm_sec),
                "min",   INTEGER(r.tm_min),
                "hour",  INTEGER(r.tm_hour),
                "mday",  INTEGER(r.tm_mday),
                "mon",   INTEGER(r.tm_mon),
                "year",  INTEGER(r.tm_year),
                "wday",  INTEGER(r.tm_wday),
                "yday",  INTEGER(r.tm_yday),
                "isdst", BOOLEAN(r.tm_isdst)
        );
#endif
}

BUILTIN_FUNCTION(time_time)
{
        ASSERT_ARGC_2("time.time()", 0, 1);

        if (argc == 0) {
                return INTEGER(time(NULL));
        }

        struct tm t = {0};
        struct value v = ARG(0);

        if (v.type != VALUE_TUPLE) {
                zP("the argument to time.time() must be a named tuple");
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
                utc != NULL && value_truthy(ty, utc)
                ? timegm(&t)
                : mktime(&t)
        );
}

BUILTIN_FUNCTION(stdio_fileno)
{
        ASSERT_ARGC("stdio.fileno()", 1);

        if (ARG(0).type != VALUE_PTR) {
                zP("the argument to stdio.fileno() must be a pointer");
        }

        return INTEGER(fileno(ARG(0).ptr));
}

BUILTIN_FUNCTION(stdio_fdopen)
{
        ASSERT_ARGC_2("stdio.fdopen()", 1, 2);

        struct value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("the first argument to stdio.fdopen() must be an integer");

        char mode[16] = "a+";
        if (argc == 2) {
                struct value m = ARG(1);
                if (m.type != VALUE_STRING)
                        zP("the second argument to stdio.fdopen() must be a string");
                if (m.bytes >= sizeof mode)
                        zP("invalid mode string %s passed to stdio.fdopen()", VSC(&m));
                memcpy(mode, m.string, m.bytes);
                mode[m.bytes] = '\0';
        }

        FILE *f = fdopen(fd.integer, mode);
        if (f == NULL)
                return NIL;

        return PTR(f);
}

BUILTIN_FUNCTION(stdio_tmpfile)
{
        ASSERT_ARGC("stdio.tmpfile()", 0);

        FILE *f = tmpfile();

        return (f == NULL) ? NIL : PTR(f);
}

BUILTIN_FUNCTION(stdio_fgets)
{
        ASSERT_ARGC("stdio.fgets()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fgets() must be a pointer");

        FILE *fp = f.ptr;

        B.count = 0;

        int c;

        lGv(true);
        while ((c = fgetc_unlocked(fp)) != EOF && c != '\n') {
                vvP(B, c);
        }
        lTk();

        if (B.count == 0 && c == EOF)
                return NIL;

        struct value s;

        if (B.count == 0) {
                s = (c == EOF) ? NIL : STRING_EMPTY;
        } else {
                s = vSs(B.items, B.count);
        }

        return s;
}

BUILTIN_FUNCTION(stdio_read_signed)
{
        ASSERT_ARGC_2("stdio.readSigned()", 1, 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readSigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected intger as second argument to stdio.readSigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).integer;
        } else {
                size = sizeof size;
        }

        char b[sizeof (intmax_t)];
        int n = min(sizeof b, size);

        lGv(true);
        if (fread(b, n, 1, fp) != 1) {
                lTk();
                return NIL;
        }
        lTk();

        switch (size) {
        case (sizeof (char)):      return INTEGER(*(char *)b);
        case (sizeof (short)):     return INTEGER(*(short *)b);
        case (sizeof (int)):       return INTEGER(*(int *)b);
        case (sizeof (long long)): return INTEGER(*(long long *)b);
        default: return NIL;
        }
}

BUILTIN_FUNCTION(stdio_write_signed)
{
        ASSERT_ARGC_2("stdio.writeSigned()", 2, 3);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeSigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        struct value x;

        if (argc == 3) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected intger as second argument to stdio.writeSigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).integer;
                x = ARG(2);
        } else {
                size = sizeof (int);
                x = ARG(3);
        }

        if (x.type != VALUE_INTEGER) {
                zP("stdio.writeUnsigned(): expected int as last argument but got: %s", VSC(&x));
        }

        char b[sizeof (intmax_t)];

        switch (size) {
        case (sizeof (char)):      memcpy(b, &(char)     {x.integer}, size); break;
        case (sizeof (short)):     memcpy(b, &(short)    {x.integer}, size); break;
        case (sizeof (int)):       memcpy(b, &(int)      {x.integer}, size); break;
        case (sizeof (long long)): memcpy(b, &(long long){x.integer}, size); break;
        default: return BOOLEAN(false);
        }

        lGv(true);
        size_t n = fwrite_unlocked(b, size, 1, fp);
        lTk();

        return BOOLEAN(n == 1);
}

BUILTIN_FUNCTION(stdio_read_unsigned)
{
        ASSERT_ARGC_2("stdio.readUnsigned()", 1, 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readUnsigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected intger as second argument to stdio.readUnsigned() but got: %s", VSC(&ARG(1)));
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

BUILTIN_FUNCTION(stdio_write_unsigned)
{
        ASSERT_ARGC_2("stdio.writeUnsigned()", 2, 3);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeUnsigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        struct value x;

        if (argc == 3) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected intger as second argument to stdio.writeUnsigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).integer;
                x = ARG(2);
        } else {
                size = sizeof (int);
                x = ARG(3);
        }

        if (x.type != VALUE_INTEGER) {
                zP("stdio.writeUnsigned(): expected int as last argument but got: %s", VSC(&x));
        }

        char b[sizeof (uintmax_t)];

        switch (size) {
        case (sizeof (unsigned char)):      memcpy(b, &(unsigned char)     {x.integer}, size); break;
        case (sizeof (unsigned short)):     memcpy(b, &(unsigned short)    {x.integer}, size); break;
        case (sizeof (unsigned int)):       memcpy(b, &(unsigned int)      {x.integer}, size); break;
        case (sizeof (unsigned long long)): memcpy(b, &(unsigned long long){x.integer}, size); break;
        default: return BOOLEAN(false);
        }

        lGv(true);
        size_t n = fwrite_unlocked(b, size, 1, fp);
        lTk();

        return BOOLEAN(n == 1);
}

BUILTIN_FUNCTION(stdio_read_double)
{
        ASSERT_ARGC("stdio.readDouble()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readDouble() must be a pointer");

        double x;
        FILE *fp = f.ptr;

        lGv(true);

        if (fread_unlocked(&x, sizeof x, 1, fp) == 1) {
                lTk();
                return REAL(x);
        } else {
                lTk();
                return NIL;
        }
}

BUILTIN_FUNCTION(stdio_read_float)
{
        ASSERT_ARGC("stdio.readFloat()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readFloat() must be a pointer");

        float x;
        FILE *fp = f.ptr;

        lGv(true);

        if (fread_unlocked(&x, sizeof x, 1, fp) == 1) {
                lTk();
                return REAL(x);
        } else {
                lTk();
                return NIL;
        }
}

BUILTIN_FUNCTION(stdio_write_float)
{
        ASSERT_ARGC("stdio.writeFloat()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeFloat() must be a pointer");

        struct value x = ARG(1);
        if (x.type != VALUE_REAL)
                zP("the second argument to stdio.writeFloat() must be a float");

        FILE *fp = f.ptr;
        float fx = (float)x.real;

        lGv(true);

        size_t n = fwrite_unlocked(&fx, sizeof fx, 1, fp);

        lTk();

        return BOOLEAN(n > 0);
}

BUILTIN_FUNCTION(stdio_write_double)
{
        ASSERT_ARGC("stdio.writeDouble()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeDouble() must be a pointer");

        struct value x = ARG(1);
        if (x.type != VALUE_REAL)
                zP("the second argument to stdio.writeDouble() must be a float");

        FILE *fp = f.ptr;
        double fx = x.real;

        lGv(true);

        size_t n = fwrite_unlocked(&fx, sizeof fx, 1, fp);

        lTk();

        return BOOLEAN(n > 0);
}

BUILTIN_FUNCTION(stdio_fread)
{
        ASSERT_ARGC_2("stdio.fread()", 2, 3);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.fread() must be a pointer");

        struct value n = ARG(1);
        if (n.type != VALUE_INTEGER || n.integer < 0)
                zP("the second argument to stdio.fread() must be a non-negative integer");

        struct blob *b;
        bool existing_blob = (argc == 3) && ARG(2).type != VALUE_NIL;

        if (existing_blob) {
                if (ARG(2).type != VALUE_BLOB) {
                        zP("stdio.fread() expects a blob as the third argument but got: %s", VSC(&ARG(2)));
                }
                b = ARG(2).blob;
        } else {
                b = value_blob_new(ty);
        }

        NOGC(b);

        FILE *fp = f.ptr;
        intmax_t bytes = 0;
        int c;

        lGv(true);
        while (bytes < n.integer && (c = fgetc_unlocked(fp)) != EOF) {
                vvP(*b, c);
                bytes += 1;
        }
        lTk();

        OKGC(b);

        if (existing_blob) {
                return INTEGER(bytes);
        } else {
                if (b->count == 0 && n.integer > 0 && c == EOF)
                        return NIL;

                return BLOB(b);
        }
}

BUILTIN_FUNCTION(stdio_slurp)
{
        ASSERT_ARGC("stdio.slurp(ty)", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.slurp(ty) must be a pointer");

        FILE *fp = f.ptr;
        int c;

        B.count = 0;

        lGv(true);
        while ((c = fgetc_unlocked(fp)) != EOF) {
                vvP(B, c);
        }
        lTk();

        if (c == EOF && B.count == 0)
                return NIL;

        struct value s = vSs(B.items, B.count);

        return s;
}

BUILTIN_FUNCTION(stdio_fgetc)
{
        ASSERT_ARGC("stdio.fgetc()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fgetc() must be a pointer");

        lGv(true);
        int c = fgetc_unlocked(f.ptr);
        lTk();

        if (c == EOF)
                return NIL;
        else
                return INTEGER(c);
}

BUILTIN_FUNCTION(stdio_fputc)
{
        ASSERT_ARGC("stdio.fputc()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.fputc() must be a pointer");

        if (ARG(1).type != VALUE_INTEGER) {
                zP("the second argument to stdio.fputc() must be an integer");
        }

        lGv(true);
        int c = fputc_unlocked((int)ARG(1).integer, f.ptr);
        lTk();

        if (c == EOF)
                return NIL;
        else
                return INTEGER(c);
}

BUILTIN_FUNCTION(stdio_fwrite)
{
        ASSERT_ARGC("stdio.fwrite()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fwrite() must be a pointer");

        struct value s = ARG(1);

        switch (s.type) {
        case VALUE_STRING:
                return INTEGER(fwrite_unlocked(s.string, 1, s.bytes, f.ptr));
        case VALUE_BLOB:
                return INTEGER(fwrite_unlocked(s.blob->items, 1, s.blob->count, f.ptr));
        case VALUE_INTEGER:
                return INTEGER(fputc_unlocked((unsigned char)s.integer, f.ptr));
        default:
                zP("invalid type for second argument passed to stdio.fwrite()");
        }
}

BUILTIN_FUNCTION(stdio_puts)
{
        ASSERT_ARGC("stdio.puts()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.puts() must be a pointer");

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
                zP("the second argument to stdio.puts() must be a string or a blob");
        }

        if (fputc_unlocked('\n', f.ptr) == EOF)
                return NIL;

        return INTEGER(r + 1);
}

BUILTIN_FUNCTION(stdio_fflush)
{
        ASSERT_ARGC("stdio.fflush()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fflush() must be a pointer");

        if (fflush(f.ptr) == EOF)
                return NIL;

        return INTEGER(0);
}

BUILTIN_FUNCTION(stdio_fclose)
{
        ASSERT_ARGC("stdio.fclose()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fclose() must be a pointer");

        if (fclose(f.ptr) == EOF)
                return NIL;

        return INTEGER(0);
}

BUILTIN_FUNCTION(stdio_clearerr)
{
        ASSERT_ARGC("stdio.clearerr()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.clearerr() must be a pointer");

        clearerr(f.ptr);

        return NIL;
}

BUILTIN_FUNCTION(stdio_setvbuf)
{
        ASSERT_ARGC("stdio.setvbuf()", 2);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.setvbuf() must be a pointer");

        struct value mode = ARG(1);
        if (mode.type != VALUE_INTEGER)
                zP("the second argument to stdio.setvbuf() must be an integer");

        return INTEGER(setvbuf(f.ptr, NULL, mode.integer, 0));
}

BUILTIN_FUNCTION(stdio_ftell)
{
        ASSERT_ARGC("stdio.ftell()", 1);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.ftell() must be a pointer");

        return INTEGER(ftell(f.ptr));
}

BUILTIN_FUNCTION(stdio_fseek)
{
        ASSERT_ARGC("stdio.fseek()", 3);

        struct value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.fseek() must be a pointer");

        struct value off = ARG(1);
        if (off.type != VALUE_INTEGER)
                zP("the second argument to stdio.fseek() must be an integer");

        struct value whence = ARG(2);
        if (whence.type != VALUE_INTEGER)
                zP("the third argument to stdio.fseek() must be an integer");

        return INTEGER(fseek(f.ptr, off.integer, whence.integer));
}

BUILTIN_FUNCTION(object)
{
        ASSERT_ARGC("object()", 1);

        struct value class = ARG(0);
        if (class.type != VALUE_CLASS)
                zP("the argument to object() must be a class");

        return OBJECT(object_new(ty, class.class), class.class);
}

BUILTIN_FUNCTION(bind)
{
        ASSERT_ARGC("bindMethod()", 2);

        struct value f = ARG(0);
        struct value x = ARG(1);

        struct value *this;
        struct value *fp;

        if (f.type == VALUE_METHOD) {
                this = mAo(sizeof x, GC_VALUE);
                *this = x;
                return METHOD(f.name, f.method, this);
        }

        if (f.type == VALUE_FUNCTION) {
                this = mAo(sizeof x, GC_VALUE);
                NOGC(this);
                *this = x;
                fp = mAo(sizeof x, GC_VALUE);
                *fp = f;
                OKGC(this);
                return METHOD(f.name, fp, this);
        }

        return f;
}

BUILTIN_FUNCTION(doc_ref)
{
        ASSERT_ARGC("docRef()", 1);

        Value f = ARG(0);

        if (f.type == VALUE_METHOD) {
                return *f.method;
        } else if (f.type == VALUE_BUILTIN_METHOD) {
                return PTR((void *)f.builtin_method);
        } else {
                return f;
        }
}

BUILTIN_FUNCTION(unbind)
{
        ASSERT_ARGC("unbindMethod()", 1);

        Value f = ARG(0);

        if (f.type == VALUE_METHOD) {
                return *f.method;
        } else {
                return f;
        }
}

BUILTIN_FUNCTION(define_method)
{
        ASSERT_ARGC("defineMethod()", 3);

        struct value class = ARG(0);
        struct value name = ARG(1);
        struct value f = ARG(2);

        if (class.type != VALUE_CLASS) {
                zP("the first argument to defineMethod() must be a class");
        }

        if (name.type != VALUE_STRING) {
                zP("the second argument to defineMethod() must be a string");
        }

        if (f.type != VALUE_FUNCTION) {
                zP("the third argument to defineMethod() must be a function");
        }

        snprintf(buffer, sizeof buffer, "%*s", (int)name.bytes, name.string);

        class_add_method(ty, class.class, sclone(ty, buffer), f);

        return NIL;
}

BUILTIN_FUNCTION(apply)
{
        if (argc == 0) {
                zP("apply() expects at least 1 argument but got %d", argc);
        }

        Value g = ARG(0);
        Value *self = NAMED("self");

        Value *collect = NAMED("collect");
        Value *kws = NAMED("kwargs");

        Value f = (self == NULL || g.type != VALUE_METHOD) ? g : METHOD(g.name, &g, self);

        if (!CALLABLE(f)) {
                zP("apply(): non-callable argument: %s", VSC(&f));
        }

        for (int i = 1; i < argc; ++i) {
                vmP(&ARG(1));
        }

        return vm_call_ex(
                ty,
                &f,
                argc - 1,
                kws,
                collect != NULL && value_truthy(ty, collect)
        );
}

BUILTIN_FUNCTION(type)
{
        ASSERT_ARGC("type()", 1);

        struct value v = ARG(0);

        if (v.type == VALUE_TUPLE) {
                int n = v.count;

                if (n == 0) {
                        return v;
                }

                struct value *types = mAo(n * sizeof (Value), GC_TUPLE);

                NOGC(types);

                for (int i = 0; i < n; ++i) {
                        vmP(&v.items[i]);
                        types[i] = builtin_type(ty, 1, NULL);
                        vmX();
                }

                OKGC(types);

                return TUPLE(types, NULL, n, false);
        }

        if (v.tags != 0) {
                return TAG(tags_first(ty, v.tags));
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
        case VALUE_FUNCTION:  return (struct value) { .type = VALUE_CLASS, .class = CLASS_FUNCTION  };
        case VALUE_GENERATOR: return (struct value) { .type = VALUE_CLASS, .class = CLASS_GENERATOR };
        case VALUE_TAG:       return (struct value) { .type = VALUE_CLASS, .class = CLASS_TAG       };
        case VALUE_PTR:       return PTR(NULL);
        default:
        case VALUE_NIL:      return NIL;
        }
}

BUILTIN_FUNCTION(subclass)
{
        ASSERT_ARGC("subclass?()", 2);

        struct value sub = ARG(0);
        struct value super = ARG(1);

        if (sub.type != VALUE_CLASS || super.type != VALUE_CLASS) {
                zP("the arguments to subclass?() must be classes");
        }

        return BOOLEAN(class_is_subclass(ty, sub.class, super.class));
}

BUILTIN_FUNCTION(members_list)
{
        ASSERT_ARGC("members()", 1);

        struct value o = ARG(0);

        Array *a = vA();
        Value items = ARRAY(a);

        gP(&items);

        switch (o.type) {
        case VALUE_OBJECT:
                for (int i = 0; i < ITABLE_SIZE; ++i) {
                        for (int v = 0; v < o.object->buckets[i].values.count; ++v) {
                                char const *key = intern_entry(&xD.members, o.object->buckets[i].ids.items[v])->name;
                                Value member = vT(2);
                                NOGC(member.items);
                                member.items[0] = vSs(key, strlen(key));
                                member.items[1] = o.object->buckets[i].values.items[v];
                                NOGC(member.items[0].string);
                                vAp(a, member);
                                OKGC(member.items[0].string);
                                OKGC(member.items);
                        }
                }

                break;
        case VALUE_TUPLE:
                for (int i = 0; i < o.count; ++i) {
                        Value entry = vT(2);
                        Value *pair = entry.items;
                        NOGC(pair);
                        vAp(a, entry);
                        if (o.ids != NULL && o.ids[i] != -1) {
                                char const *name = intern_entry(&xD.members, o.ids[i])->name;
                                pair[0] = vSs(name, strlen(name));
                                pair[1] = o.items[i];
                        } else {
                                pair[0] = INTEGER(i);
                                pair[1] = o.items[i];
                        }
                        OKGC(pair);
                }

                break;
        default:
                gX();
                return NIL;
        }

        gX();

        return items;
}

BUILTIN_FUNCTION(members)
{
        ASSERT_ARGC("members()", 1);

        Value *list = NAMED("list");
        if (list != NULL && value_truthy(ty, list)) {
                return builtin_members_list(ty, argc, NULL);
        }

        struct value o = ARG(0);

        struct dict *members = dict_new(ty);
        struct value vMembers = DICT(members);

        gP(&vMembers);

        switch (o.type) {
        case VALUE_OBJECT:
                for (int i = 0; i < ITABLE_SIZE; ++i) {
                        for (int v = 0; v < o.object->buckets[i].values.count; ++v) {
                                char const *key = intern_entry(&xD.members, o.object->buckets[i].ids.items[v])->name;
                                dict_put_member(ty, members, key, o.object->buckets[i].values.items[v]);
                        }
                }

                break;
        case VALUE_TUPLE:
                for (int i = 0; i < o.count; ++i) {
                        if (o.ids != NULL && o.ids[i] != -1) {
                                char const *name = intern_entry(&xD.members, o.ids[i])->name;
                                struct value key = vSs(name, strlen(name));
                                NOGC(key.string);
                                dict_put_value(ty, members, key, o.items[i]);
                                OKGC(key.string);
                        } else {
                                dict_put_value(ty, members, INTEGER(i), o.items[i]);
                        }
                }

                break;
        default:
                gX();
                return NIL;
        }

        gX();

        return DICT(members);
}

BUILTIN_FUNCTION(member)
{
        ASSERT_ARGC_2("member()", 2, 3);

        Value o = ARG(0);
        Value name = ARG(1);

        if (name.type != VALUE_STRING) {
                zP("the second argument to member() must be a string");
        }

        if (name.bytes >= sizeof buffer) {
                // sus
                return NIL;
        }

        memcpy(buffer, name.string, name.bytes);
        buffer[name.bytes] = '\0';

        int id = M_ID(buffer);

        if (argc == 2) {
                Value v = GetMember(ty, o, id, false);
                return (v.type == VALUE_NONE) ? NIL : v;
        } else if (o.type == VALUE_OBJECT) {
                itable_add(
                        ty,
                        o.object,
                        id,
                        ARG(2)
                );
                return ARG(2);
        } else {
                zP("member(o, _, _): expected object but got: %s", VSC(&o));
        }
}

BUILTIN_FUNCTION(finalizer)
{
        ASSERT_ARGC("setFinalizer()", 2);

        if (ARG(0).type != VALUE_OBJECT) {
                zP("the first argument to setFinalizer() must be an object");
        }

        if (!CALLABLE(ARG(1))) {
                zP("the second argument to setFinalizer() must be callable");
        }

        ARG(0).object->finalizer = ARG(1);

        return NIL;
}

static struct value
fdoc(Ty *ty, struct value const *f)
{
        char name_buf[512] = {0};

        char const *s = doc_of(f);
        char const *name = name_of(f);
        char const *proto = proto_of(f);

        GC_STOP();

        struct value n;
        if (f->info[6] != -1) {
                snprintf(name_buf, sizeof name_buf, "%s.%s", class_name(ty, f->info[6]), name);
                n = vSs(name_buf, strlen(name_buf));
        } else if (name != NULL) {
                n = vSs(name, strlen(name));
        } else {
                n = NIL;
        }
        struct value p = (proto == NULL) ? NIL : vSs(proto, strlen(proto));
        struct value doc = (s == NULL) ? NIL : vSs(s, strlen(s));
        struct value v = vT(3);
        v.items[0] = n;
        v.items[1] = p;
        v.items[2] = doc;

        GC_RESUME();

        return v;
}

static void
mdocs(Ty *ty, struct itable const *t, struct array *a)
{
        for (int i = 0; i < TABLE_SIZE; ++i) {
                for (int j = 0; j < t->buckets[i].values.count; ++j) {
                        vAp(a, fdoc(ty, &t->buckets[i].values.items[j]));
                }
        }
}

BUILTIN_FUNCTION(set_doc)
{
        ASSERT_ARGC("set-doc()", 1);

        Value f = ARG(0);

        if (f.type != VALUE_FUNCTION) {
                zP("set-doc(): expected function but got: %s", VSC(&f));
        }

        Value *name = NAMED("name");
        Value *proto = NAMED("proto");
        Value *doc = NAMED("doc");

        if (f.xinfo == NULL) {
                f.xinfo = mAo0(sizeof (FunUserInfo), GC_ANY);
        }

        if (name != NULL && name->type != VALUE_NIL) {
                if (name->type != VALUE_STRING) {
                        zP("set-doc(): non-string passed as `name`: %s", VSC(name));
                }
                BufferCString(name);
                f.xinfo->name = sclone(ty, buffer);
        }

        if (proto != NULL && proto->type != VALUE_NIL) {
                if (proto->type != VALUE_STRING) {
                        zP("set-doc(): non-string passed as `proto`: %s", VSC(proto));
                }
                BufferCString(proto);
                f.xinfo->proto = sclone(ty, buffer);
        }

        if (doc != NULL && doc->type != VALUE_NIL) {
                if (doc->type != VALUE_STRING) {
                        zP("set-doc(): non-string passed as `doc`: %s", VSC(doc));
                }
                BufferCString(doc);
                f.xinfo->doc = sclone(ty, buffer);
        }

        return f;
}

BUILTIN_FUNCTION(doc)
{
        char mod[256];
        char id[256];

        if (argc == 0 || argc > 2) {
                zP("doc(): expected 1 or 2 arguments but got: %d", argc);
        }

        if (ARG(0).type == VALUE_FUNCTION) {
                return fdoc(ty, &ARG(0));
        }

        if (ARG(0).type == VALUE_CLASS) {
                GC_STOP();

                char const *s = class_doc(ty, ARG(0).class);
                char const *name = class_name(ty, ARG(0).class);
                struct value v = vT(3);
                v.items[0] = STRING_NOGC(name, strlen(name));
                v.items[1] = (s == NULL) ? NIL : vSs(s, strlen(s));
                v.items[2] = ARRAY(vA());
                mdocs(ty, class_methods(ty, ARG(0).class), v.items[2].array);
                mdocs(ty, class_static_methods(ty, ARG(0).class), v.items[2].array);
                mdocs(ty, class_getters(ty, ARG(0).class), v.items[2].array);
                mdocs(ty, class_setters(ty, ARG(0).class), v.items[2].array);

                GC_RESUME();

                return v;
        }

        if (ARG(0).type != VALUE_STRING) {
                return NIL;
        }

        snprintf(id, sizeof id, "%.*s", (int)ARG(0).bytes, ARG(0).string);

        struct symbol *s;

        if (argc == 2) {
                if (ARG(1).type != VALUE_STRING) {
                        zP("doc(): expected function or string but got: %s", VSC(&ARG(1)));
                }
                snprintf(mod, sizeof mod, "%.*s", (int)ARG(1).bytes, ARG(1).string);
                s = compiler_lookup(ty, mod, id);
        } else {
                s = compiler_lookup(ty, NULL, id);
        }

        if (s == NULL || s->doc == NULL)
                return NIL;

        return vSsz(s->doc);
}

BUILTIN_FUNCTION(ty_gc)
{
        ASSERT_ARGC("ty.gc()", 0);
        DoGC(ty);
        return NIL;
}

BUILTIN_FUNCTION(ty_bt)
{
        ASSERT_ARGC("ty.bt()", 0);

        FrameStack *frames = vm_get_frames(ty);
        Array *avFrames = vA();

        GC_STOP();

        for (size_t i = 0; i < frames->count; ++i) {
                if (frames->items[i].ip == NULL) {
                        continue;
                }

                Value *f = &frames->items[i].f;

                if (((char *)f->info)[FUN_HIDDEN]) {
                        continue;
                }

                char const *name = name_of(f);
                char const *ip = frames->items[i].ip;
                Expr const *e = compiler_find_expr(ty, ip - 1);

                Value entry = vT(5);

                entry.items[0] = *f;
                entry.items[1] = STRING_NOGC(name, strlen(name));
                entry.items[2] = (e == NULL) ? NIL : STRING_NOGC(e->file, strlen(e->file));
                entry.items[3] = (e == NULL) ? NIL : INTEGER(e->start.line);
                entry.items[4] = (e == NULL) ? NIL : INTEGER(e->start.col);

                vAp(avFrames, entry);
        }

        GC_RESUME();

        return ARRAY(avFrames);
}

BUILTIN_FUNCTION(ty_unlock)
{
        lGv(true);
        return NIL;
}

BUILTIN_FUNCTION(ty_lock)
{
        lTk();
        return NIL;
}

BUILTIN_FUNCTION(ty_gensym)
{
        ASSERT_ARGC("ty.gensym(ty)", 0);

        char const *s = gensym(ty);

        return STRING_NOGC(s, strlen(s));
}

inline static char const *
beginning_of(char const *s)
{
        while (s && s[-1]) --s;
        return s;
}

static Value
make_location(Ty *ty, Location const *loc)
{
        return vTn(
                "line", INTEGER(loc->line),
                "col",  INTEGER(loc->col),
                "byte", INTEGER(loc->byte)
        );
}

Value
make_token(Ty *ty, Token const *t)
{
        char *type = NULL;

        Value start = make_location(ty, &t->start);
        Value end = make_location(ty, &t->end);

#define T(name) (STRING_NOGC(#name, strlen(#name)))
        switch (t->type) {
        case TOKEN_IDENTIFIER:
                return vTn(
                        "type",   T(id),
                        "start",  start,
                        "end",    end,
                        "id",     STRING_NOGC(t->identifier, strlen(t->identifier)),
                        "module", t->module == NULL ? NIL : STRING_NOGC(t->module, strlen(t->module))
                );
        case TOKEN_INTEGER:
                return vTn(
                        "type",   T(int),
                        "start",  start,
                        "end",    end,
                        "int",    INTEGER(t->integer)
                );
        case TOKEN_REAL:
                return vTn(
                        "type",   T(int),
                        "start",  start,
                        "end",    end,
                        "float",  INTEGER(t->real)
                );
        case TOKEN_STRING:
                return vTn(
                        "type",   T(string),
                        "start",  start,
                        "end",    end,
                        "str",    STRING_NOGC(t->string, strlen(t->string))
                );
        case TOKEN_COMMENT:
                return vTn(
                        "type",    T(comment),
                        "start",   start,
                        "end",     end,
                        "comment", STRING_NOGC(t->comment, strlen(t->comment))
                );
        case TOKEN_END:
                return NIL;
        case TOKEN_DOT_DOT:         type = "..";   break;
        case TOKEN_DOT_DOT_DOT:     type = "...";  break;
        case TOKEN_AT:              type = "@";    break;
        case TOKEN_INC:             type = "++";   break;
        case TOKEN_BANG:            type = "!";    break;
        case TOKEN_EQ:              type = "=";    break;
        case TOKEN_NOT_EQ:          type = "!=";   break;
        case TOKEN_STAR:            type = "*";    break;
        case TOKEN_PLUS:            type = "+";    break;
        case TOKEN_LT:              type = "<";    break;
        case TOKEN_GT:              type = ">";    break;
        case TOKEN_LEQ:             type = "<=";   break;
        case TOKEN_GEQ:             type = ">=";   break;
        case TOKEN_CMP:             type = "<=>";  break;
        case TOKEN_STAR_EQ:         type = "*=";   break;
        case TOKEN_PLUS_EQ:         type = "+=";   break;
        case TOKEN_MINUS_EQ:        type = "-=";   break;
        case TOKEN_DIV_EQ:          type = "/=";   break;
        case TOKEN_AND_EQ:          type = "&=";   break;
        case TOKEN_OR_EQ:           type = "|=";   break;
        case TOKEN_XOR_EQ:          type = "^=";   break;
        case TOKEN_SHL_EQ:          type = "<<=";  break;
        case TOKEN_SHR_EQ:          type = ">>=";  break;
        case TOKEN_WTF:             type = "??";   break;
        case TOKEN_ARROW:           type = "->";   break;
        case TOKEN_FAT_ARROW:       type = "=>";   break;
        case TOKEN_SQUIGGLY_ARROW:  type = "~>";   break;

        case TOKEN_KEYWORD:
                type = (char *)keyword_show(t->keyword);
                break;
        case TOKEN_SPECIAL_STRING:
        case TOKEN_FUN_SPECIAL_STRING:
                type = "f-string";
                break;
        case TOKEN_NEWLINE:
                type = "\\n";
                break;
        case TOKEN_REGEX:
                type = "regex";
                break;
        case TOKEN_USER_OP:
                type = t->operator;
                break;
        }

#undef T

        int tlen;
        if (type == NULL) {
                char const *charset = "[](){}<>;.,?`~=!@#$%^&*/()-_~+|\"\\\n";

                if ((type = strchr(charset, t->type)) == NULL) {
                        tlen = 0;
                } else {
                        tlen = 1;
                }
        } else {
                tlen = strlen(type);
        }

        return vTn(
                "type",   STRING_NOGC(type, tlen),
                "start",  start,
                "end",    end
        );
}

static Value
make_tokens(Ty *ty, TokenVector const *ts)
{
        Array *a = vA();

        GC_STOP();

        for (int i = 0; i < ts->count; ++i) {
                if (ts->items[i].ctx != LEX_FAKE) {
                        vAp(a, make_token(ty, &ts->items[i]));
                }
        }

        GC_RESUME();

        return ARRAY(a);
}

BUILTIN_FUNCTION(ty_disassemble)
{
        ASSERT_ARGC("ty.disassemble()", 1);

        Value what = ARG(0);

        char *code;
        char const *end;
        char const *name;

        switch (what.type) {
        case VALUE_STRING:
                uvP(B, '\0');
                uvPn(B, what.string, what.bytes);
                uvP(B, '\0');

                name = "(eval)";
                code = compiler_compile_source(ty, B.items + 1, name);
                end = NULL;

                if (code == NULL) {
                        snprintf(buffer, sizeof buffer, "%s", compiler_error(ty));
                        zP("disassemble(): %s\n=============================================================", buffer);
                }

                break;
        case VALUE_GENERATOR:
                what = what.gen->f;
        case VALUE_FUNCTION:
                if (class_of(&what) != -1) {
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s.%s%s",
                                class_name(ty, class_of(&what)),
                                name_of(&what),
                                proto_of(&what)
                        );
                } else {
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s%s",
                                name_of(&what),
                                proto_of(&what)
                        );
                }

                name = buffer;
                code = code_of(&what);
                end = code + code_size_of(&what);

                break;
        default:
                zP("I don't know how to disassemble that yet :( %s", VSC(&what));
        }

        byte_vector text = {0};
        DumpProgram(ty, &text, name, code, end);

        Value result = vSs(text.items, text.count);

        free(text.items);

        return result;
}

BUILTIN_FUNCTION(eval)
{
        ASSERT_ARGC_2("ty.eval()", 1, 2);

        struct scope *scope = NULL;

        if (argc == 2) {
                scope = ARG(1).ptr;
        }

        if (ARG(0).type == VALUE_STRING) {
                B.count = 0;
                vec_push_unchecked(B, '\0');
                vec_push_n_unchecked(B, EVAL_PROLOGUE, countof(EVAL_PROLOGUE) - 1);
                vec_push_n_unchecked(B, ARG(0).string, ARG(0).bytes);
                vec_push_n_unchecked(B, EVAL_EPILOGUE, countof(EVAL_EPILOGUE));
                Arena old = amNg(1 << 26);
                Stmt **prog = parse(ty, B.items + 1, "(eval)");

                if (prog == NULL) {
                        char const *msg = parse_error(ty);
                        Value e = Err(ty, vSs(msg, strlen(msg)));
                        ReleaseArena(ty, old);
                        vmE(&e);
                }

                Expr *e = (Expr *)prog[0];

                if (!compiler_symbolize_expression(ty, e, scope))
E1:
                {
                        char const *msg = compiler_error(ty);
                        Value e = Err(ty, vSs(msg, strlen(msg)));
                        ReleaseArena(ty, old);
                        vmE(&e);
                }

                Value v = tyeval(ty, e);

                if (v.type == VALUE_NONE) {
                        goto E1;
                }

                ReleaseArena(ty, old);

                return v;
        } else {
                compiler_clear_location(ty);
                struct expression *e = TyToCExpr(ty, &ARG(0));
                if (e == NULL || !compiler_symbolize_expression(ty, e, scope))
E2:
                {
                        char const *msg = compiler_error(ty);
                        struct value e = Err(ty, vSs(msg, strlen(msg)));
                        vmE(&e);
                }

                Value v = tyeval(ty, e);

                if (v.type == VALUE_NONE) {
                        goto E2;
                }

                return v;
        }
}

BUILTIN_FUNCTION(ty_tokenize)
{
        ASSERT_ARGC("ty.tokenize()", 1);

        if (ARG(0).type != VALUE_STRING) {
                zP("ty.tokenize(): expected string but got: %s", VSC(&ARG(0)));
        }

        B.count = 0;
        vec_push_unchecked(B, '\0');
        vec_push_n_unchecked(B, ARG(0).string, ARG(0).bytes);
        vec_push_unchecked(B, '\0');

        Arena old = amNg(1 << 18);

        TokenVector tokens;
        if (!tokenize(ty, B.items + 1, &tokens)) {
                ReleaseArena(ty, old);
                return NIL;
        }

        ReleaseArena(ty, old);

        return make_tokens(ty, &tokens);
}

BUILTIN_FUNCTION(ty_parse)
{
        ASSERT_ARGC("ty.parse()", 1);

        if (ARG(0).type != VALUE_STRING) {
                zP("ty.parse(): expected string but got: %s", VSC(&ARG(0)));
        }

        B.count = 0;
        vec_push_unchecked(B, '\0');
        vec_push_n_unchecked(B, ARG(0).string, ARG(0).bytes);
        vec_push_unchecked(B, '\0');

        Arena old = amNg(1 << 22);

        struct statement **prog;
        Location stop;
        Value extra = NIL;
        TokenVector tokens = {0};

        Value *want_tokens = NAMED("tokens");

        char const *tokens_key = (want_tokens && value_truthy(ty, want_tokens)) ? "tokens" : NULL;
        Value vTokens = NIL;

        Value result;

        GC_STOP();

        jmp_buf cjb;
        jmp_buf *cjb_save;

        CompileState compiler_state = PushCompilerState(ty, "(eval)");

        if (setjmp(cjb) != 0) {
                char const *msg = compiler_error(ty);

                result = Err(
                        ty,
                        vTn(
                                "msg", vSs(msg, strlen(msg))
                        )
                );

                goto Return;
        }

        cjb_save = compiler_swap_jb(ty, &cjb);

        if (!parse_ex(ty, B.items + 1, "(eval)", &prog, &stop, &tokens)) {
                char const *msg = parse_error(ty);

                if (tokens_key) {
                        vTokens = make_tokens(ty, &tokens);
                }

                extra = vTn(
                        "where",    make_location(ty, &stop),
                        "msg",      vSs(msg, strlen(msg)),
                        tokens_key, vTokens
                );
        } else if (tokens_key) {
                vTokens = make_tokens(ty, &tokens);
                extra = vTn(
                        tokens_key, vTokens
                );
        }

        if (prog == NULL || prog[0] == NULL) {
                result = Err(ty, extra);
                goto Return;
        }

        if (prog[1] == NULL && prog[0]->type == STATEMENT_EXPRESSION) {
                Value v = CToTyExpr(ty, prog[0]->expression);
                if (v.type == VALUE_NONE) {
                        result = Err(ty, extra);
                } else {
                        result = Ok(ty, PAIR(v, extra));
                }
                goto Return;
        }

        if (prog[1] == NULL) {
                Value v = CToTyStmt(ty, prog[0]);
                if (v.type == VALUE_NONE) {
                        result = Err(ty, extra);
                } else {
                        result = Ok(ty, PAIR(v, extra));
                }
                goto Return;
        }

        Stmt *multi = amA0(sizeof *multi);
        multi->type = STATEMENT_MULTI;
        multi->arena = GetArenaAlloc(ty);

        for (int i = 0; prog[i] != NULL; ++i) {
                avP(multi->statements, prog[i]);
        }

        Value v = CToTyStmt(ty, multi);
        if (v.type == VALUE_NONE) {
                result = Err(ty, extra);
        } else {
                result = Ok(ty, PAIR(v, extra));
        }

Return:
        ReleaseArena(ty, old);
        GC_RESUME();

        PopCompilerState(ty, compiler_state);

        compiler_swap_jb(ty, cjb_save);

        return result;
}

BUILTIN_FUNCTION(ty_id)
{
        ASSERT_ARGC("ty.id()", 1);
        return INTEGER(ARG(0).src);
}

BUILTIN_FUNCTION(ty_copy_source)
{
        ASSERT_ARGC("ty.copySource()", 2);

        Value from = ARG(0);
        Value to = ARG(1);

        to.src = from.src;

        return to;
}

BUILTIN_FUNCTION(ty_get_source)
{
        ASSERT_ARGC("ty.getSource()", 1);

        Value expr = ARG(0);
        Expr *src = source_lookup(ty, expr.src);

        if (src == NULL && expr.type == VALUE_PTR) {
                src = (Expr const *)expr.ptr;
        }

        if (src == NULL || src->start.s == NULL || src->end.s == NULL) {
                return NIL;
        }

        GC_STOP();

        Value file = (src->file == NULL)
                   ? NIL
                   : vSsz(src->file);

        Value result = vTn(
                "start", make_location(ty, &src->start),
                "end",   make_location(ty, &src->end),
                "file",  file,
                "prog",  xSz(src->start.s - src->start.byte),
                "src",   xSs(src->start.s, src->end.s - src->start.s)
        );

        GC_RESUME();

        return result;
}

BUILTIN_FUNCTION(ty_strip_source)
{
        ASSERT_ARGC("ty.stripSource()", 1);

        Value e = ARG(0);
        e.src = 0;

        return e;
}

BUILTIN_FUNCTION(lex_state)
{
        ASSERT_ARGC("ty.lex.state()", 0);

        Value *sync = NAMED("noSync");
        LexState st;

        if (sync == NULL || !value_truthy(ty, sync)) {
                parse_sync_lex(ty);
        }

        lex_save(ty, &st);

        return vTn(
                "source",       xSs(st.start, st.end - st.start),
                "position",     make_location(ty, &st.loc),
                "context",      INTEGER(st.ctx),
                "keepComments", BOOLEAN(st.keep_comments),
                "keepNewline",  BOOLEAN(st.need_nl),
                "blankLine",    BOOLEAN(st.blank_line)
        );
}

BUILTIN_FUNCTION(lex_peek_char)
{
        ASSERT_ARGC("ty.lex.peekc()", 0);

        parse_sync_lex(ty);

        char b[128];
        int n = lex_peek_char(ty, b);

        if (n == 0) {
                return NIL;
        }

        return vSs(b, n);
}

BUILTIN_FUNCTION(lex_next_char)
{
        ASSERT_ARGC("ty.lex.getc()", 0);

        parse_sync_lex(ty);

        char b[128];

        if (!lex_next_char(ty, b)) {
                return NIL;
        }

        return vSsz(b);
}

BUILTIN_FUNCTION(token_peek)
{
        ASSERT_ARGC_2("ty.token.peek()", 0, 1);

        if (argc == 1 && ARG(0).type != VALUE_INTEGER) {
                zP("ty.token.peek(): expected integer but got: %s", VSC(&ARG(0)));
        }

        GC_STOP();

        Token t = parse_get_token(ty, argc == 0 ? 0 : ARG(0).integer);
        Value v = make_token(ty, &t);

        GC_RESUME();

        return v;
}

BUILTIN_FUNCTION(token_next)
{
        ASSERT_ARGC("ty.token.next()", 0);

        Value v = builtin_token_peek(ty, 0, NULL);

        parse_next(ty);

        return v;
}

BUILTIN_FUNCTION(parse_source)
{
        ASSERT_ARGC_2("ty.parse.source()", 0, 1);

        char const *s;
        size_t n;

        switch (ARG(0).type) {
        case VALUE_STRING:
                s = ARG(0).string;
                n = ARG(0).bytes;
                break;
        case VALUE_BLOB:
                s = (char const *)ARG(0).blob->items;
                n = ARG(0).blob->count;
                break;
        default:
                zP("ty.parse.source(): expected Blob or String but got: %s", VSC(&ARG(0)));
        }

        char *src = ((char *)mA(n + 2)) + 1;
        memcpy(src, s, n);
        src[-1] = '\0';
        src[n] = '\0';

        struct statement **p = parse(ty, src, NULL);

        return tyexpr(ty, p[0]->expression);
}


BUILTIN_FUNCTION(parse_expr)
{
        ASSERT_ARGC_2("ty.parse.expr()", 0, 1);

        int prec;

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("ty.parse.expr(): expected integer but got: %s", VSC(&ARG(0)));
                }
                prec = ARG(0).integer;
        } else {
                prec = 0;
        }

        struct value *resolve = NAMED("resolve");
        Value *raw = NAMED("raw");

        return parse_get_expr(ty, prec, resolve != NULL && value_truthy(ty, resolve), raw != NULL && value_truthy(ty, raw));
}

BUILTIN_FUNCTION(parse_stmt)
{
        ASSERT_ARGC_2("ty.parse.stmt()", 0, 1);

        int prec;

        struct value *raw = NAMED("raw");

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("ty.parse.stmt(): expected integer but got: %s", VSC(&ARG(0)));
                }
                prec = ARG(0).integer;
        } else {
                prec = -1;
        }

        return parse_get_stmt(ty, prec, raw != NULL && value_truthy(ty, raw));
}

BUILTIN_FUNCTION(parse_show)
{
        ASSERT_ARGC("ty.parse.show()", 1);

        Value expr = ARG(0);

        Expr const *src = (expr.type == VALUE_PTR)
                        ? expr.ptr
                        : source_lookup(ty, expr.src);

        if (src == NULL) {
                return NIL;
        }

        int n = src->end.s - src->start.s;

        return vSs(src->start.s, n);
}

BUILTIN_FUNCTION(parse_fail)
{
        ASSERT_ARGC("ty.parse.fail(ty)", 1);

        if (ARG(0).type != VALUE_STRING) {
                zP("ty.parse.fail(ty): expected string but got: %s", VSC(&ARG(0)));
        }

        parse_fail(ty, ARG(0).string, ARG(0).bytes);

        // Unreachable
}

BUILTIN_FUNCTION(ptr_typed)
{
        ASSERT_ARGC("ptr.typed()", 2);

        if (ARG(0).type != VALUE_PTR) {
                zP("ptr.typed(): expected pointer as first argument but got: %s", VSC(&ARG(0)));
        }

        if (ARG(1).type != VALUE_PTR) {
                zP("ptr.typed(): expected pointer as second argument but got: %s", VSC(&ARG(1)));
        }

        return TGCPTR(ARG(0).ptr, ARG(1).ptr, ARG(0).gcptr);
}

BUILTIN_FUNCTION(ptr_untyped)
{
        ASSERT_ARGC("ptr.untyped()", 1);

        struct value p = ARG(0);

        if (p.type != VALUE_PTR) {
                zP("ptr.untyped(): expected pointer as first argument but got: %s", VSC(&p));
        }

        return GCPTR(p.ptr, p.gcptr);
}

BUILTIN_FUNCTION(tdb_eval)
{
        ASSERT_ARGC("tdb.eval()", 1);

        if (!DEBUGGING) return NIL;

        ty = TDB->ty;

        B.count = 0;
        vec_push_unchecked(B, '\0');
        vec_push_n_unchecked(B, EVAL_PROLOGUE, countof(EVAL_PROLOGUE) - 1);
        vec_push_n_unchecked(B, ARG(0).string, ARG(0).bytes);
        vec_push_n_unchecked(B, EVAL_EPILOGUE, countof(EVAL_EPILOGUE));

        Arena old = amNg(1 << 20);

        Stmt **prog = parse(ty, B.items + 1, "(eval)");
        if (prog == NULL) {
                char const *msg = parse_error(ty);
                Value error = Err(ty, vSsz(msg));
                ReleaseArena(ty, old);
                return error;
        }

        Expr *e = (Expr *)prog[0];

        Expr const *context = compiler_find_expr(ty, TDB->host->ip);
        Scope *scope = (context == NULL) ? NULL : context->xscope;

// =====================================================================
        Ty save = *TDB->host;

        Value v;
        if (
                compiler_symbolize_expression(ty, e, scope)
             && (v = tyeval(TDB->host, e)).type != VALUE_NONE
        ) {
                ReleaseArena(ty, old);
                *TDB->host = save;
                return Ok(ty, v);
        }

        *TDB->host = save;
// =====================================================================

        char const *msg = compiler_error(ty);
        Value error = Err(ty, vSsz(msg));

        ReleaseArena(ty, old);

        return error;
}

BUILTIN_FUNCTION(tdb_list)
{
        ASSERT_ARGC("tdb.list()", 0);
        TDB_MUST_BE(STOPPED);

        tdb_list(TDB->host);

        return NIL;
}

BUILTIN_FUNCTION(tdb_stack)
{
        Array *stack = vA();
        *stack = *(Array *)&TDB->host->stack;
        return ARRAY(stack);
}


BUILTIN_FUNCTION(tdb_span)
{
        ASSERT_ARGC_2("tdb.list()", 0, 1);

        // TODO
        if (argc == 1) {
                Expr const *expr = ARG(0).ptr;
                return NIL;
        }

        ExprLocation *eloc = compiler_find_expr_x(ty, TDB->host->ip, false);
        if (eloc == NULL) {
                return NIL;
        }

        return PAIR(
                PTR((void *)eloc->p_start),
                PTR((void *)eloc->p_end)
        );
}

BUILTIN_FUNCTION(tdb_over)
{
        ASSERT_ARGC("tdb.over()", 0);
        TDB_MUST_BE(STOPPED);
        return BOOLEAN(tdb_step_over(TDB->host));
}

BUILTIN_FUNCTION(tdb_into)
{
        ASSERT_ARGC("tdb.into()", 0);
        TDB_MUST_BE(STOPPED);
        return BOOLEAN(tdb_step_into(TDB->host));
}

BUILTIN_FUNCTION(tdb_step)
{
        ASSERT_ARGC("tdb.step()", 0);
        TDB_MUST_BE(STOPPED);
        return BOOLEAN(tdb_step_line(TDB->host));
}

BUILTIN_FUNCTION(tdb_backtrace)
{
        ASSERT_ARGC("tdb.backtrace()", 0);
        TDB_MUST_BE(STOPPED);

        tdb_backtrace(TDB->host);

        return NIL;
}

BUILTIN_FUNCTION(tdb_ip)
{
        ASSERT_ARGC_2("tdb.ip()", 0, 1);
        TDB_MUST_NOT_BE(OFF);

        return (argc == 0)
             ? PTR(TDB->host->ip)
             : PTR(code_of(&ARG(0)));
}

BUILTIN_FUNCTION(tdb_breakpoint)
{
        ASSERT_ARGC_2("tdb.breakpoint()", 0, 1);

        char *ip;
        Value arg;

        if (argc == 0) {
                ip = TDB->host->ip;
        } else switch ((arg = ARG(0)).type) {
        case VALUE_PTR:       ip = arg.ptr;             break;
        case VALUE_FUNCTION:  ip = code_of(&arg);       break;
        case VALUE_METHOD:    ip = code_of(arg.method); break;

        default:
                zP(
                        "tdb.breakpoint(): attempt to set breakpoint "
                        "on invalid type: %s",
                        VSC(&arg)
                );
        }

        tdb_set_break(ty, ip);

        return BOOLEAN(true);
}

BUILTIN_FUNCTION(tdb_locals)
{
        ASSERT_ARGC("tdb.locals()", 0);
        TDB_MUST_NOT_BE(OFF);
        return tdb_locals(ty);
}

BUILTIN_FUNCTION(tdb_context)
{
        ASSERT_ARGC_2("tdb.context()", 0, 1);
        TDB_MUST_NOT_BE(OFF);

        char *ip = (argc == 0) ? TDB->host->ip : ARG(0).ptr;
        Expr *context = (Expr *)compiler_find_expr(ty, ip);

        Value expr = (context == NULL) ? NIL : PTR(context);

        Value prog = (context == NULL)          ? NIL
                   : (context->start.s == NULL) ? NIL
                   : xSz(context->start.s - context->start.byte);

        Value file = (context == NULL)       ? NIL
                   : (context->file == NULL) ? NIL
                   : xSz(context->file);

        return (context == NULL) ? NIL : vTn(
                "prog",  prog,
                "file",  file,
                "expr",  expr
        );
}

BUILTIN_FUNCTION(tdb_state)
{
        ASSERT_ARGC("tdb.state()", 0);
        TDB_MUST_NOT_BE(OFF);

        Expr *context = (Expr *)compiler_find_expr(ty, TDB->host->ip);

        Value ip = PTR(TDB->host->ip);

        Value expr = (context == NULL) ? NIL : PTR(context);

        Value prog = (context == NULL)          ? NIL
                   : (context->start.s == NULL) ? NIL
                   : xSz(context->start.s - context->start.byte);

        Value file = (context == NULL)       ? NIL
                   : (context->file == NULL) ? NIL
                   : xSz(context->file);

        Value f = (TDB->host->frames.count > 0)
                ? vvL(TDB->host->frames)->f
                : NIL;

        Value fp = (TDB->host->frames.count > 0)
                 ? INTEGER(vvL(TDB->host->frames)->fp)
                 : NIL;

        return vTn(
                "ip",    ip,
                "prog",  prog,
                "file",  file,
                "expr",  expr,
                "func",  f,
                "fp",    fp,
                "sp",    INTEGER(TDB->host->stack.count)
        );
}

/* vim: set sw=8 sts=8 expandtab: */
