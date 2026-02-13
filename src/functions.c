#include "ast.h"
#include "ty.h"
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

#include <signal.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <utf8proc.h>
#include <sha1.h>
#include <sha256.h>
#include <sha512.h>
#include <md5.h>

#include "tthread.h"
#include "polyfill_time.h"
#include "polyfill_unistd.h"
#include "polyfill_stdatomic.h"

#define NOT_ON_WINDOWS(name) zP("%s is not implemented in Windows builds of Ty", #name);

#ifdef __linux__
#include <sys/epoll.h>
#include <sys/sendfile.h>
#include <pty.h>
#endif

#ifdef __APPLE__
#include <sys/sysctl.h>
#include <util.h>
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
#include <dirent.h>
#include <netdb.h>
#include <netdb.h>
#include <netinet/ip.h>
#include <poll.h>
#include <pthread.h>
#include <spawn.h>
#include <sys/file.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
extern char **environ;
#endif

#include "functions.h"
#include "tags.h"
#include "value.h"
#include "parse.h"
#include "vm.h"
#include "log.h"
#include "xd.h"
#include "token.h"
#include "json.h"
#include "dict.h"
#include "object.h"
#include "class.h"
#include "compiler.h"
#include "types.h"

#ifdef __APPLE__
#define fputc_unlocked putc_unlocked
#define fgetc_unlocked getc_unlocked
#define fwrite_unlocked fwrite
#define fread_unlocked fread
#define fputs_unlocked fputs
#define fflush_unlocked fflush
#endif

static _Thread_local vec(char) B;
static _Atomic(u64) tid = 0;

u64 NextThreadId() { return ++tid; }

void
TyFunctionsCleanup(void)
{
        xvF(B);
}

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


#define ASSERT_ARGC_2(func, ac1, ac2) \
        if (argc != (ac1) && argc != (ac2)) { \
                zP(func " expects " #ac1 " or " #ac2 " argument(s) but got %d", argc); \
        }

#define ASSERT_ARGC_3(func, ac1, ac2, ac3) \
        if (argc != (ac1) && argc != (ac2) && argc != (ac3)) { \
                zP(func " expects " #ac1 ", " #ac2 ", or " #ac3 " argument(s) but got %d", argc); \
        }

#define EVAL_PROLOGUE "(fn () {\n"
#define EVAL_EPILOGUE "\n})()"

static struct timespec
tuple_timespec(Ty *ty, char const *func, Value const *v);

inline static void
IntoSigSet(Ty *ty, char const *ctx, Value const *v, sigset_t *set)
{
        sigemptyset(set);

        switch (v->type) {
        case VALUE_ARRAY:
                for (int i = 0; i < vN(*v->array); ++i) {
                        Value sig = v__(*v->array, i);
                        if (sig.type != VALUE_INTEGER) {
                                zP("%s: bad signal set: %s", ctx, VSC(v));
                        }
                        sigaddset(set, sig.z);
                }
                break;

        case VALUE_DICT:
                dfor(v->dict, {
                        if (key->type != VALUE_INTEGER) {
                                zP("%s: bad signal set: %s", ctx, VSC(v));
                        }
                        if (value_truthy(ty, val)) {
                                sigaddset(set, key->z);
                        }
                });
                break;

        case VALUE_PTR:
                *set = *(sigset_t *)v->ptr;
                break;

        case VALUE_NIL:
                break;

        case VALUE_OBJECT:
        {
                Value *f = class_lookup_method_i(ty, v->class, NAMES.ptr);
                if (f != NULL) {
                        Value addr = vm_call_method(ty, v, f, 0);
                        if (addr.type == VALUE_PTR) {
                                *set = *(sigset_t *)addr.ptr;
                                break;
                        }
                }
                // fallthrough
        }

        default:
                zP("%s: bad signal set: %s", ctx, VSC(v));
        }
}

inline static Value
NewSigSetFrom(Ty *ty, sigset_t const *set)
{
        sigset_t *new = mAo(sizeof *new, GC_ANY);
        *new = *set;
        return GCPTR(new, new);
}

inline static i64
TryIntoTime(Ty *ty, char const *ctx, Value const *t, i64 factor)
{
        struct timespec spec;

        switch (t->type) {
        case VALUE_REAL:
                return (factor * t->real);

        case VALUE_INTEGER:
                return t->z;

        case VALUE_TUPLE:
                spec = tuple_timespec(ty, ctx, t);
                return (factor * (TY_1e9*spec.tv_sec + spec.tv_nsec)) / TY_1e9;

        case VALUE_NIL:
                return -1;

        default:
                zP("%s: invalid timespec: %s", ctx, VSC(t));
        }
}

#define NSEC_ARG(i) TryIntoTime(ty, _name__, &ARG(i), 1000000000)
#define USEC_ARG(i) TryIntoTime(ty, _name__, &ARG(i), 1000000)
#define MSEC_ARG(i) TryIntoTime(ty, _name__, &ARG(i), 1000)

inline static void
GetCurrentTimespec(struct timespec* ts)
{
#ifdef _WIN32
        FILETIME ft;
        GetSystemTimeAsFileTime(&ft);
        u64 totalUs = (((u64)ft.dwHighDateTime << 32) + ft.dwLowDateTime - 0x19DB1DED53E8000ULL) / 10ULL;
        ts->tv_sec = totalUs / 1000000ULL;
        ts->tv_nsec = (totalUs % 1000000ULL) * 1000ULL;
#else
        clock_gettime(CLOCK_REALTIME, ts);
#endif
}

static intmax_t
doprint(Ty *ty, int argc, Value *kwargs, FILE *f)
{
        Value *sep = NAMED("sep");
        if (sep != NULL && sep->type == VALUE_NIL) {
                sep = NULL;
        }
        if (sep != NULL && sep->type != VALUE_STRING) {
                zP(
                        "print(): %s%ssep%s must be a string",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        Value *end = NAMED("end");
        if (end != NULL && end->type == VALUE_NIL) {
                end = NULL;
        }
        if (end != NULL && end->type != VALUE_STRING) {
                zP(
                        "print(): %s%send%s must be a string",
                        TERM(93),
                        TERM(1),
                        TERM(0)
                );
        }

        Value *flush = NAMED("flush");
        bool do_flush = (flush != NULL) && value_truthy(ty, flush);

        lGv(true);
        flockfile(f);

        imax written = 0;

        u32 show_flags = !isatty(fileno_unlocked(f))
                       ? TY_SHOW_NOCOLOR
                       : 0;

        for (int i = 0; i < argc; ++i) {
                Value *v = &ARG(i);

                if (i > 0) {
                        if (sep != NULL) {
                                if (fwrite_unlocked(ss(*sep), 1, sN(*sep), f) < sN(*sep)) {
                                        funlockfile(f);
                                        lTk();
                                        return -1;
                                }
                                written += sN(*sep);
                        } else {
                                if (fputs_unlocked(", ", f) == EOF) {
                                        funlockfile(f);
                                        lTk();
                                        return -1;
                                }
                                written += 2;
                        }
                }

                char const  *s;
                i64          n;
                bool need_free = false;

                switch (v->type) {
                case VALUE_STRING:
                        s = (char const *)ss(*v);
                        n = sN(*v);
                        break;

                case VALUE_BLOB:
                        s = (char const *)vv(*v->blob);
                        n = vN(*v->blob);
                        break;

                case VALUE_PTR:
                        s = v->ptr;
                        n = strlen(v->ptr);
                        break;

                default:
                        lTk();
                        s = VSC(&ARG(i), show_flags);
                        lGv(true);
                        n = strlen(s);
                        need_free = true;
                        break;
                }

                if (fwrite_unlocked(s, 1, n, f) < n) {
                        if (need_free) {
                                xmF((char *)s);
                        }
                        funlockfile(f);
                        lTk();
                        return -1;
                }

                if (need_free) {
                        xmF((char *)s);
                }

                written += n;
        }


        if (end != NULL) {
                if (fwrite_unlocked(ss(*end), 1, sN(*end), f) < sN(*end)) {
                        funlockfile(f);
                        lTk();
                        return -1;
                }
                written += sN(*end);
        } else {
                if (fputc_unlocked('\n', f) == EOF) {
                        funlockfile(f);
                        lTk();
                        return -1;
                } else {
                        written += 1;
                }
        }

        if (do_flush) {
                fflush_unlocked(f);
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

        char p[PATH_MAX + 1];
        int fd;
        bool need_close = false;

        if (argc == 0) {
                fd = 0;
        } else if (ARG(0).type == VALUE_STRING) {
                Value v = ARG(0);

                if (sN(v) >= sizeof p)
                        return NIL;

                memcpy(p, ss(v), sN(v));
                p[sN(v)] = '\0';

#ifdef _WIN32
                fd = _open(p, _O_RDONLY);
#else
                fd = open(p, O_RDONLY);
#endif
                if (fd < 0)
                        return NIL;

                need_close = true;
        } else if (ARG(0).type == VALUE_INTEGER) {
                fd = ARG(0).z;
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

                void *tmp = TY_TMP();


                v0(B);
                lGv(true);
                while (!feof(f) && (r = fread(tmp, 1, TY_TMP_N, f)) > 0) {
                        xvPn(B, tmp, r);
                }
                lTk();

                Value str = vSs(vv(B), vN(B));

                if (need_close) {
                        fclose(f);
                }

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
        case VALUE_STRING:  return PAIR(PTR((void *)ss(v)), INTEGER(sN(v)));
        default:            return v;
        }
}

BUILTIN_FUNCTION(die)
{
        char *_name__ = "die()";

        CHECK_ARGC(1);
        Value message = ARGx(0, VALUE_STRING);

        zP("%.*s", (int)sN(message), ss(message));
}

BUILTIN_FUNCTION(__debug)
{
        char *_name__ = "__debug()";
        CHECK_ARGC(1);
        return INTEGER(EnableLogging += INT_ARG(0));
}

BUILTIN_FUNCTION(read)
{
        ASSERT_ARGC("readLine()", 0);

        int c;

        v0(B);
        lGv(true);
        while (c = getchar(), c != EOF && c != '\n') {
                xvP(B, c);
        }

        lTk();

        if (vN(B) == 0 && c != '\n') {
                return NIL;
        }

        return vSs(vv(B), vN(B));
}

inline static Value
xpick(Array const *xs, u64 z)
{
        usize n = vN(*xs);
        if (n == 0) {
                return NIL;
        } else {
                return v__(*xs, z % n);
        }
}

BUILTIN_FUNCTION(rand)
{
        ASSERT_ARGC("rand()", 0, 1, 2);

        i64 low;
        i64 high;

        u64 z = xoshiro256ss(ty);

        switch (argc) {
        case 0:
                return REAL(TyRandom(ty));

        case 1:
                if (ARG_T(0) == VALUE_ARRAY) {
                        return xpick(ARG(0).array, z);
                }
                low  = 0;
                high = INT_ARG(0);
                break;

        case 2:
                low  = INT_ARG(0);
                high = INT_ARG(1);
                break;
        }

        return INTEGER((z % (high - low)) + low);

}

BUILTIN_FUNCTION(abs)
{
        ASSERT_ARGC("abs()", 1);

        Value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return INTEGER(llabs(x.z));
        case VALUE_REAL:    return REAL(fabs(x.real));
        default:
                zP("the argument to abs() must be a number");
        }
}

BUILTIN_FUNCTION(gcd)
{
        ASSERT_ARGC("gcd()", 2);

        Value t = ARG(0);
        Value u = ARG(1);

        if (t.type == VALUE_REAL) t = INTEGER(t.real);
        if (u.type == VALUE_REAL) u = INTEGER(u.real);

        if (t.type != VALUE_INTEGER || u.type != VALUE_INTEGER) {
                zP("both arguments to gcd() must be integers");
        }

        intmax_t a = t.z;
        intmax_t b = u.z;

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

        Value t = ARG(0);
        Value u = ARG(1);

        if (t.type == VALUE_REAL) t = INTEGER(t.real);
        if (u.type == VALUE_REAL) u = INTEGER(u.real);

        if (t.type != VALUE_INTEGER || u.type != VALUE_INTEGER) {
                zP("both arguments to lcm() must be integers");
        }

        intmax_t a = t.z;
        intmax_t b = u.z;

        while (b != 0) {
                intmax_t t = b;
                b = a % b;
                a = t;
        }

        return INTEGER(llabs(t.z * u.z) / a);
}

BUILTIN_FUNCTION(round)
{
        ASSERT_ARGC("round()", 1);

        Value x = ARG(0);

        switch (x.type) {
        case VALUE_INTEGER: return REAL(x.z);
        case VALUE_REAL:    return REAL(round(x.real));
        default:
                zP("the argument to round() must be a number");
        }
}

BUILTIN_FUNCTION(iround)
{
        ASSERT_ARGC("iround()", 1);

        Value x = ARG(0);

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

        Value x = ARG(0);

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

        Value x = ARG(0);

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

        i32 rune = INT_ARG(0);

        if (!utf8proc_codepoint_valid(rune)) {
                return NIL;
        }

        u8 b[4];
        int n = utf8proc_encode_char(rune, b);

        return vSs(b, n);
}

BUILTIN_FUNCTION(ord)
{
        ASSERT_ARGC("ord()", 1);

        Value c = ARG(0);

        if (c.type != VALUE_STRING)
                zP("the argument to ord() must be a string");

        i32 rune;
        i32 n = utf8proc_iterate(ss(c), sN(c), &rune);

        if (n <= 0) {
                return NIL;
        }

        return INTEGER(rune);
}

BUILTIN_FUNCTION(hash)
{
        ASSERT_ARGC("hash()", 1);
        return INTEGER(value_hash(ty, &ARG(0)));
}

BUILTIN_FUNCTION(float)
{
        ASSERT_ARGC("float()", 1);

        Value v = ARG(0);

        switch (v.type) {
        case VALUE_NIL:     return NIL;
        case VALUE_INTEGER: return REAL((double)v.z);
        case VALUE_REAL:    return v;
        case VALUE_STRING:;
                char buf[128];
                char *end;
                unsigned n = min(sN(v), 127);

                memcpy(buf, ss(v), n);
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
                zP("nan?() expects a float but got: %s", SHOW(&ARG(0)));
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
        ASSERT_ARGC("int()", 0, 1, 2);

        Value v = INTEGER(0), a, s, b;
        int base;

        char *tmp = TY_TMP();
        char const *string = tmp;

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

        case VALUE_INTEGER:                                         return a;
        case VALUE_REAL:    v.z = a.real;                           return v;
        case VALUE_BOOLEAN: v.z = a.boolean;                        return v;
        case VALUE_ARRAY:   v.z = a.array->count;                   return v;
        case VALUE_DICT:    v.z = a.dict->count;                    return v;
        case VALUE_BLOB:    v.z = a.blob->count;                    return v;
        case VALUE_PTR:     return INTEGER((uintptr_t)a.ptr);

        case VALUE_STRING:
                base = 0;
                if (sN(a) >= TY_TMP_N) {
                        goto TooBig;
                }
                memcpy(tmp, ss(a), sN(a));
                tmp[sN(a)] = '\0';
                goto String;
        }

CustomBase:

        s = ARGx(0, VALUE_STRING);
        base = INT_ARG(1);

        if (base < 0 || base == 1 || base > 36) {
                bP("invalid base(): expected 0 or 2..36, but got %"PRIiMAX, b.z);
        }

        if (sN(s) >= TY_TMP_N) {
                goto TooBig;
        }

        memcpy(tmp, ss(s), sN(s));
        tmp[sN(s)] = '\0';

String:
        /*
         * Handle 0b and 0o manually.
         */
        if (base == 0 && string[0] == '0' && string[1] == 'b') {
                base = 2;
                string += 2;
        }
        if (base == 0 && string[0] == '0' && string[1] == 'o') {
                base = 8;
                string += 2;
        }

        errno = 0;

        char *end;
        intmax_t n = strtoimax(string, &end, base);

        if (errno != 0 || *end != '\0' || end == string) {
                return NIL;
        }

        return INTEGER(n);

TooBig:
        errno = ERANGE;
        return NIL;
}

BUILTIN_FUNCTION(show)
{
        ASSERT_ARGC("show()", 1);

        Value arg = ARG(0);
        Value *color = NAMED("color");

        bool use_color = (color == NULL) ? isatty(1) : value_truthy(ty, color);

        return use_color ? value_vshow_color(ty, &arg, TY_SHOW_REPR)
                         : value_vshow(ty, &arg, TY_SHOW_REPR);
}

BUILTIN_FUNCTION(str)
{
        ASSERT_ARGC("str()", 0, 1);

        if (argc == 0) {
                return STRING_EMPTY;
        }

        Value arg = ARG(0);

        return (arg.type == VALUE_STRING)
             ? arg
             : value_vshow(ty, &arg, 0);
}

inline static bool
isflag(int c)
{
        return (c == '0')
            || (c == '-')
            || (c == '+')
            || (c == ' ')
            || (c == '#')
            || (c == '\'');
}

struct fspec {
        bool alt;
        bool blank;
        bool sep;
        bool sign;
        bool zero;
        i8 justify;
        char xsep;
        i32 fill;
        char prec[64];
        char width[64];
};

inline static int
getfmt(char const **s, char const *end, struct fspec *out)
{
        int w = 0;
        int p = 0;

        out->alt     = false;
        out->blank   = false;
        out->justify = 1;
        out->sep     = false;
        out->sign    = false;
        out->fill    = 0;
        out->xsep    = '\0';

        i32 rune;
        int bytes;

        for (;;) {
                if (out->fill == 0) {
                        bytes = utf8proc_iterate((u8 const *)*s, end - *s, &rune);

                        if (bytes <= 0) {
                                bytes = 1;
                                rune = **s;
                        }

                        if (*s + bytes < end && strchr("<^>", (*s)[bytes]) != NULL) {
                                out->fill = rune;
                                *s += bytes;
                                continue;
                        }
                }

                switch (**s) {
                case '+':  out->sign    = true; break;
                case '#':  out->alt     = true; break;
                case '\'': out->sep     = true; break;
                case ' ':  out->blank   = true; break;
                case '0':  out->fill    = '0';  break;
                case '-':  out->justify = -1;   break;
                case '<':  out->justify = -1;   break;
                case '^':  out->justify =  0;   break;
                case '>':  out->justify =  1;   break;
                default: goto FlagsComplete;
                }

                *s += 1;
        }

FlagsComplete:
        if (out->fill == 0) {
                out->fill = ' ';
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
        case VALUE_INTEGER: return v->z;
        case VALUE_REAL:    return v->real;
        case VALUE_BOOLEAN: return v->boolean;
        default: BadFmt(ty, spec, n, v);
        }
}

inline static double
float_from(Ty *ty, Value const *v, char const *spec, int n)
{
        switch (v->type) {
        case VALUE_INTEGER: return v->z;
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

        char const *fmt = (char const *)ss(ARG(0));
        size_t n = sN(ARG(0));
        int ai = 0;

        struct fspec spec;

        int len;

        vec(char) cs = {0};
        vec(char) sb = {0};

        char *tmp = TY_TMP();

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

                                snprintf(spec.width, sizeof spec.width, "%"PRIiMAX, ARG(ai).z);
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

                                snprintf(spec.prec, sizeof spec.prec, "%"PRIiMAX, ARG(ai).z);
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

                        int wlen;
                        if (spec.fill == '0' && spec.justify != 0) {
                                scratch[si++] = '0';
                                if (spec.justify == -1) {
                                        scratch[si++] = '-';
                                }
                                wlen = strlen(spec.width);
                        } else {
                                wlen = 0;
                        }

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
                                        tmp,
                                        TY_TMP_N,
                                        scratch,
                                        int_from(ty, &arg, start, nspec)
                                );

                                if (spec.xsep != '\0') {
                                        AddThousandsSep(&tmp[spec.blank], spec.xsep);
                                }

                                break;
                        case 'b':
                                scratch[si++] = 's';
                                scratch[si] = '\0';

                                utobsx(b, (uintmax_t)int_from(ty, &arg, start, nspec));

                                snprintf(
                                        tmp,
                                        TY_TMP_N,
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
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                snprintf(
                                        tmp,
                                        TY_TMP_N,
                                        scratch,
                                        float_from(ty, &arg, start, nspec)
                                );

                                if (spec.xsep != '\0') {
                                        AddThousandsSep(&tmp[spec.blank], spec.xsep);
                                }

                                break;
                        case 'q':
                                scratch[si++] = 'l';
                                scratch[si++] = 'f';
                                scratch[si++] = '%';
                                scratch[si++] = '%';
                                scratch[si] = '\0';

                                len = snprintf(
                                        tmp,
                                        TY_TMP_N,
                                        scratch,
                                        100.0 * float_from(ty, &arg, start, nspec)
                                );

                                while (
                                        (tmp[0] == '0' && isdigit(tmp[1]))
                                     || (tmp[0] == ' ' && tmp[spec.blank] == ' ')
                                ) {
                                        memmove(tmp, tmp + 1, len);
                                        len -= 1;
                                }

                                for (int i = len - 1; tmp[i - 1] == ' '; --i) {
                                        SWAP(char, tmp[i], tmp[i - 1]);
                                }

                                if (tmp[len - 1] == ' ') {
                                        tmp[--len] = '\0';
                                }

                                break;
                        case 's':
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                sb.count = 0;

                                switch (arg.type) {
                                case VALUE_STRING:
                                        xvPn(sb, ss(arg), sN(arg));
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
                                        tmp,
                                        TY_TMP_N,
                                        scratch,
                                        p
                                );

                                break;
                        case 'p':
                                scratch[si++] = t;
                                scratch[si] = '\0';

                                switch (arg.type) {
                                case VALUE_STRING:   p = ss(arg); break;
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
                                        tmp,
                                        TY_TMP_N,
                                        scratch,
                                        p
                                );

                                break;
                        default:
                                goto BadFormatSpecifier;
                        }

                        if (*spec.width) {
                                int goal = atoi(spec.width);
                                int curr = term_width(tmp, -1);

                                u8 fill[8];
                                int sz = utf8proc_encode_char(spec.fill, fill);

                                if (sz <= 0) {
                                        fill[0] = (u8)spec.fill;
                                        sz = 1;
                                }

                                int pad = max(0, goal - curr);
                                int odd;

                                switch (spec.justify) {
                                case 1:
                                        for (int i = 0; i < pad; ++i) {
                                                xvPn(cs, fill, sz);
                                        }
                                        xvPn(cs, tmp, strlen(tmp));
                                        break;
                                case 0:
                                        odd = pad & 1;
                                        pad /= 2;
                                        for (int i = 0; i < pad; ++i) {
                                                xvPn(cs, fill, sz);
                                        }
                                        xvPn(cs, tmp, strlen(tmp));
                                        for (int i = 0; i < pad + odd; ++i) {
                                                xvPn(cs, fill, sz);
                                        }
                                        break;
                                case -1:
                                        xvPn(cs, tmp, strlen(tmp));
                                        for (int i = 0; i < pad; ++i) {
                                                xvPn(cs, fill, sz);
                                        }
                                        break;
                                }
                        } else {
                                xvPn(cs, tmp, strlen(tmp));
                        }
                } else {
                        xvP(cs, fmt[i]);
                }
        }

        Value s = vSs(vv(cs), vN(cs));

        xvF(cs);
        xvF(sb);

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
        Dict *d = (kwargs != NULL && !IsNil(*kwargs)) ? kwargs->dict : NULL;

        if (d != NULL) {
                named += d->count;
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

        int n = argc;

        if (d != NULL) dfor(d, {
                tuple.items[n] = *val;
                tuple.ids[n] = intern(&xD.members, TY_TMP_C_STR(*key))->id;
                n += 1;
        });

        return tuple;
}

BUILTIN_FUNCTION(regex)
{
        char const *_name__ = "regex()";

        CHECK_ARGC(1, 2);

        Value pattern = ARGx(0, VALUE_STRING, VALUE_REGEX);

        if (pattern.type == VALUE_REGEX) {
                return pattern;
        }

        u32 options = 0;
        bool detailed = false;

        if (argc == 2) {
                Value flags = ARGx(1, VALUE_STRING);
                for (int i = 0; i < sN(flags); ++i) {
                        switch (ss(flags)[i]) {
                        case 'i': options |= PCRE2_CASELESS;  break;
                        case 'u': options |= PCRE2_UTF;       break;
                        case 'm': options |= PCRE2_MULTILINE; break;
                        case 'x': options |= PCRE2_EXTENDED;  break;
                        case 'v': detailed = true;            break;
                        }
                }
        }


        int err;
        usize off;

        pcre2_code *re = pcre2_compile(
                (PCRE2_SPTR)ss(pattern),
                sN(pattern),
                options,
                &err,
                &off,
                NULL
        );

        if (re == NULL) {
                return NIL;
        }

        err = pcre2_jit_compile(re, PCRE2_JIT_COMPLETE);
        if (err < 0) {
                pcre2_code_free(re);
                return NIL;
        }

        Regex *r = mAo(sizeof *r, GC_REGEX);
        r->pcre2 = re;
        r->pattern = TY_C_STR(pattern);
        r->detailed = detailed;
        r->gc = true;

        return REGEX(r);
}

BUILTIN_FUNCTION(min)
{
        if (argc < 2)
                zP("min() expects 2 or more arguments, but got %d", argc);

        Value min, v;
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

        Value max, v;
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

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the argument to math.exp() must be a float");

        return REAL(exp(x.real));
}

BUILTIN_FUNCTION(log)
{
        ASSERT_ARGC("math.log()", 1);

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the argument to math.log() must be a float");

        return REAL(log(x.real));
}

BUILTIN_FUNCTION(log2)
{
        ASSERT_ARGC("math.log2()", 1);

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the argument to math.log2() must be a float");

        return REAL(log2(x.real));
}

BUILTIN_FUNCTION(log10)
{
        ASSERT_ARGC("math.log10()", 1);

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the argument to math.log10() must be a float");

        return REAL(log10(x.real));
}

BUILTIN_FUNCTION(pow)
{
        ASSERT_ARGC("math.pow()", 2);

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the first argument to math.pow() must be a float");

        Value y = ARG(1);
        if (y.type == VALUE_INTEGER)
                y = REAL(y.z);
        if (y.type != VALUE_REAL)
                zP("the second argument to math.pow() must be a float");

        return REAL(pow(x.real, y.real));
}

BUILTIN_FUNCTION(atan2)
{
        ASSERT_ARGC("math.atan2()", 2);

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the first argument to math.atan2() must be a float");

        Value y = ARG(1);
        if (y.type == VALUE_INTEGER)
                y = REAL(y.z);
        if (y.type != VALUE_REAL)
                zP("the second argument to math.atan2() must be a float");

        return REAL(atan2(x.real, y.real));
}

#define MATH_WRAP(func)                                 \
        Value                                    \
        builtin_ ## func (Ty *ty, int argc, Value *kwargs)           \
        {                                               \
                ASSERT_ARGC("math." #func "()", 1);    \
                                                        \
                Value x = ARG(0);        \
                if (x.type == VALUE_INTEGER)            \
                        x = REAL(x.z);            \
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

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the argument to math.sqrt() must be a float");

        return REAL(sqrt(x.real));
}

BUILTIN_FUNCTION(cbrt)
{
        ASSERT_ARGC("math.cbrt()", 1);

        Value x = ARG(0);
        if (x.type == VALUE_INTEGER)
                x = REAL(x.z);
        if (x.type != VALUE_REAL)
                zP("the argument to math.cbrt() must be a float");

        return REAL(cbrt(x.real));
}

BUILTIN_FUNCTION(bit_and)
{
        ASSERT_ARGC("bit.and()", 2);

        Value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.and() must be an integer");

        Value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.and() must be an integer");

        return INTEGER((uintmax_t)a.z & (uintmax_t)b.z);
}

BUILTIN_FUNCTION(bit_or)
{
        ASSERT_ARGC("bit.or()", 2);

        Value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.or() must be an integer");

        Value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.or() must be an integer");

        return INTEGER((uintmax_t)a.z | (uintmax_t)b.z);
}

BUILTIN_FUNCTION(bit_xor)
{
        ASSERT_ARGC("bit.xor()", 2);

        Value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.xor() must be an integer");

        Value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.xor() must be an integer");

        return INTEGER((uintmax_t)a.z ^ (uintmax_t)b.z);
}

BUILTIN_FUNCTION(bit_shift_left)
{
        ASSERT_ARGC("bit.shiftLeft()", 2);

        Value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.shiftLeft() must be an integer");

        Value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.shiftLeft() must be an integer");

        return INTEGER((uintmax_t)a.z << (uintmax_t)b.z);
}

BUILTIN_FUNCTION(bit_shift_right)
{
        ASSERT_ARGC("bit.shiftRight()", 2);

        Value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.shiftRight() must be an integer");

        Value b = ARG(1);
        if (b.type != VALUE_INTEGER)
                zP("the second argument to bit.shiftRight() must be an integer");

        return INTEGER((uintmax_t)a.z >> (uintmax_t)b.z);
}

BUILTIN_FUNCTION(bit_complement)
{
        ASSERT_ARGC("bit.complement()", 1);

        Value a = ARG(0);
        if (a.type != VALUE_INTEGER)
                zP("the first argument to bit.complement() must be an integer");

        return INTEGER(~(uintmax_t)a.z);
}

BUILTIN_FUNCTION(setenv)
{
        ASSERT_ARGC("setenv()", 2);

        char *key = TY_TMP_C_STR_A(ARGx(0, VALUE_STRING, VALUE_BLOB));
        char *val = TY_TMP_C_STR_B(ARGx(1, VALUE_STRING, VALUE_BLOB));

#ifdef _WIN32
        SetEnvironmentVariableA(key, val);
#else
        setenv(key, val, 1);
#endif
        return NIL;
}

BUILTIN_FUNCTION(getenv)
{
        ASSERT_ARGC("getenv()", 1);

        Value var = ARGx(0, VALUE_STRING);
        char const *val = getenv(TY_TMP_C_STR(var));

        return (val != NULL) ? vSsz(val) : NIL;
}

BUILTIN_FUNCTION(locale_setlocale)
{
        ASSERT_ARGC("locale.setlocale()", 2);

        int category = INT_ARG(0);
        char const *locale = TY_TMP_C_STR(ARGx(1, VALUE_STRING));

        locale = setlocale(category, locale);

        return (locale != NULL) ? vSsz(locale) : NIL;
}

BUILTIN_FUNCTION(json_parse)
{
        ASSERT_ARGC("json.parse()", 1);

        Value json = ARGx(0, VALUE_STRING, VALUE_BLOB);

        u8 const *data;
        usize len;

        switch (json.type) {
        case VALUE_STRING:
                data = ss(json);
                len  = sN(json);
                break;

        case VALUE_BLOB:
                data = vv(*json.blob);
                len  = vN(*json.blob);
                break;

        default:
                UNREACHABLE();
        }

        return json_parse(ty, (char const *)data, len);
}

BUILTIN_FUNCTION(json_parse_xD)
{
        ASSERT_ARGC("json.parse!()", 1);

        Value json = ARGx(0, VALUE_STRING, VALUE_BLOB);

        u8 const *data;
        usize len;

        switch (json.type) {
        case VALUE_STRING:
                data = ss(json);
                len  = sN(json);
                break;

        case VALUE_BLOB:
                data = vv(*json.blob);
                len  = vN(*json.blob);
                break;

        default:
                UNREACHABLE();
        }

        return json_parse_xD(ty, (char const *)data, len);
}

BUILTIN_FUNCTION(json_encode)
{
        ASSERT_ARGC("json.parse()", 1);
        return json_encode(ty, &ARG(0));
}

BUILTIN_FUNCTION(sha512)
{
        ASSERT_ARGC("sha512", 1);

        Value s = ARGx(0, VALUE_STRING, VALUE_BLOB);
        char digest[SHA512_DIGEST_STRING_LENGTH];

        if (s.type == VALUE_STRING) {
                SHA512Data(ss(s), sN(s), digest);
        } else if (s.type == VALUE_BLOB) {
                SHA512Data(vv(*s.blob), vN(*s.blob), digest);
        }

        return vSsz(digest);
}

BUILTIN_FUNCTION(sha256)
{
        ASSERT_ARGC("sha256", 1);

        Value s = ARGx(0, VALUE_STRING, VALUE_BLOB);
        char digest[SHA256_DIGEST_STRING_LENGTH];

        if (s.type == VALUE_STRING) {
                SHA256Data(ss(s), sN(s), digest);
        } else if (s.type == VALUE_BLOB) {
                SHA256Data(vv(*s.blob), vN(*s.blob), digest);
        }

        return vSsz(digest);
}

BUILTIN_FUNCTION(sha1)
{
        ASSERT_ARGC("sha1", 1);

        Value s = ARGx(0, VALUE_STRING, VALUE_BLOB);
        char digest[SHA1_DIGEST_STRING_LENGTH];

        if (s.type == VALUE_STRING) {
                SHA1Data(ss(s), sN(s), digest);
        } else {
                SHA1Data(vv(*s.blob), vN(*s.blob), digest);
        }

        return vSsz(digest);
}

BUILTIN_FUNCTION(md5)
{
        ASSERT_ARGC("md5", 1);

        Value s = ARGx(0, VALUE_STRING, VALUE_BLOB);
        char digest[MD5_DIGEST_STRING_LENGTH];

        if (s.type == VALUE_STRING) {
                MD5Data(ss(s), sN(s), digest);
        } else {
                MD5Data(vv(*s.blob), vN(*s.blob), digest);
        }

        return vSsz(digest);
}

static bool
b64dec(Ty *ty, u8 const *s, size_t n)
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
                xvP(B, (s1 << 2) | (s2 >> 4));
                xvP(B, ((s2 & 0x0F) << 4) | (s3 >> 2));
                xvP(B, ((s3 & 0x03) << 6) | s4);
        }

        memset(g, 0, sizeof g);
        memcpy(g, s + 4*d.quot, d.rem);

        switch (d.rem) {
        case 3:
                s1 = table[g[0]];
                s2 = table[g[1]];
                s3 = table[g[2]];
                xvP(B, (s1 << 2) | (s2 >> 4));
                xvP(B, ((s2 & 0x0F) << 4) | (s3 >> 2));
                break;
        case 2:
                s1 = table[g[0]];
                s2 = table[g[1]];
                xvP(B, (s1 << 2) | (s2 >> 4));
                break;
        case 1:
                s1 = table[g[0]];
                xvP(B, s1 << 2);
                break;
        }

        return true;
}

static void
b64enc(Ty *ty, void const *data, size_t n)
{
        B.count = 0;

        lldiv_t d = lldiv(n, 3);
        unsigned char g[3];

        static char table[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                              "abcdefghijklmnopqrstuvwxyz"
                              "0123456789"
                              "+/";
        u8 const *s = data;

        for (size_t i = 0; i < d.quot; ++i) {
                memcpy(g, s + 3*i, 3);
                xvP(B, table[g[0] >> 2]);
                xvP(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                xvP(B, table[((g[1] & 0x0F) << 2) | (g[2] >> 6)]);
                xvP(B, table[g[2] & 0x3F]);
        }

        memset(g, 0, sizeof g);
        memcpy(g, s + 3*d.quot, d.rem);

        switch (d.rem) {
        case 2:
                xvP(B, table[g[0] >> 2]);
                xvP(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                xvP(B, table[((g[1] & 0x0F) << 2) | (g[2] >> 6)]);
                xvP(B, '=');
                break;
        case 1:
                xvP(B, table[g[0] >> 2]);
                xvP(B, table[((g[0] & 0x03) << 4) | (g[1] >> 4)]);
                xvP(B, '=');
                xvP(B, '=');
                break;
        }
}

BUILTIN_FUNCTION(base64_encode)
{
        ASSERT_ARGC("base64.encode()", 1, 2);

        void const *data;
        isize       len;
        isize       size;

        Value _data = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);

        switch (ARG_T(0)) {
        case VALUE_STRING:
                data = ss(_data);
                size = sN(_data);
                len  = (argc == 2) ? INT_ARG(1) : size;
                break;
                break;

        case VALUE_BLOB:
                data = vv(*_data.blob);
                size = vN(*_data.blob);
                len  = (argc == 2) ? INT_ARG(1) : size;
                break;

        case VALUE_PTR:
                data = ARG(0).ptr;
                size = (argc == 2) ? INT_ARG(1) : strlen((char const *)data);
                len  = size;
                break;
        }

        if (len < 0) {
                len += size;
        }

        b64enc(ty, data, max(0, min(len, size)));

        return vSs(vv(B), vN(B));
}

BUILTIN_FUNCTION(base64_decode)
{
        ASSERT_ARGC("base64.decode()", 1);

        Value _data = ARGx(0, VALUE_STRING, VALUE_BLOB);
        bool ok;

        switch (_data.type) {
        case VALUE_BLOB:
                ok = b64dec(ty, vv(*_data.blob), vN(*_data.blob));
                break;

        case VALUE_STRING:
                ok = b64dec(ty, ss(_data), sN(_data));
                break;
        }

        if (!ok) {
                return NIL;
        }

        Blob *b = value_blob_new(ty);
        uvPv(*b, B);

        return BLOB(b);
}

BUILTIN_FUNCTION(os_umask)
{
        ASSERT_ARGC("os.umask()", 1);

        Value mask = ARG(0);
        if (mask.type != VALUE_INTEGER) {
                zP("the argument to os.umask() must be an integer");
        }

        return INTEGER(umask(mask.z));
}

BUILTIN_FUNCTION(os_open)
{
        ASSERT_ARGC("os.open()", 2, 3);

        char const *path = TY_TMP_C_STR(ARGx(0, VALUE_STRING));

        int flags = INT_ARG(1);
        int fd;

#ifdef __linux__
        bool pass_mode = flags & (O_CREAT | O_TMPFILE);
#else
        bool pass_mode = flags & O_CREAT;
#endif

        if (pass_mode) {
                if (argc != 3) {
                        bP("O_CREAT or O_TMPFILE but no mode");
                }
                fd = open(path, flags, (mode_t)INT_ARG(2));
        } else {
                fd = open(path, flags);
        }


        return INTEGER(fd);
}

BUILTIN_FUNCTION(os_close)
{
        ASSERT_ARGC("os.close()", 1);
        return INTEGER(close(INT_ARG(0)));
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
                Value s = ARG(0);
                if (s.type != VALUE_STRING)
                        zP("the first argument to os.mkdtemp() must be a string");
                /* -8 to make room for the .XXXXXX suffix and NUL byte */
                memcpy(template, ss(s), min(sN(s), sizeof template - 8));
        } else {
                strcpy(template, "tmp");
        }

        strcat(template, ".XXXXXX");

        if (make_temp_dir(template) == NULL) {
                return NIL;
        }

        return vSsz(template);
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
        ASSERT_ARGC("os.mktemp()", 0, 1, 2);

        char template[PATH_MAX + 1] = {0};

        if (argc >= 1 && ARG(0).type != VALUE_NIL) {
                Value s = ARGx(0, VALUE_STRING);
                /* -8 to make room for the .XXXXXX suffix and NUL byte */
                memcpy(template, ss(s), min(sN(s), sizeof template - 8));
        } else {
                strcpy(template, "tmp");
        }

        strcat(template, ".XXXXXX");

        int fd;

        if (argc == 2)
        {
                int flags = INT_ARG(1);
                fd = make_temp_file(template, flags);
        }
        else
        {
                fd = make_temp_file(template, -1);
        }

        if (fd == -1) {
                return NIL;
        }

        Value pair = vT(2);

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

        Value path = ARG(0);
        DIR *dir;

        if (path.type == VALUE_STRING) {
                if (sN(path) >= TY_TMP_N) {
                        errno = ENOENT;
                        return NIL;
                }
                dir = opendir(TY_TMP_C_STR(path));
        } else if (path.type == VALUE_INTEGER) {
                dir = fdopendir(path.z);
        } else {
                ARGx(0, VALUE_INTEGER, VALUE_STRING);
                UNREACHABLE();
        }

        if (dir == NULL)
                return NIL;

        return PTR(dir);
#endif
}

BUILTIN_FUNCTION(os_readdir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.readdir()");
#else
        ASSERT_ARGC("os.readdir()", 1);

        DIR *dir = PTR_ARG(0);

        struct dirent *entry = readdir(dir);
        if (entry == NULL) {
                return NIL;
        }

        Value name = vSsz(entry->d_name);

        NOGC(ss(name));

        Value result = vTn(
                "ino",    INTEGER(entry->d_ino),
                "reclen", INTEGER(entry->d_reclen),
                "type",   INTEGER(entry->d_type),
                "name",   name
        );

        OKGC(ss(name));

        return result;
#endif
}

BUILTIN_FUNCTION(os_rewinddir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.rewinddir()");
#else
        ASSERT_ARGC("os.rewinddir()", 1);
        rewinddir(PTR_ARG(0));
        return NIL;
#endif
}

BUILTIN_FUNCTION(os_seekdir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.seekdir()");
#else
        ASSERT_ARGC("os.seekdir()", 2);

        DIR *dir = PTR_ARG(0);
        isize off = INT_ARG(1);
        seekdir(dir, off);

        return NIL;
#endif
}

BUILTIN_FUNCTION(os_telldir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.telldir()");
#else
        ASSERT_ARGC("os.telldir()", 1);
        return INTEGER(telldir(PTR_ARG(0)));
#endif
}

BUILTIN_FUNCTION(os_closedir)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.closedir()");
#else
        ASSERT_ARGC("os.closedir()", 1);
        return INTEGER(closedir(PTR_ARG(0)));
#endif
}

BUILTIN_FUNCTION(os_getcwd)
{
        ASSERT_ARGC("os.getcwd()", 0);

        char *tmp = TY_TMP();

        if (getcwd(tmp, TY_TMP_N) == NULL) {
                return NIL;
        }

        return vSsz(tmp);
}

BUILTIN_FUNCTION(os_getsid)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.getsid()");
#else
        ASSERT_ARGC("os.getsid()", 1);
        pid_t pid = INT_ARG(0);
        return INTEGER(getsid(pid));
#endif
}

BUILTIN_FUNCTION(os_setsid)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.setsid()");
#else
        ASSERT_ARGC("os.setsid()", 0);
        return INTEGER(setsid());
#endif
}

BUILTIN_FUNCTION(os_getpgid)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.getpgid()");
#else
        ASSERT_ARGC("os.getpgid()", 1);
        pid_t pid = INT_ARG(0);
        return INTEGER(getpgid(pid));
#endif
}

BUILTIN_FUNCTION(os_unlink)
{
        ASSERT_ARGC("os.unlink()", 1);
        Value path = ARGx(0, VALUE_STRING);
        return INTEGER(unlink(TY_TMP_C_STR(path)));
}

BUILTIN_FUNCTION(os_link)
{
        ASSERT_ARGC("os.symlink()", 2);

        char const *old = TY_TMP_C_STR_A(ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR));
        char const *new = TY_TMP_C_STR_B(ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_PTR));

#ifdef _WIN32
        return INTEGER(!CreateHardLinkA(new, new, NULL));
#else
        return INTEGER(link(old, new));
#endif
}

BUILTIN_FUNCTION(os_linkat)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.linkat()");
#else
        ASSERT_ARGC("os.linkat()", 4, 5);

        int dirfd0 = INT_ARG(0);
        Value path0 = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_PTR);

        int dirfd1 = INT_ARG(2);
        Value path1 = ARGx(3, VALUE_STRING, VALUE_BLOB, VALUE_PTR);

        int flags = 0;
        if (argc == 5) {
                flags = INT_ARG(4);
        }

        return INTEGER(
                linkat(
                        dirfd0,
                        TY_TMP_C_STR_A(path0),
                        dirfd1,
                        TY_TMP_C_STR_B(path1),
                        flags
                )
        );
#endif
}

BUILTIN_FUNCTION(os_symlink)
{
        ASSERT_ARGC("os.symlink()", 2);

        Value old = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        Value new = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_PTR);

        char *c_old = TY_TMP_C_STR_A(old);
        char *c_new = TY_TMP_C_STR_B(new);

#ifdef _WIN32
        return INTEGER(!CreateSymbolicLinkA(c_old, c_new, 0));
#else
        return INTEGER(symlink(c_old, c_new));
#endif
}

BUILTIN_FUNCTION(os_rename)
{
        ASSERT_ARGC("os.rename()", 2);

        Value old = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        Value new = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_PTR);

        char *c_old = TY_TMP_C_STR_A(old);
        char *c_new = TY_TMP_C_STR_B(new);

        return INTEGER(rename(c_old, c_new));
}

BUILTIN_FUNCTION(os_mkdir)
{
        ASSERT_ARGC("os.mkdir()", 1, 2);

        Value path = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        mode_t mode = 0777;

        if (argc == 2 && ARG(1).type != VALUE_NIL) {
                mode = INT_ARG(1);
        }

#ifdef _WIN32
        return INTEGER(mkdir(B.items));
#else
        return INTEGER(mkdir(TY_TMP_C_STR(path), mode));
#endif
}

BUILTIN_FUNCTION(os_rmdir)
{
        ASSERT_ARGC("os.rmdir()", 1);
        Value path = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        return INTEGER(rmdir(TY_TMP_C_STR(path)));
}

BUILTIN_FUNCTION(os_chown)
{
        ASSERT_ARGC("os.chown()", 3);

#ifdef _WIN32
        NOT_ON_WINDOWS("os.chown()");
#else

        Value path = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        u64 owner = INT_ARG(1);
        u64 group = INT_ARG(2);

        return INTEGER(chown(TY_TMP_C_STR(path), owner, group));
#endif
}

BUILTIN_FUNCTION(os_chmod)
{
        ASSERT_ARGC("os.chmod()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.chmod()");
#else

        Value path = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        u64 mode = INT_ARG(1);

        return INTEGER(chmod(TY_TMP_C_STR(path), mode));
#endif
}

BUILTIN_FUNCTION(os_access)
{
        ASSERT_ARGC("os.access()", 2);

        Value path = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        int mode = INT_ARG(1);

        return INTEGER(access(TY_TMP_C_STR(path), mode));
}

BUILTIN_FUNCTION(os_readlink)
{
        ASSERT_ARGC("os.readlink()", 1);

        Value path = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);

        char buf[PATH_MAX + 1];
        isize n = readlink(TY_TMP_C_STR(path), buf, sizeof buf - 1);

        if (n < 0)
                return NIL;

        buf[n] = '\0';

        return vSs(buf, n);
}

BUILTIN_FUNCTION(os_utimes)
{
        ASSERT_ARGC("os.utimes()", 1, 3);

#ifndef _WIN32
        Value file = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR, VALUE_INTEGER);
#else
        Value file = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
#endif

        struct timeval times[2];
        struct timeval *ptimes = NULL;

        if (argc == 3) {
                double atime = (ARG(1).type == VALUE_INTEGER)
                             ? ARG(1).z
                             : FLOAT_ARG(1);

                double mtime = (ARG(2).type == VALUE_INTEGER)
                             ? ARG(2).z
                             : FLOAT_ARG(2);

                times[0] = (struct timeval) {
                        .tv_sec = (time_t)atime,
                        .tv_usec = (suseconds_t)((atime - (time_t)atime) * 1e6)
                };

                times[1] = (struct timeval) {
                        .tv_sec = (time_t)mtime,
                        .tv_usec = (suseconds_t)((mtime - (time_t)mtime) * 1e6)
                };

                ptimes = times;
        }

        switch (file.type) {
        case VALUE_STRING:
        case VALUE_BLOB:
        case VALUE_PTR:
                return INTEGER(utimes(TY_TMP_C_STR(file), ptimes));

#ifndef _WIN32
        case VALUE_INTEGER:
                return INTEGER(futimes(file.z, ptimes));
#endif

        default:
                UNREACHABLE();
        }
}

BUILTIN_FUNCTION(os_futimes)
{
        ASSERT_ARGC("os.futimes()", 1, 3);

        int fd = INT_ARG(0);

        if (argc == 1) {
                return INTEGER(futimes(fd, NULL));
        }

        double atime = (ARG(1).type == VALUE_INTEGER)
                     ? ARG(1).z
                     : FLOAT_ARG(1);

        double mtime = (ARG(2).type == VALUE_INTEGER)
                     ? ARG(2).z
                     : FLOAT_ARG(2);

        struct timeval times[2] = {
                {
                        .tv_sec = (time_t)atime,
                        .tv_usec = (suseconds_t)((atime - (time_t)atime) * 1e6)
                },
                {
                        .tv_sec = (time_t)mtime,
                        .tv_usec = (suseconds_t)((mtime - (time_t)mtime) * 1e6)
                }
        };

        return INTEGER(futimes(fd, times));
}

BUILTIN_FUNCTION(os_chdir)
{
        ASSERT_ARGC("os.chdir()", 1);

#ifndef _WIN32
        Value dir = ARGx(0, VALUE_STRING, VALUE_INTEGER, VALUE_BLOB, VALUE_PTR);
#else
        Value dir = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
#endif

        switch (dir.type) {
        case VALUE_STRING:
        case VALUE_BLOB:
        case VALUE_PTR:
                return INTEGER(chdir(TY_TMP_C_STR(dir)));

#ifndef _WIN32
        case VALUE_INTEGER:
                return INTEGER(fchdir(dir.z));
#endif
        }

        UNREACHABLE();
}

BUILTIN_FUNCTION(os_chroot)
{
        ASSERT_ARGC("os.chroot()", 1);
        Value dir = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        return INTEGER(chroot(TY_TMP_C_STR(dir)));
}

BUILTIN_FUNCTION(os_read)
{
        ASSERT_ARGC("os.read()", 2, 3);

        int fd = INT_ARG(0);

        Value blob;
        imax n;

        if (argc == 3) {
                blob = ARGx(1, VALUE_BLOB);
                n = INT_ARG(2);
        } else {
                blob = BLOB(value_blob_new(ty));
                n = INT_ARG(1);
        }

        if (n < 0) {
                bP("bad size: %"PRIiMAX, n);
        }

        uvR(*blob.blob, vN(*blob.blob) + n);

        Value *all = NAMED("all");
        bool read_all = all != NULL && value_truthy(ty, all);

        ssize_t n_read = 0;
        while (n_read < n) {
                lGv(true);
                ssize_t r = read(fd, vZ(*blob.blob) + n_read, n);
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

        if (n_read > 0) {
                vN(*blob.blob) += n_read;
        }

        if (argc == 3) {
                return INTEGER(n_read);
        } else {
                return (n_read > 0) ? blob : NIL;
        }
}

BUILTIN_FUNCTION(os_write)
{
        ASSERT_ARGC("os.write()", 2, 3);

        int fd = INT_ARG(0);
        Value data = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER, VALUE_PTR);

        isize n;
        void const *p;
        unsigned char c;

        switch (data.type) {
        case VALUE_BLOB:
                p = vv(*data.blob);
                n = vN(*data.blob);
                break;
        case VALUE_STRING:
                p = ss(data);
                n = sN(data);
                break;
        case VALUE_INTEGER:
                c = data.z;
                p = &c;
                n = 1;
                break;
        case VALUE_PTR:
                p = data.ptr;
                n = (argc == 3) ? INT_ARG(2) : strlen(p);
                break;
        default:
                UNREACHABLE();
        }

        Value *all = NAMED("all");
        bool write_all = (all != NULL) && value_truthy(ty, all);

        usize off = 0;

        lGv(true);
        while (n > 0) {
                ssize_t r = write(fd, ((unsigned char const *)p) + off, n);
                if (r < 0) {
                        lTk();
                        return (off == 0) ? INTEGER(r) : INTEGER(off);
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

BUILTIN_FUNCTION(os_lseek)
{
        ASSERT_ARGC("os.lseek()", 3);

        int fd = INT_ARG(0);
        isize offset = INT_ARG(1);
        int whence = INT_ARG(2);

        return INTEGER(lseek(fd, (off_t)offset, whence));
}

BUILTIN_FUNCTION(os_ftruncate)
{
        ASSERT_ARGC("os.ftruncate()", 2);

        int fd = INT_ARG(0);
        isize length = INT_ARG(1);

#ifdef __linux__
        return INTEGER(ftruncate64(fd, (off64_t)length));
#else
        return INTEGER(ftruncate(fd, (off_t)length));
#endif
}

BUILTIN_FUNCTION(os_sendfile)
{
#if defined(__APPLE__) || defined(__FreeBSD__)
        ASSERT_ARGC_RANGE("os.sendfile()", 2, 7);
#else
        ASSERT_ARGC_RANGE("os.sendfile()", 2, 4);
#endif

        int out_fd = INT_ARG(0);
        int in_fd = INT_ARG(1);

        isize offset = 0;
        isize count = -1;
        int flags = 0;

        Value header  = NIL;
        Value trailer = NIL;

        switch (argc) {
        case 7:
                trailer = ARGx(6, VALUE_NIL, VALUE_BLOB, VALUE_STRING);
        case 6:
                header = ARGx(5, VALUE_NIL, VALUE_BLOB, VALUE_STRING);
        case 5:
                flags = INT_ARG(4);
        case 4:
                count = INT_ARG(3);
        case 3:
                offset = INT_ARG(2);
                break;
        }

#if defined(_WIN32)
        NOT_ON_WINDOWS("os.sendfile()");
#elif defined(__linux__)
        off_t off = offset;

        ssize_t result = sendfile(
                out_fd,
                in_fd,
                (count >= 0 || offset != 0) ? &off : NULL,
                (count < 0) ? 0x7ffff000 : count
        );

        return PAIR(INTEGER(result), INTEGER(off));
#elif defined(__APPLE__) || defined(__FreeBSD__)
        off_t len = (count < 0) ? 0 : count;

        struct sf_hdtr hdtr;
        struct sf_hdtr *phdtr = NULL;
        struct iovec hdr_iov;
        struct iovec trl_iov;

        if (header.type != VALUE_NIL || trailer.type != VALUE_NIL) {
                switch (header.type) {
                case VALUE_BLOB:
                        hdr_iov.iov_base = vv(*header.blob);
                        hdr_iov.iov_len = vN(*header.blob);
                        hdtr.headers = &hdr_iov;
                        hdtr.hdr_cnt = 1;
                        break;

                case VALUE_STRING:
                        hdr_iov.iov_base = (void *)ss(header);
                        hdr_iov.iov_len = sN(header);
                        hdtr.headers = &hdr_iov;
                        hdtr.hdr_cnt = 1;
                        break;

                default:
                        hdtr.headers = NULL;
                        hdtr.hdr_cnt = 0;
                        break;
                }

                switch (trailer.type) {
                case VALUE_BLOB:
                        trl_iov.iov_base = vv(*trailer.blob);
                        trl_iov.iov_len = vN(*trailer.blob);
                        hdtr.trailers = &trl_iov;
                        hdtr.trl_cnt = 1;
                        break;

                case VALUE_STRING:
                        trl_iov.iov_base = (void *)ss(trailer);
                        trl_iov.iov_len = sN(trailer);
                        hdtr.trailers = &trl_iov;
                        hdtr.trl_cnt = 1;
                        break;

                default:
                        hdtr.trailers = NULL;
                        hdtr.trl_cnt = 0;
                        break;
                }

                phdtr = &hdtr;
        }

#ifdef __APPLE__
        int result = sendfile(in_fd, out_fd, offset, &len, phdtr, flags);
        return INTEGER((result == 0) ? len : result);
#else
        int result = sendfile(
                in_fd,
                out_fd,
                offset,
                (count < 0) ? 0 : count,
                phdtr,
                &len,
                flags
        );

        return PAIR(INTEGER(result), INTEGER(len));
#endif // __APPLE__

#else
        bP("unsupported platform");
#endif
}

BUILTIN_FUNCTION(os_splice)
{
#ifdef __linux__
        ASSERT_ARGC("os.splice()", 5, 6);

        int fd_in = INT_ARG(0);

        loff_t offset_in;
        loff_t *off_in = NULL;
        if (ARG(1).type != VALUE_NIL) {
                offset_in = INT_ARG(1);
                off_in = &offset_in;
        }

        int fd_out = INT_ARG(2);

        loff_t offset_out;
        loff_t *off_out = NULL;
        if (ARG(3).type != VALUE_NIL) {
                offset_out = INT_ARG(3);
                off_out = &offset_out;
        }

        size_t len = INT_ARG(4);

        unsigned int flags = 0;
        if (argc == 6) {
                flags = INT_ARG(5);
        }

        return INTEGER(splice(fd_in, off_in, fd_out, off_out, len, flags));
#else
        zP("os.splice(): unsupported platform");
#endif
}

BUILTIN_FUNCTION(os_copy_file_range)
{
#ifdef __linux__
        ASSERT_ARGC("os.copy_file_range()", 5, 6);

        int fd_in = INT_ARG(0);
        isize *off_in = NULL;
        isize offset_in = 0;
        if (ARG(1).type != VALUE_NIL) {
                offset_in = INT_ARG(1);
                off_in = &offset_in;
        }

        int fd_out = INT_ARG(2);
        isize *off_out = NULL;
        isize offset_out = 0;
        if (ARG(3).type != VALUE_NIL) {
                offset_out = INT_ARG(3);
                off_out = &offset_out;
        }

        imax len = INT_ARG(4);

        uint flags = 0;
        if (argc == 6) {
                flags = INT_ARG(5);
        }

        return INTEGER(
                copy_file_range(
                        fd_in,
                        (off_in != NULL) ? (loff_t *)off_in : NULL,
                        fd_out,
                        (off_out != NULL) ? (loff_t *)off_out : NULL,
                        (usize)len,
                        flags
                )
        );
#else
        zP("os.copy_file_range(): unsupported platform");
#endif
}

BUILTIN_FUNCTION(os_fsync)
{
        ASSERT_ARGC("os.fsync()", 1);

        int fd = INT_ARG(0);
#ifdef _WIN32
        return INTEGER(_commit(fd));
#else
        return INTEGER(fsync(fd));
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

BUILTIN_FUNCTION(os_mmap)
{
        ASSERT_ARGC("os.mmap()", 5, 6);

        Value _hint  = ARGx(0, VALUE_PTR, VALUE_INTEGER, VALUE_NIL);
        isize length = INT_ARG(1);
        int prot     = INT_ARG(2);
        int flags    = INT_ARG(3);
        int fd       = INT_ARG(4);
        isize offset;

        if (argc == 6) {
                offset = INT_ARG(5);
        } else {
                offset = 0;
        }

        void *hint;

        switch (_hint.type) {
        case VALUE_PTR:     hint = _hint.ptr;       break;
        case VALUE_INTEGER: hint = (void *)_hint.z; break;
        case VALUE_NIL:     hint = NULL;            break;
        }

        void *addr = mmap(hint, length, prot, flags, fd, offset);

        return (addr != MAP_FAILED) ? PTR(addr) : NIL;
}

BUILTIN_FUNCTION(os_munmap)
{
        ASSERT_ARGC("os.munmap()", 2);

        void *addr = PTR_ARG(0);
        isize length = INT_ARG(1);

        return INTEGER(munmap(addr, length));
}

#ifdef _WIN32
// Paraphrased from https://github.com/python/cpython/blob/main/Lib/subprocess.py (list2cmdline)
char *
make_cmdline(Array *args)
{
        vec(char) result = {0};

        for (int i = 0; i < args->count; ++i) {
                char const *arg = (char const *)ss(args->items[i]);
                i32 n = sN(args->items[i]);
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

        Value cmd = ARG(0);
        if (cmd.type != VALUE_ARRAY)
                zP("the argument to os.spawn() must be an array");

        if (cmd.array->count == 0)
                zP("empty array passed to os.spawn()");

        for (int i = 0; i < cmd.array->count; ++i)
                if (cmd.array->items[i].type != VALUE_STRING)
                        zP("non-string in array passed to os.spawn()");

        Value *detached = NAMED("detach");
        Value *combine = NAMED("combineOutput");
        Value *share_stderr = NAMED("shareStderr");
        Value *share_stdout = NAMED("shareStdout");
        Value *share_stdin = NAMED("shareStdin");

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
                ty_free(lpAttributeList);
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
        ty_free(lpAttributeList);
        ty_free(cmdline);

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
                "hStdin",   PTR((void *)_get_osfhandle(vStdin.z)),
                "hStdout",  PTR((void *)_get_osfhandle(vStdout.z)),
                "hStderr",  PTR((void *)_get_osfhandle(vStderr.z)),
                "pid",      INTEGER(piProcInfo.dwProcessId),
                "handle",   PTR((void *)piProcInfo.hProcess)
        );
}
#else
BUILTIN_FUNCTION(os_spawn)
{
/* ========================================================================= */
        static TyMutex     SpawnLock;
        static atomic_bool SpawnReady = false;

        bool _false = false;
        if (atomic_compare_exchange_weak(&SpawnReady, &_false, true)) {
                TyMutexInit(&SpawnLock);
                SpawnReady = true;
        }
/* ========================================================================= */
        ASSERT_ARGC("os.spawn()", 1);

        Value cmd = ARGx(0, VALUE_ARRAY);

        if (cmd.array->count == 0) {
                bP("empty argv");
        }

        for (int i = 0; i < vN(*cmd.array); ++i) {
                if (v_(*cmd.array, i)->type != VALUE_STRING) {
                        bP("non-string in argv: %s", VSC(&cmd));
                }
        }

        Value _detach   = KWARG("detach", BOOLEAN);
        Value _chdir    = KWARG("chdir",  INTEGER, STRING, BLOB, PTR, _NIL);
        Value _v_stdin  = KWARG("stdin",  INTEGER);
        Value _v_stdout = KWARG("stdout", INTEGER);
        Value _v_stderr = KWARG("stderr", INTEGER);
        Value _ctty     = KWARG("ctty",   TUPLE, _NIL);

        int ret;

        char const *chdir = NULL;
        int        fchdir = -1;

        switch (_chdir.type) {
        case VALUE_NIL:
                break;

        case VALUE_INTEGER:
                fchdir = _chdir.z;
                break;

        case VALUE_STRING:
        case VALUE_BLOB:
        case VALUE_PTR:
                chdir = TY_TMP_C_STR_B(_chdir);
                break;
        }

        char *ctty;
        int ctty_m;
        int ctty_s;

        if (!IsMissing(_ctty)) {
                Value *name   = tget_t(&_ctty, "name",   VALUE_STRING);
                Value *master = tget_t(&_ctty, "master", VALUE_INTEGER);
                Value *slave  = tget_t(&_ctty, "slave",  VALUE_INTEGER);
                if (name == NULL || master == NULL || slave == NULL) {
                        bP("bad ctty: %s", VSC(&_ctty));
                }
                ctty_m = master->z;
                ctty_s = slave->z;
                ctty = TY_TMP_C_STR_C(*name);
        } else {
                ctty_m = -1;
                ctty_s = -1;
                ctty   = NULL;
        }

        bool detach = !IsMissing(_detach) && _detach.boolean;
        bool setsid = !IsNone(_ctty);

        int _stdin  = IsMissing(_v_stdin)  ? TY_SPAWN_INHERIT : _v_stdin.z;
        int _stdout = IsMissing(_v_stdout) ? TY_SPAWN_INHERIT : _v_stdout.z;
        int _stderr = IsMissing(_v_stderr) ? TY_SPAWN_INHERIT : _v_stderr.z;

        if (_stdin  == TY_SPAWN_INHERIT) { _stdin  = 0; }
        if (_stdout == TY_SPAWN_INHERIT) { _stdout = 1; }
        if (_stderr == TY_SPAWN_INHERIT) { _stderr = 2; }

        int null;
        if (
                (_stdin  == TY_SPAWN_NULL)
              | (_stdout == TY_SPAWN_NULL)
              | (_stderr == TY_SPAWN_NULL)
        ) {
                null = open("/dev/null", O_RDWR);
                if (null < 0) {
                        bP("open(\"/dev/null\"): %s", strerror(errno));
                }
                if (_stdin  == TY_SPAWN_NULL) { _stdin  = null; }
                if (_stdout == TY_SPAWN_NULL) { _stdout = null; }
                if (_stderr == TY_SPAWN_NULL) { _stderr = null; }
        } else {
                null = -1;
        }

        pid_t pgid = getpgrp();
        bool ctty0 = ctty && isatty(_stdin ) && (tcgetpgrp(_stdin ) == pgid);
        bool ctty1 = ctty && isatty(_stdout) && (tcgetpgrp(_stdout) == pgid);
        bool ctty2 = ctty && isatty(_stderr) && (tcgetpgrp(_stderr) == pgid);

        if (ctty0) { _stdin  = ctty_s; }
        if (ctty1) { _stdout = ctty_s; }
        if (ctty2) { _stderr = ctty_s; }

        int _0 = (_stdin  != null) ? _stdin  : -1;
        int _1 = (_stdout != null) ? _stdout : -1;
        int _2 = (_stderr != null) ? _stderr : -1;

        if (ctty0) { _0 = ctty_m; }
        if (ctty1) { _1 = ctty_m; }
        if (ctty2) { _2 = ctty_m; }

        bool octty = (ctty != NULL) && !(ctty0 | ctty1 | ctty2);

        int  in[2];
        int out[2];
        int err[2];

        SCRATCH_SAVE();

        vec(int) x0  = {0};
        vec(int) x1  = {0};

        Value proc = NIL;
/* ========================================================================= */
#define X0(x) svP(x0, x)
#define X1(x) svP(x1, x)

#define P(x, u) do {                                  \
        if (pipe(x) == 0) { X0(x[u 0]); X1(x[u 1]); } \
        else              { goto Fail;              } \
} while (0)
/* ------------------------------------------------------------------------- */
        TyMutexLock(&SpawnLock);

        bool const pipe0 = (_stdin  == TY_SPAWN_PIPE);
        bool const pipe1 = (_stdout == TY_SPAWN_PIPE);
        bool const pipe2 = (_stderr == TY_SPAWN_PIPE);

        bool const merge = (_stderr == TY_SPAWN_MERGE_ERR);

        bool const same0 = (_stdin  == 0);
        bool const same1 = (_stdout == 1);
        bool const same2 = (_stderr == 2);

        if (null != -1) { X0(null); }

        if (pipe0) { P(in, !!); _stdin  =  in[0]; _0 =  in[1]; }
        if (pipe1) { P(out, !); _stdout = out[1]; _1 = out[0]; }
        if (pipe2) { P(err, !); _stderr = err[1]; _2 = err[0]; }

        if (merge) { _stderr = _stdout; _2 = _1; }
/* ------------------------------------------------------------------------- */
#undef P
#undef X1
#undef X0
/* ------------------------------------------------------------------------- */
        posix_spawn_file_actions_t actions;
        posix_spawn_file_actions_init(&actions);
/* ========================================================================= */
#define xD(op, ...) (posix_spawn_file_actions_add##op)(&actions, __VA_ARGS__)
/* ------------------------------------------------------------------------- */
        if (!same0) { xD(dup2, _stdin,  0); }
        if (!same1) { xD(dup2, _stdout, 1); }
        if (!same2) { xD(dup2, _stderr, 2); }

        vfor(x0, xD(close, *it));
        vfor(x1, xD(close, *it));

        if (fchdir !=   -1) { xD(fchdir_np, fchdir); }
        if (chdir  != NULL) { xD( chdir_np,  chdir); }

        if (octty) { xD(open, 3, ctty, O_RDWR, O_CLOEXEC); }
/* ------------------------------------------------------------------------- */
#undef xD
/* ========================================================================= */

        posix_spawnattr_t attr;
        posix_spawnattr_init(&attr);

        if (detach | setsid) {
                i32 flags = 0;
                if (detach) {
                        posix_spawnattr_setpgroup(&attr, 0);
                        flags |= POSIX_SPAWN_SETPGROUP;
                }
                if (setsid) {
                        flags |= POSIX_SPAWN_SETSID;
                }
                posix_spawnattr_setflags(&attr, flags);
        }

        vec(char *) argv = {0};
        vfor(*cmd.array, svP(argv, TY_C_STR(*it)));
        svP(argv, NULL);

        pid_t pid;
        ret = posix_spawnp(&pid, v_0(argv), &actions, &attr, vv(argv), environ);

        posix_spawn_file_actions_destroy(&actions);
        posix_spawnattr_destroy(&attr);
        vfor(argv, ty_free(*it));

        if (ret == 0) {
                proc = vTn(
                        "stdin",   INTEGER(_0),
                        "stdout",  INTEGER(_1),
                        "stderr",  INTEGER(_2),
                        "pid",     INTEGER(pid)
                );
                goto Cleanup;
        } else {
                errno = ret;
        }
/* ------------------------------------------------------------------------- */
Fail:
        vfor(x1, close(*it));
Cleanup:
        vfor(x0, close(*it));
        TyMutexUnlock(&SpawnLock);
        SCRATCH_RESTORE();

        return proc;
}
#endif

BUILTIN_FUNCTION(thread_join)
{
        ASSERT_ARGC("thread.join()", 1, 2);

        Thread *t = ARGx(0, VALUE_THREAD).thread;

        if (t->joined) {
                bP("thread has already been joined");
        }

        if ((argc == 1) || (ARG(1).type == VALUE_NIL)) {
                lGv(true);
                TyThreadJoin(t->t);
                lTk();

                t->joined = true;

                return t->v;
        } else {
                i64 timeoutMs = MSEC_ARG(1);

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

                t->joined = true;

                return Some(t->v);
        }
}

BUILTIN_FUNCTION(thread_detach)
{
        ASSERT_ARGC("thread.detach()", 1);

        Thread *thread = ARGx(0, VALUE_THREAD).thread;

        if (TyThreadDetach(thread->t)) {
                thread->detached = true;
                return BOOLEAN(true);
        } else {
                return BOOLEAN(false);
        }
}

BUILTIN_FUNCTION(thread_mutex)
{
        ASSERT_ARGC("thread.mutex()", 0);
        TyMutex *mtx = mAo(sizeof *mtx, GC_ANY);
        TyMutexInit(mtx);
        return TGCPTR(mtx, (void *)1, mtx);
}

BUILTIN_FUNCTION(thread_spinlock)
{
        ASSERT_ARGC("thread.spinLock()", 0);
        TySpinLock *spin = mAo(sizeof *spin, GC_ANY);
        TySpinLockInit(spin);
        return TGCPTR(spin, (void *)2, spin);
}

BUILTIN_FUNCTION(thread_cond)
{
        ASSERT_ARGC("thread.cond()", 0);
        TyCondVar *cond = mAo(sizeof *cond, GC_ANY);
        TyCondVarInit(cond);
        return TGCPTR(cond, (void *)3, cond);
}

BUILTIN_FUNCTION(thread_cond_wait)
{
        ASSERT_ARGC("thread.waitCond()", 2, 3);

        TyCondVar *cond = PTR_ARG(0);
        TyMutex    *mtx = PTR_ARG(1);

        i64 usec;
        bool forever;

        if (argc == 3) {
                usec = USEC_ARG(2);
                forever = (usec == -1)
                       && (ARG_T(2) == VALUE_INTEGER);
        } else {
                forever = true;
        }

        lGv(true);
        bool ok = forever
                ? TyCondVarWait(cond, mtx)
                : TyCondVarTimedWaitRelative(cond, mtx, usec / 1000);
        lTk();

        return BOOLEAN(ok);
}

BUILTIN_FUNCTION(thread_cond_signal)
{
        ASSERT_ARGC("thread.signalCond()", 1);
        return BOOLEAN(TyCondVarSignal(PTR_ARG(0)));
}

BUILTIN_FUNCTION(thread_cond_broadcast)
{
        ASSERT_ARGC("thread.broadcastCond()", 1);
        return BOOLEAN(TyCondVarBroadcast(PTR_ARG(0)));
}

BUILTIN_FUNCTION(thread_destroy)
{
        ASSERT_ARGC("thread.destroy()", 1);

        bool ok;
        Value object = ARGx(0, VALUE_PTR);

        switch ((uptr)object.extra) {
        case 1:
                ok = TyMutexDestroy(object.ptr);
                break;

        case 2:
                ok = TySpinLockDestroy(object.ptr);
                break;

        case 3:
                ok = TyCondVarDestroy(object.ptr);
                break;

        default:
                UNREACHABLE("invalid object type");
        }

        return BOOLEAN(ok);
}

BUILTIN_FUNCTION(thread_lock)
{
        ASSERT_ARGC("thread.lock()", 1);

        bool ok;
        Value lock = ARGx(0, VALUE_PTR);

        switch ((uptr)lock.extra) {
        case 1:
                lGv(true);
                ok = TyMutexLock(lock.ptr);
                lTk();
                break;

        case 2:
                ok = TySpinLockLock(lock.ptr);
                break;

        default:
                UNREACHABLE("invalid lock type");
        }

        return BOOLEAN(ok);
}

BUILTIN_FUNCTION(thread_trylock)
{
        ASSERT_ARGC("thread.tryLock()", 1);

        bool ok;
        Value lock = ARGx(0, VALUE_PTR);

        switch ((uptr)lock.extra) {
        case 1:
                lGv(true);
                ok = TyMutexTryLock(lock.ptr);
                lTk();
                break;

        case 2:
                ok = TySpinLockTryLock(lock.ptr);
                break;

        default:
                UNREACHABLE("invalid lock type");
        }

        return BOOLEAN(ok);
}

BUILTIN_FUNCTION(thread_unlock)
{
        ASSERT_ARGC("thread.unlock()", 1);

        bool ok;
        Value lock = ARGx(0, VALUE_PTR);

        switch ((uptr)lock.extra) {
        case 1:
                ok = TyMutexUnlock(lock.ptr);
                break;

        case 2:
                ok = TySpinLockUnlock(lock.ptr);
                break;

        default:
                UNREACHABLE("invalid lock type");
        }

        return BOOLEAN(ok);
}

BUILTIN_FUNCTION(thread_create)
{
        ASSERT_ARGC_RANGE("thread.create()", 1, INT_MAX);

        Thread *t = mAo(sizeof *t, GC_THREAD);
        NOGC(t);

        t->i = NextThreadId();
        t->v = NONE;
        t->joined = false;
        t->detached = false;

        Value *ctx = mA((argc + 1) * sizeof (Value));

        for (int i = 0; i < argc; ++i) {
                ctx[i] = ARG(i);
        }

        ctx[argc] = NONE;

        NewThread(ty, t, ctx, NAMED("name"), HAVE_FLAG("isolated"));

        return THREAD(t);
}

BUILTIN_FUNCTION(thread_channel)
{
        ASSERT_ARGC("thread.channel()", 0);

        Channel *chan = mAo(sizeof *chan, GC_ANY);

        chan->open = true;
        v00(chan->q);
        TyCondVarInit(&chan->c);
        TyMutexInit(&chan->m);

        return GCPTR(chan, chan);
}

BUILTIN_FUNCTION(thread_send)
{
        ASSERT_ARGC("thread.send()", 2);

        Channel *chan = PTR_ARG(0);
        ChanVal cv = { .v = ARG(1) };

        Forget(ty, &cv.v, (AllocList *)&cv.as);

        lGv(true);
        TyMutexLock(&chan->m);
        lTk();
        uvP(chan->q, cv);
        TyMutexUnlock(&chan->m);
        TyCondVarSignal(&chan->c);

        return NIL;
}

BUILTIN_FUNCTION(thread_recv)
{
        ASSERT_ARGC("thread.recv()", 1, 2);

        Channel *chan = PTR_ARG(0);

        lGv(true);
        TyMutexLock(&chan->m);
        if (argc == 1) {
                while (chan->open && chan->q.count == 0) {
                        TyCondVarWait(&chan->c, &chan->m);
                }
        } else {
                Value t = ARG(1);
                if (t.type != VALUE_INTEGER) {
                        lTk();
                        zP("thread.recv(): expected integer but got: %s", VSC(&t));
                }
                while (chan->open && chan->q.count == 0) {
                        if (!TyCondVarTimedWaitRelative(&chan->c, &chan->m, t.z)) {
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

        return Some(v.v);
}

BUILTIN_FUNCTION(thread_close)
{
        ASSERT_ARGC("thread.close()", 1);

        Channel *chan = PTR_ARG(0);

        lGv(true);
        TyMutexLock(&chan->m);
        lTk();
        chan->open = false;
        TyMutexUnlock(&chan->m);

        return NIL;
}

BUILTIN_FUNCTION(thread_kill)
{
        ASSERT_ARGC("thread.kill()", 1, 2);

        int how;
        TyThread thread;

        if (argc == 1) {
                thread = TyThreadSelf();
                how = INT_ARG(0);
        } else {
                thread = ARGx(0, VALUE_THREAD).thread->t;
                how = INT_ARG(1);
        }

        return BOOLEAN(TyThreadKill(thread, how));
}

BUILTIN_FUNCTION(thread_setname)
{
        char *_name__ = "thread.setName()";

#if defined(__APPLE__)
        CHECK_ARGC(1);
#else
        CHECK_ARGC(1, 2);
#endif

#ifdef _WIN32
        NOT_ON_WINDOWS("thread.setName()");
#else
        TyThread thread;
        Value name;

        if (argc == 1 || ARG(0).type == VALUE_NIL) {
                thread = TyThreadSelf();
                name = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        } else {
                thread = ARGx(0, VALUE_THREAD).thread->t;
                name = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        }

        char const *pname;

        switch (name.type) {
        case VALUE_STRING:
        case VALUE_BLOB:
                pname = TY_TMP_C_STR(name);
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
        pthread_setname_np(thread, pname);
#endif
        return NIL;
#endif
}

BUILTIN_FUNCTION(thread_getname)
{
        ASSERT_ARGC("thread.getName()", 0, 1);

#ifdef _WIN32
        NOT_ON_WINDOWS("thread.getName()");
#else
        TyThread thread;
        if (argc == 1 && ARG(0).type != VALUE_NIL) {
                thread = ARGx(0, VALUE_THREAD).thread->t;
        } else {
                thread = TyThreadSelf();
        }

        int err;
        char *name = TY_TMP();

        err = pthread_getname_np(thread, name, TY_TMP_N);
        if (err != 0) {
                errno = err;
                return NIL;
        }

        return (*name == '\0') ? NIL : vSsz(name);
#endif
}

BUILTIN_FUNCTION(thread_id)
{
        ASSERT_ARGC_2("thread.id()", 0, 1);

        if (argc == 0 || ARG(0).type == VALUE_NIL) {
                return INTEGER(TyThreadId(ty));
        } else if (ARG(0).type == VALUE_PTR) {
                return INTEGER(((Thread *)ARG(0).ptr)->i);
        } else if (ARG(0).type == VALUE_THREAD) {
                return INTEGER(ARG(0).thread->i);
        } else {
                zP("thread.id(): expected thread pointer but got: %s", VSC(&ARG(0)));
        }
}

BUILTIN_FUNCTION(thread_self)
{
        ASSERT_ARGC("thread.self()", 0);
        return PTR((void *)TyThreadSelf());
}

BUILTIN_FUNCTION(thread_group)
{
        ASSERT_ARGC("thread.group()", 0);

        GC_STOP();
        TySpinLockLock(&ty->group->Lock);

        Array *threads = vAn(vN(ty->group->ThreadList));
        vfor(
                ty->group->ThreadList,
                vPx(*threads, PTR(it))
        );

        TySpinLockUnlock(&ty->group->Lock);
        GC_RESUME();

        return ARRAY(threads);
}

BUILTIN_FUNCTION(thread_sigmask)
{
        ASSERT_ARGC("thread.sigmask()", 0, 2);

        imax how;
        sigset_t set;
        sigset_t *pset;

        if (argc == 0) {
                how = SIG_SETMASK;
                pset = NULL;
        } else {
                how = INT_ARG(0);
                pset = &set;
                IntoSigSet(ty, "thread.sigmask()", &ARG(1), &set);
        }

        sigset_t old;

        int ret = pthread_sigmask(how, pset, &old);
        if (ret != 0) {
                bP("pthread_sigmask(): %s", strerror(ret));
        }

        return NewSigSetFrom(ty, &old);
}

BUILTIN_FUNCTION(thread_atomic)
{
        ASSERT_ARGC("thread.atomic()", 0, 1);

        TyAtomicInt *atomic = mAo(sizeof *atomic, GC_ANY);
        *atomic = (argc == 1) ? INT_ARG(0) : 0;

        return GCPTR(atomic, atomic);
}

BUILTIN_FUNCTION(thread_atomic_load)
{
        ASSERT_ARGC("thread.load()", 1);

        TyAtomicInt *atomic = PTR_ARG(0);

        return INTEGER(
                atomic_load_explicit(
                        atomic,
                        memory_order_acquire
                )
        );
}

BUILTIN_FUNCTION(thread_atomic_store)
{
        ASSERT_ARGC("thread.store()", 2);

        TyAtomicInt *atomic = PTR_ARG(0);
        imax            val = INT_ARG(1);

        atomic_store_explicit(
                atomic,
                val,
                memory_order_release
        );

        return INTEGER(val);
}

BUILTIN_FUNCTION(thread_atomic_cmpxchg)
{
        ASSERT_ARGC("thread.try-swap()", 3);

        TyAtomicInt *atomic = PTR_ARG(0);
        imax            old = INT_ARG(1);
        imax            new = INT_ARG(2);

        imax expected = old;

        bool ok = atomic_compare_exchange_strong_explicit(
                atomic,
                &expected,
                new,
                memory_order_acq_rel,
                memory_order_acquire
        );

        return ok
             ? Ok(ty, INTEGER(new))
             : Err(ty, INTEGER(expected));
}

BUILTIN_FUNCTION(thread_atomic_swap)
{
        ASSERT_ARGC("thread.swap()", 2);

        TyAtomicInt *atomic = PTR_ARG(0);
        imax            val = INT_ARG(1);

        return INTEGER(
                atomic_exchange_explicit(
                        atomic,
                        val,
                        memory_order_acq_rel
                )
        );
}

BUILTIN_FUNCTION(thread_atomic_fetch_add)
{
        ASSERT_ARGC("thread.fetchAdd()", 2);

        TyAtomicInt *atomic = PTR_ARG(0);
        imax            val = INT_ARG(1);

        return INTEGER(
                atomic_fetch_add_explicit(
                        atomic,
                        val,
                        memory_order_acq_rel
                )
        );
}

BUILTIN_FUNCTION(thread_atomic_fetch_sub)
{
        ASSERT_ARGC("thread.fetchSub()", 2);

        TyAtomicInt *atomic = PTR_ARG(0);
        imax            val = INT_ARG(1);

        return INTEGER(
                atomic_fetch_sub_explicit(
                        atomic,
                        val,
                        memory_order_acq_rel
                )
        );
}

BUILTIN_FUNCTION(os_fork)
{
        ASSERT_ARGC("os.fork()", 0);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.fork()");
#else
        int ret = fork();

        switch (ret) {
        case -1:
                return NIL;

        case 0:
                TyPostFork(ty);
        }

        return INTEGER(ret);
#endif
}

BUILTIN_FUNCTION(os_openpty)
{
        ASSERT_ARGC("os.openpty()", 0, 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.openpty()");
#else
        struct termios tios;
        struct winsize winsz;
        struct winsize *pwinsz;

        if (argc == 1) {
                Value size = ARGx(0, VALUE_TUPLE);
                Value *rows = tget_t(&size, 0, VALUE_INTEGER);
                Value *cols = tget_t(&size, 1, VALUE_INTEGER);
                if (rows == NULL || cols == NULL) {
                        bP("bad winsize: %s", VSC(&size));
                }
                winsz.ws_row = rows->z;
                winsz.ws_col = cols->z;
                winsz.ws_xpixel = 0;
                winsz.ws_ypixel = 0;
                pwinsz = &winsz;
        } else {
                pwinsz = NULL;
        }

        int master_fd;
        int slave_fd;

        char *name = TY_TMP();

        if (openpty(&master_fd, &slave_fd, name, &tios, pwinsz) == -1) {
                return NIL;
        }

        return vTn(
                "master",    INTEGER(master_fd),
                "slave",     INTEGER(slave_fd),
                "name",      vSsz(name)
        );
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

        Value fds = vT(2);

        fds.items[0] = INTEGER(p[0]);
        fds.items[1] = INTEGER(p[1]);

        return fds;
#endif
}

BUILTIN_FUNCTION(os_dup)
{
        ASSERT_ARGC("os.dup()", 1);

        Value old = ARG(0);

        if (old.type != VALUE_INTEGER)
                zP("os.dup(): argument must be an integer");

        return INTEGER(dup(old.z));
}

BUILTIN_FUNCTION(os_dup2)
{
        ASSERT_ARGC("os.dup2()", 2);

        Value old = ARG(0);
        Value new = ARG(1);

        if (old.type != VALUE_INTEGER || new.type != VALUE_INTEGER)
                zP("the arguments to os.dup2() must be integers");

        return INTEGER(dup2(old.z, new.z));
}

BUILTIN_FUNCTION(os_socket)
{
        ASSERT_ARGC("os.socket()", 3);

        Value domain = ARG(0);
        Value type = ARG(1);
        Value protocol = ARG(2);

        if (domain.type != VALUE_INTEGER || type.type != VALUE_INTEGER || protocol.type != VALUE_INTEGER)
                zP("the arguments to os.socket() must be integers");

        return INTEGER(socket(domain.z, type.z, protocol.z));
}

BUILTIN_FUNCTION(os_setsockopt)
{
        ASSERT_ARGC_2("os.setsockopt()", 3, 4);

        Value sock = ARG(0);
        if (sock.type != VALUE_INTEGER)
                zP("the first argument to os.setsockopt() must be an integer (socket fd)");

        Value level = ARG(1);
        if (level.type != VALUE_INTEGER)
                zP("the second argument to os.setsockopt() must be an integer (level)");

        Value option = ARG(2);
        if (level.type != VALUE_INTEGER)
                zP("the third argument to os.setsockopt() must be an integer (option)");

        int o;

        if (argc == 4) {
                Value v = ARG(3);
                if (v.type != VALUE_INTEGER)
                        zP("the fourth argument to os.setsockopt() must be an integer (opt value)");
                o = v.z;
        } else {
                o = 1;
        }

        return INTEGER(setsockopt(sock.z, level.z, option.z, &o, sizeof o));
}

BUILTIN_FUNCTION(os_getsockopt)
{
        ASSERT_ARGC("os.getsockopt()", 3);

        Value sock = ARG(0);
        if (sock.type != VALUE_INTEGER)
                zP("the first argument to os.getsockopt() must be an integer (socket fd)");

        Value level = ARG(1);
        if (level.type != VALUE_INTEGER)
                zP("the second argument to os.getsockopt() must be an integer (level)");

        Value option = ARG(2);
        if (level.type != VALUE_INTEGER)
                zP("the third argument to os.getsockopt() must be an integer (option)");

        int o;
        socklen_t n = sizeof o;

        if (getsockopt(sock.z, level.z, option.z, &o, &n) == 0) {
                return INTEGER(o);
        } else {
                return NIL;
        }
}

BUILTIN_FUNCTION(os_getnameinfo)
{
        ASSERT_ARGC("os.getnameinfo()", 1, 2);

        Value _addr = ARGx(0, VALUE_PTR, VALUE_BLOB);
        int flags   = (argc == 2) ? INT_ARG(1) : 0;

        struct sockaddr *addr;
        socklen_t alen;

        switch (_addr.type) {
        case VALUE_PTR:
                addr = _addr.ptr;
                alen = sizeof (struct sockaddr_storage);
                break;

        case VALUE_BLOB:
                addr = (void *)vv(*_addr.blob);
                alen = vN(*_addr.blob);
                break;
        }

        char host[128];
        char serv[32];

        int ret = getnameinfo(addr, alen, host, sizeof host, serv, sizeof serv, flags);
        if (ret != 0) {
                errno = ret;
                return NIL;
        }

        Value v = vT(2);
        gP(&v);
        v.items[0] = vSsz(host);
        v.items[1] = vSsz(serv);
        gX();

        return v;
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
        int r = getpeername(ARG(0).z, (void *)&addr, &addr_size);
        lTk();

        if (r < 0) {
                return NIL;
        }

        Blob *b = value_blob_new(ty);
        uvPn(*b, &addr, min(addr_size, sizeof addr));

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
        int r = getsockname(ARG(0).z, (void *)&addr, &addr_size);
        lTk();

        if (r < 0) {
                return NIL;
        }

        Blob *b = value_blob_new(ty);
        uvPn(*b, &addr, min(addr_size, sizeof addr));

        return BLOB(b);
}

BUILTIN_FUNCTION(os_shutdown)
{
        ASSERT_ARGC("os.shutdown()", 2);

        Value fd = ARG(0);
        Value how = ARG(1);

        if (fd.type != VALUE_INTEGER || how.type != VALUE_INTEGER)
                zP("the arguments to os.shutdown() must be integers");

        return INTEGER(shutdown(fd.z, how.z));
}

BUILTIN_FUNCTION(os_listen)
{
        ASSERT_ARGC("os.listen()", 2);

        Value sockfd = ARG(0);
        Value backlog = ARG(1);

        if (sockfd.type != VALUE_INTEGER || backlog.type != VALUE_INTEGER)
                zP("the arguments to os.listen() must be integers");

        return INTEGER(listen(sockfd.z, backlog.z));
}

BUILTIN_FUNCTION(os_connect)
{
        ASSERT_ARGC("os.connect()", 2);

        Value sockfd = ARG(0);
        Value addr = ARG(1);

        if (sockfd.type != VALUE_INTEGER)
                zP("the first argument to os.connect() must be an integer");

        if (addr.type != VALUE_TUPLE)
                zP("the second argument to os.connect() must be a tuple");

        Value *v = tuple_get(&addr, "family");
        if (v == NULL || v->type != VALUE_INTEGER)
                zP("missing or invalid address family in dict passed to os.connect()");

#ifndef _WIN32
        struct sockaddr_un un_addr;
#endif
        struct sockaddr_in in_addr;
        struct in_addr ia;

        Value *sockaddr = tuple_get(&addr, "address");
        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                return INTEGER(connect(sockfd.z, (struct sockaddr *)sockaddr->blob->items, sockaddr->blob->count));
        } else switch (v->z) {
#ifndef _WIN32
                case AF_UNIX:
                        memset(&un_addr, 0, sizeof un_addr);
                        un_addr.sun_family = AF_UNIX;
                        v = tuple_get(&addr, "path");
                        if (v == NULL || v->type != VALUE_STRING)
                                zP("missing or invalid path in dict passed to os.connect()");
                       memcpy(un_addr.sun_path, ss(*v), min(sN(*v), sizeof un_addr.sun_path));
                        return INTEGER(connect(sockfd.z, (struct sockaddr *)&un_addr, sizeof un_addr));
#endif
                case AF_INET:
                        memset(&in_addr, 0, sizeof in_addr);
                        in_addr.sin_family = AF_INET;
                        v = tuple_get(&addr, "address");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                zP("missing or invalid address in dict passed to os.connect()");
                        ia.s_addr = htonl(v->z);
                        in_addr.sin_addr = ia;
                        v = tuple_get(&addr, "port");
                        if (v == NULL || v->type != VALUE_INTEGER)
                                zP("missing or invalid port in dict passed to os.connect()");
                        unsigned short p = htons(v->z);
                        memcpy(&in_addr.sin_port, &p, sizeof in_addr.sin_port);
                        return INTEGER(connect(sockfd.z, (struct sockaddr *)&in_addr, sizeof in_addr));
                default:
                        zP("invalid arguments to os.connect()");
        }
}

BUILTIN_FUNCTION(os_bind)
{
        ASSERT_ARGC("os.bind()", 2);

        int fd = INT_ARG(0);
        Value addr = ARGx(1, VALUE_TUPLE);

        Value *v = tuple_get(&addr, "family");
        if (v == NULL || v->type != VALUE_INTEGER) {
                bP("expected `family: Int` in address tuple: %s", VSC(&addr));
        }

#ifndef _WIN32
        struct sockaddr_un un_addr;
#endif
        struct sockaddr_in in_addr;
        struct in_addr ia;

        unsigned port;

        Value *sockaddr = tuple_get(&addr, "address");

        if (sockaddr != NULL && sockaddr->type == VALUE_BLOB) {
                int err = bind(
                        fd,
                        (struct sockaddr *)vv(*sockaddr->blob),
                        vN(*sockaddr->blob)
                );
                return INTEGER(err);
        }

        switch (v->z) {
#ifndef _WIN32
        case AF_UNIX:
                memset(&un_addr, 0, sizeof un_addr);
                un_addr.sun_family = AF_UNIX;
                v = tuple_get(&addr, "path");
                if (v == NULL || v->type != VALUE_STRING) {
                        bP("expected `path: String` in address tuple: %s", VSC(&addr));
                }
                memcpy(un_addr.sun_path, ss(*v), min(sN(*v), sizeof un_addr.sun_path));
                return INTEGER(bind(fd, (struct sockaddr *)&un_addr, sizeof un_addr));
#endif
        case AF_INET:
                memset(&in_addr, 0, sizeof in_addr);
                in_addr.sin_family = AF_INET;
                v = tuple_get(&addr, "address");
                if (v == NULL || v->type != VALUE_INTEGER) {
                        bP("expected `address: Int` in address tuple: %s", VSC(&addr));
                }
                ia.s_addr = htonl(v->z);
                in_addr.sin_addr = ia;
                v = tuple_get(&addr, "port");
                if (v == NULL || v->type != VALUE_INTEGER) {
                        bP("expected `port: Int` in address tuple: %s", VSC(&addr));
                }
                port = htons(v->z);
                memcpy(&in_addr.sin_port, &port, sizeof in_addr.sin_port);
                return INTEGER(bind(fd, (struct sockaddr *)&in_addr, sizeof in_addr));

        default:
                bP("unknown address family: %d", (int)v->z);
        }
}

BUILTIN_FUNCTION(os_getaddrinfo)
{
        ASSERT_ARGC("os.getaddrinfo()", 5, 6);

        Value host = ARGx(0, VALUE_STRING, VALUE_NIL);
        Value port = ARGx(1, VALUE_STRING, VALUE_INTEGER, VALUE_NIL);

        if (host.type == VALUE_NIL && port.type == VALUE_NIL) {
                bP("node and service cannot both be nil");
        }

        i32 family = INT_ARG(2);
        i32 type = INT_ARG(3);
        i32 protocol = INT_ARG(4);

        // Default to the flags used when hints == NULL in glibc getaddrinfo()
        int flags = AI_V4MAPPED | AI_ADDRCONFIG;
        if (argc == 6 && ARG(5).type != VALUE_NIL) {
                flags = INT_ARG(5);
        }

        char const *node;
        char const *service;

        B.count = 0;

        char *tmp = TY_TMP();

        if (port.type == VALUE_INTEGER) {
                snprintf(tmp, TY_TMP_N, "%hu", (unsigned short)port.z);
                port = xSz(tmp);
        }

        if (host.type != VALUE_NIL) {
                xvPn(B, ss(host), sN(host));
                xvP(B, '\0');

                xvPn(B, ss(port), sN(port));
                xvP(B, '\0');

                node = B.items;
                service = B.items + sN(host) + 1;
        } else if (port.type == VALUE_NIL) {
                xvPn(B, ss(host), sN(host));
                xvP(B, '\0');

                node = B.items;
                service = NULL;
        } else {
                xvPn(B, ss(port), sN(port));
                xvP(B, '\0');

                node = NULL;
                service = B.items;
        }

        struct addrinfo *res;
        struct addrinfo hints;

        memset(&hints, 0, sizeof hints);
        hints.ai_flags = flags;
        hints.ai_family = family;
        hints.ai_socktype = type;
        hints.ai_protocol = protocol;

        lGv(true);
        int ret = getaddrinfo(node, service, &hints, &res);
        lTk();
        if (ret != 0) {
                return Err(ty, INTEGER(ret));
        }

        Value results = ARRAY(vA());

        GC_STOP();
        for (struct addrinfo *it = res; it != NULL; it = it->ai_next) {
                Blob *b = value_blob_new(ty);

                Value entry = vTn(
                        "family",    INTEGER(it->ai_family),
                        "type",      INTEGER(it->ai_socktype),
                        "protocol",  INTEGER(it->ai_protocol),
                        "address",   BLOB(b),
                        "canonname", NIL
                );

                vAp(results.array, entry);

                vvPn(*b, (char *)it->ai_addr, it->ai_addrlen);

                if (it->ai_canonname != NULL) {
                        entry.items[4] = vSsz(it->ai_canonname);
                }
        }
        freeaddrinfo(res);
        GC_RESUME();

        return Ok(ty, results);
}

BUILTIN_FUNCTION(os_gai_strerror)
{
        ASSERT_ARGC("os.gai_strerror()", 1);
        return xSz(gai_strerror(INT_ARG(0)));
}

BUILTIN_FUNCTION(os_accept)
{
        ASSERT_ARGC("os.accept()", 1);

        int sockfd = INT_ARG(0);

        struct sockaddr _addr;
        socklen_t n = sizeof _addr;

        lGv(true);
        int ret = accept(sockfd, &_addr, &n);
        lTk();

        if (ret < 0) {
                return NIL;
        }

        Blob *addr = value_blob_new(ty);
        GC_STOP();
        Value conn = PAIR(INTEGER(ret), BLOB(addr));
        uvPn(*addr, (u8 *)&_addr, n);
        GC_RESUME();

        return conn;
}

BUILTIN_FUNCTION(os_recvfrom)
{
        ASSERT_ARGC("os.recvfrom()", 3, 4);

        int fd = INT_ARG(0);

        Value buffer;
        imax size;
        imax flags;

        if (argc == 3) {
                buffer = BLOB(value_blob_new(ty));
                size = INT_ARG(1);
                flags = INT_ARG(2);
        } else {
                buffer = ARGx(1, VALUE_BLOB);
                size = INT_ARG(2);
                flags = INT_ARG(3);
        }

        uvR(*buffer.blob, size);

        struct sockaddr_storage addr;
        socklen_t addr_size = sizeof addr;

        lGv(true);
        ssize_t r = recvfrom(fd, vv(*buffer.blob), size, flags, (void *)&addr, &addr_size);
        lTk();
        if (r < 0) {
                return NIL;
        }

        vN(*buffer.blob) = r;

        GC_STOP();

        Blob *b = value_blob_new(ty);
        uvPn(*b, &addr, min(addr_size, sizeof addr));

        Value result = vT(2);

        result.items[0] = buffer;
        result.items[1] = BLOB(b);

        GC_RESUME();

        return result;
}

BUILTIN_FUNCTION(os_sendto)
{
        ASSERT_ARGC("os.sendto()", 3, 4);

        int fd = INT_ARG(0);

        u8 const *data;
        usize len;

        Value buffer = ARGx(1, VALUE_BLOB, VALUE_STRING);

        switch (buffer.type) {
        case VALUE_BLOB:
                data = vv(*buffer.blob);
                len = vN(*buffer.blob);
                break;

        case VALUE_STRING:
                data = ss(buffer);
                len = sN(buffer);
                break;
        }

        int flags = INT_ARG(2);
        Blob *addr = ARGx(3, VALUE_BLOB).blob;

        lGv(true);
        ssize_t ret = sendto(fd, data, len, flags, (void *)vv(*addr), vN(*addr));
        lTk();

        return INTEGER(ret);
}

BUILTIN_FUNCTION(os_poll)
{
        ASSERT_ARGC("os.poll()", 1, 2, 3);

        Array *fds = ARRAY_ARG(0);
        Array *fds_out;
        i64 timeout;

        switch (argc) {
        case 1:
                fds_out = vA();
                timeout = -1;
                break;

        case 2:
                fds_out = vA();
                timeout = MSEC_ARG(1);
                break;

        case 3:
                fds_out = ARRAY_ARG(1);
                timeout = MSEC_ARG(2);
                break;

        default:
                UNREACHABLE();
        }

        // Don't treat -1 as an indefinite timeout if the argument was
        // originally floating point
        if (
                (argc == 2 && ARG(1).type == VALUE_REAL)
             || (argc == 3 && ARG(2).type == VALUE_REAL)
        ) {
                timeout += (timeout == -1);
        }

        SCRATCH_SAVE();

        struct pollfd *pfds = smA0(vN(*fds) * sizeof (struct pollfd));

        Value *v;
        Value *fd;
        Value *ev;
        for (int i = 0; i < vN(*fds); ++i) {
                struct pollfd pfd = {0};

                v = v_(*fds, i);
                switch (v->type) {
                case VALUE_INTEGER:
                        pfd.fd = v->z;
                        pfd.events = POLLIN;
                        break;

                case VALUE_TUPLE:
                        if (
                                ((fd = tget_t(v, 0, VALUE_INTEGER)) != NULL)
                             && ((ev = tget_t(v, 1, VALUE_INTEGER)) != NULL)
                        ) {
                                pfd.fd = fd->z;
                                pfd.events = ev->z;
                                break;
                        }
                        // fall

                default:
                        bP("unexpected value in pollfd set: %s", VSC(v));
                }

                pfds[i] = pfd;
        }

        NOGC(fds_out);
        lGv(true);
#ifdef _WIN32
        int n = WSAPoll(pfds, vN(*fds), timeout);
#else
        int n = poll(pfds, vN(*fds), timeout);
#endif
        int err = errno;
        lTk();
        OKGC(fds_out);

        vN(*fds_out) = 0;

        if (n > 0) {
                GC_STOP();
                for (int i = 0; i < vN(*fds) && vN(*fds_out) < n; ++i) {
                        if (pfds[i].revents != 0) {
                                Value fd = INTEGER(pfds[i].fd);
                                Value ev = INTEGER(pfds[i].revents);
                                Value *user = tget_or_null(v_(*fds, i), 2);
                                Value out = (user != NULL)
                                          ? TRIPLE(fd, ev, *user)
                                          : PAIR(fd, ev);
                                vAp(fds_out, out);
                        }
                }
                GC_RESUME();
        }

        SCRATCH_RESTORE();

        return (argc == 3) ? INTEGER(n)
             : (n    >= 0) ? Ok(ty, ARRAY(fds_out))
             :               Err(ty, INTEGER(err));
}

#ifdef __linux__
BUILTIN_FUNCTION(os_epoll_create)
{
        ASSERT_ARGC("os.epoll_create()", 1);

        Value flags = ARG(0);
        if (flags.type != VALUE_INTEGER)
                zP("the argument to os.epoll_create() must be an integer");

        return INTEGER(epoll_create1(flags.z));
}

BUILTIN_FUNCTION(os_epoll_ctl)
{
        ASSERT_ARGC("os.epoll_ctl()", 4);

        Value efd = ARG(0);
        if (efd.type != VALUE_INTEGER)
                zP("the first argument to os.epoll_ctl() must be an integer");

        Value op = ARG(1);
        if (op.type != VALUE_INTEGER)
                zP("the second argument to os.epoll_ctl() must be an integer");

        Value fd = ARG(2);
        if (fd.type != VALUE_INTEGER)
                zP("the third argument to os.epoll_ctl() must be an integer");

        Value events = ARG(3);
        if (events.type != VALUE_INTEGER)
                zP("the fourth argument to os.epoll_ctl() must be an integer");

        struct epoll_event ev = {
                .events = events.z,
                .data = { .fd = fd.z }
        };

        return INTEGER(epoll_ctl(efd.z, op.z, fd.z, &ev));
}

BUILTIN_FUNCTION(os_epoll_wait)
{
        ASSERT_ARGC("os.epoll_wait()", 2);

        Value efd = ARG(0);
        if (efd.type != VALUE_INTEGER)
                zP("the first argument to os.epoll_wait() must be an integer (epoll fd)");

        Value timeout = ARG(1);
        if (timeout.type != VALUE_INTEGER)
                zP("the second argument to os.epoll_wait() must be an integer (timeout in ms)");

        struct epoll_event events[32];

        lGv(true);
        int n = epoll_wait(efd.z, events, sizeof events / sizeof events[0], timeout.z);
        lTk();

        if (n == -1)
                return NIL;

        struct array *result = vA();

        gP(&ARRAY(result));

        for (int i = 0; i < n; ++i) {
                Value ev = vT(2);
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

BUILTIN_FUNCTION(os_wait)
{
        ASSERT_ARGC("os.wait()", 0, 1, 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.wait()");
#else
        imax pid;
        imax flags;

        switch (argc) {
        case 0:
                pid = -1;
                flags = 0;
                break;

        case 1:
                pid = INT_ARG(0);
                flags = 0;
                break;

        case 2:
                pid = INT_ARG(0);
                flags = INT_ARG(1);
                break;
        }

        int status;
        int ret;

        lGv(true);
        for (;;) {
                ret = waitpid(pid, &status, flags);
                if (ret == -1 && errno == EINTR) {
                        continue;
                }
                break;
        }
        lTk();
        if (ret < 0 && errno != ECHILD) {
                bP("%s", strerror(errno));
        }

        return (ret > 0) ? PAIR(INTEGER(ret), INTEGER(status)) : NIL;
#endif
}

#ifdef _WIN32
#define WAITMACRO(name) \
        Value \
        builtin_os_ ## name(Ty *ty, int argc, Value *kwargs) \
        { \
                NOT_ON_WINDOWS("os." #name); \
        }
#else
#define WAITMACRO(name)                                                           \
        Value                                                                     \
        builtin_os_ ## name(Ty *ty, int argc, Value *kwargs)                      \
        {                                                                         \
                ASSERT_ARGC("os." #name, 1);                                      \
                                                                                  \
                Value status = ARG(0);                                            \
                if (status.type != VALUE_INTEGER)                                 \
                        zP("the argument to os." #name "() must be an integer");  \
                                                                                  \
                int s = status.z;                                                 \
                                                                                  \
                return INTEGER(name(s));                                          \
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
        Value \
        builtin_os_ ## name (Ty *ty, int argc, Value *kwargs) \
        { \
                NOT_ON_WINDOWS("os." #name); \
        }
#define SETID(name) \
        Value \
        builtin_os_ ## name (Ty *ty, int argc, Value *kwargs) \
        { \
                NOT_ON_WINDOWS("os." #name); \
        }
#else
#define GETID(name) \
        Value \
        builtin_os_ ## name (Ty *ty, int argc, Value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 0); \
                return INTEGER(name()); \
        }

#define SETID(name) \
        Value \
        builtin_os_ ## name (Ty *ty, int argc, Value *kwargs) \
        { \
                ASSERT_ARGC("os." #name, 1); \
                Value id = ARG(0); \
                if (id.type != VALUE_INTEGER) \
                        zP("the argument to os." #name "() must be an integer"); \
                return INTEGER(name(id.z)); \
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
        exit(INT_ARG(0));
}

BUILTIN_FUNCTION(os_pause)
{
        ASSERT_ARGC("os.pause()", 0);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.pause()");
#else
        return INTEGER(pause());
#endif
}

BUILTIN_FUNCTION(os_exec)
{
        ASSERT_ARGC("os.exec()", 1);

        Value cmd = ARGx(0, VALUE_ARRAY);

        if (vN(*cmd.array) == 0) {
                bP("empty argv");
        }

        for (int i = 0; i < vN(*cmd.array); ++i) {
                if (v_(*cmd.array, i)->type != VALUE_STRING) {
                        bP("non-string in argv: %s", VSC(&cmd));
                }
        }

        StringVector argv = {0};

        for (int i = 0; i < vN(*cmd.array); ++i) {
                char *arg = TY_C_STR(v__(*cmd.array, i));
                xvP(argv, arg);
        }

        vvP(argv, NULL);

        return INTEGER(execvp(v_0(argv), vv(argv)));
}

BUILTIN_FUNCTION(os_signal)
{
        ASSERT_ARGC("os.signal()", 1, 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.signal()");
#else
        imax sig = INT_ARG(0);

        if (argc == 1) {
                return vm_get_sigfn(ty, sig);
        }

        Value f = ARG(1);

        struct sigaction act = {0};

        switch (f.type) {
        case VALUE_INTEGER:
                switch (f.z) {
                case 0:
                        vm_del_sigfn(ty, sig);
                        act.sa_handler = SIG_DFL;
                        break;

                case 1:
                        vm_del_sigfn(ty, sig);
                        act.sa_handler = SIG_IGN;
                        break;

                default:
                        bP("bad signal handler: %s", VSC(&f));
                }
                break;

        case VALUE_NIL:
                vm_del_sigfn(ty, sig);
                act.sa_handler = SIG_DFL;
                break;

        default:
                if (!CALLABLE(f)) {
                        zP("the second argument to os.signal() must be callable");
                }
                act.sa_flags = SA_SIGINFO;
                act.sa_sigaction = vm_do_signal;
        }

        int ret = sigaction(sig, &act, NULL);
        if (ret == 0) {
                vm_set_sigfn(ty, sig, &f);
        }

        return INTEGER(ret);
#endif
}

BUILTIN_FUNCTION(os_sigprocmask)
{
        ASSERT_ARGC("os.sigprocmask()", 0, 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigprocmask()");
#else
        imax how;
        sigset_t set;
        sigset_t old;

        if (argc == 0) {
                how = SIG_SETMASK;
                sigemptyset(&set);
        } else {
                how = INT_ARG(0);
                IntoSigSet(ty, "os.sigprocmask()", &ARG(1), &set);
        }

        int ret = sigprocmask(how, &set, &old);
        if (ret != 0) {
                bP("%s", strerror(errno));
        }

        return NewSigSetFrom(ty, &old);
#endif
}

BUILTIN_FUNCTION(os_sigpending)
{
        ASSERT_ARGC("os.sigpending()", 0);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigpending()");
#else
        sigset_t pending;
        sigemptyset(&pending);

        int ret = sigpending(&pending);
        if (ret != 0) {
                bP("%s", strerror(errno));
        }

        return NewSigSetFrom(ty, &pending);
#endif
}

BUILTIN_FUNCTION(os_sigsuspend)
{
        ASSERT_ARGC("os.sigsuspend()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigsuspend()");
#else
        sigset_t set;

        IntoSigSet(ty, "os.sigsuspend()", &ARG(0), &set);

        lGv(true);
        int ret = sigsuspend(&set);
        lTk();
        if (ret != 0 && errno != EINTR) {
                bP("%s", strerror(errno));
        }

        return NIL;
#endif
}

BUILTIN_FUNCTION(os_sigwaitinfo)
{
        ASSERT_ARGC("os.sigwaitinfo()", 1, 2);
#if !defined(__linux__)
        bP("os.sigwaitinfo() is not supported on this platform");
#else
        Value timeout;

        if (argc == 1) {
                timeout = NIL;
        } else {
                timeout = ARGx(1, VALUE_TUPLE, VALUE_INTEGER, VALUE_REAL, VALUE_NIL);
        }

        sigset_t set;
        IntoSigSet(ty, "os.sigwaitinfo()", &ARG(0), &set);

        struct timespec ts;
        i64 nsec;

        switch (timeout.type) {
        case VALUE_TUPLE:
                ts = tuple_timespec(ty, "os.sigtimedwait()", &timeout);
                break;

        case VALUE_INTEGER:
        case VALUE_REAL:
                nsec = NSEC_ARG(1);
                ts.tv_sec = nsec / TY_1e9;
                ts.tv_nsec = nsec % TY_1e9;
                break;

        case VALUE_NIL:
                ts.tv_sec = 0;
                ts.tv_nsec = 0;
                break;
        }

        siginfo_t info;
        int ret;

        errno = 0;
        if (argc == 1) {
                ret = sigwaitinfo(&set, &info);
        } else {
                ret = sigtimedwait(&set, &info, &ts);
        }

        if (ret == -1) {
                if (errno == EAGAIN) {
                        return NIL;
                } else {
                        bP("%s", strerror(errno));
                }
        }

        Value result = vTn(
                "signo",   INTEGER(info.si_signo),
                "code",    INTEGER(info.si_code),
                "errno",   INTEGER(info.si_errno),
                "pid",     INTEGER(info.si_pid),
                "uid",     INTEGER(info.si_uid),
                "status",  INTEGER(info.si_status),
#if defined(__linux__)
                "utime",   INTEGER(info.si_utime),
                "stime",   INTEGER(info.si_stime),
                "fd",      INTEGER(info.si_fd),
#endif
                "value",   INTEGER(info.si_value.sival_int),
                "addr",    INTEGER((imax)(uintptr_t)info.si_addr),
                "band",    INTEGER(info.si_band)
        );

        return result;
#endif
}

BUILTIN_FUNCTION(os_sigwait)
{
        ASSERT_ARGC("os.sigwait()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigwait()");
#else
        sigset_t set;

        IntoSigSet(ty, "os.sigwait()", &ARG(0), &set);

        int sig;
        lGv(true);
        int ret = sigwait(&set, &sig);
        lTk();
        if (ret != 0) {
                bP("%s", strerror(ret));
        }

        return INTEGER(sig);
#endif
}

BUILTIN_FUNCTION(os_sigset)
{
        ASSERT_ARGC("os.sigset()", 0, 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigset()");
#else
        sigset_t set;

        if (argc == 1) {
                IntoSigSet(ty, "os.sigset()", &ARG(0), &set);
        } else {
                sigemptyset(&set);
        }

        return NewSigSetFrom(ty, &set);
#endif
}

BUILTIN_FUNCTION(os_sigemptyset)
{
        ASSERT_ARGC("os.sigemptyset()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigemptyset()");
#else
        sigemptyset((sigset_t *)PTR_ARG(0));
        return ARG(0);
#endif
}

BUILTIN_FUNCTION(os_sigfillset)
{
        ASSERT_ARGC("os.sigfillset()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigfillset()");
#else
        sigfillset((sigset_t *)PTR_ARG(0));
        return ARG(0);
#endif
}

BUILTIN_FUNCTION(os_sigaddset)
{
        ASSERT_ARGC("os.sigaddset()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigaddset()");
#else
        sigset_t *set = PTR_ARG(0);
        imax sig = INT_ARG(1);

        int ret = sigaddset(set, sig);
        if (ret != 0) {
                bP("%s", strerror(ret));
        }

        return ARG(0);
#endif
}

BUILTIN_FUNCTION(os_sigdelset)
{
        ASSERT_ARGC("os.sigdelset()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigdelset()");
#else
        sigset_t *set = PTR_ARG(0);
        imax sig = INT_ARG(1);

        int ret = sigdelset(set, sig);
        if (ret != 0) {
                bP("%s", strerror(ret));
        }

        return ARG(0);
#endif
}

BUILTIN_FUNCTION(os_sigismember)
{
        ASSERT_ARGC("os.sigismember()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.sigismember()");
#else
        sigset_t *set = PTR_ARG(0);
        imax sig = INT_ARG(1);

        return BOOLEAN(sigismember(set, sig));
#endif
}

BUILTIN_FUNCTION(os_signame)
{
        ASSERT_ARGC("os.signame()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.strsignal()");
#else
        imax sig = INT_ARG(0);

        if (sig < 0 || sig >= NSIG) {
                return NIL;
        }

#if defined(__APPLE__)
        return xSz(sys_signame[sig]);
#else
        return xSz(sigabbrev_np(sig));
#endif
#endif
}

BUILTIN_FUNCTION(os_strsignal)
{
        ASSERT_ARGC("os.strsignal()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.strsignal()");
#else
        imax sig = INT_ARG(0);
        char *name = strsignal(sig);
        return (name != NULL) ? xSz(name) : NIL;
#endif
}

BUILTIN_FUNCTION(os_kill)
{
        ASSERT_ARGC("os.kill()", 2);

        imax pid = INT_ARG(0);
        imax sig = INT_ARG(1);

#ifdef _WIN32
        HANDLE hProc = OpenProcess(PROCESS_ALL_ACCESS, FALSE, pid);
        bool bSuccess = TerminateProcess(hProc, 0);
        int error = GetLastError();
        CloseHandle(hProc);
        return INTEGER(bSuccess ? 0 : error);
#else
        return INTEGER(kill(pid, sig));
#endif
}

BUILTIN_FUNCTION(os_raise)
{
        ASSERT_ARGC("os.raise()", 1);
        return INTEGER(raise(INT_ARG(0)));
}

static Value
timespec_tuple(Ty *ty, struct timespec const *ts)
{
        return vTn(
                "sec",  INTEGER(ts->tv_sec),
                "nsec", INTEGER(ts->tv_nsec)
        );
}

inline static double
timespec_seconds(struct timespec const *ts)
{
        return (double)ts->tv_sec + (double)ts->tv_nsec / 1e9;
}

static struct timespec
tuple_timespec(Ty *ty, char const *func, Value const *v)
{
        Value *sec = tuple_get(v, "sec");

        if (sec == NULL || sec->type != VALUE_INTEGER) {
                zP(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        VSC(v),
                        TERM(0),
                        TERM(92),
                        "sec",
                        TERM(0)
                );
        }

        Value *nsec = tuple_get(v, "nsec");

        if (nsec == NULL || nsec->type != VALUE_INTEGER) {
                zP(
                        "%s: expected timespec %s%s%s to have Int field %s%s%s",
                        func,
                        TERM(93),
                        VSC(v),
                        TERM(0),
                        TERM(92),
                        "nsec",
                        TERM(0)
                );
        }

        return (struct timespec) {
                .tv_sec = sec->z,
                .tv_nsec = nsec->z
        };
}

#if !defined(__APPLE__)
BUILTIN_FUNCTION(os_sleep)
{
        ASSERT_ARGC("os.sleep()", 1);

        struct timespec dur;
        struct timespec rem = {0};

        i64 nsec = NSEC_ARG(0);

        int flags = 0;

        clockid_t clk;
        Value *abs = NAMED("abs");

#ifndef _WIN32
        if (abs != NULL && abs->type == VALUE_BOOLEAN && abs->boolean) {
                flags = TIMER_ABSTIME;
                clk = CLOCK_REALTIME;
        } else {
                clk = CLOCK_MONOTONIC;
        }
#endif

        Value *clock = NAMED("clock");
        if (clock != NULL && clock->type == VALUE_INTEGER) {
                clk = clock->z;
        }

        dur.tv_sec = nsec / TY_1e9;
        dur.tv_nsec = nsec % TY_1e9;

        lGv(true);
#ifdef _WIN32
        Sleep(dur.tv_sec * 1000 + dur.tv_nsec / 1000000);
        int ret = 0;
#else
        errno = 0;
        int ret = clock_nanosleep(clk, flags, &dur, &rem);
#endif
        lTk();

        switch (ret) {
        case 0:
                return NIL;
        case EINTR:
                return timespec_tuple(ty, &rem);
        default:
                bP("clock_nanosleep(): %s", strerror(errno));
        }
}
#else
BUILTIN_FUNCTION(os_sleep)
{
        ASSERT_ARGC("os.sleep()", 1);

        i64 nsec = NSEC_ARG(0);

        struct timespec dur = {
                .tv_sec = nsec / TY_1e9,
                .tv_nsec = nsec % TY_1e9
        };
        struct timespec rem = {0};

        lGv(true);
        errno = 0;
        int ret = nanosleep(&dur, &rem);
        lTk();

        switch (ret) {
        case -1:
                if (errno == EINTR) {
                        return timespec_tuple(ty, &rem);
                } else {
                        bP("nanosleep(): %s", strerror(errno));
                }

        default:
                return NIL;
        }
}
#endif

static int
microsleep(i64 usec)
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
        return INTEGER(microsleep(USEC_ARG(0)));
}

#ifdef _WIN32
BUILTIN_FUNCTION(os_listdir)
{
        ASSERT_ARGC("os.listdir()", 1);
        Value dir = ARG(0);
        if (dir.type != VALUE_STRING)
                zP("the argument to os.listdir() must be a string");

        // Prepare the search path
        B.count = 0;
        xvPn(B, ss(dir), sN(dir));
        xvPn(B, "\\*", 2); // Add wildcard for all files
        xvP(B, '\0');

        WIN32_FIND_DATAA findData;
        HANDLE hFind = FindFirstFileA(B.items, &findData);
        if (hFind == INVALID_HANDLE_VALUE)
                return NIL;

        struct array* files = vA();
        Value vFiles = ARRAY(files);
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

        Value dir = ARGx(0, VALUE_STRING);

        DIR *d = opendir(TY_TMP_C_STR(dir));
        if (d == NULL) {
                return NIL;
        }

        Array *files = vA();
        Value vFiles = ARRAY(files);

        GC_STOP();

        struct dirent *e;
        while (e = readdir(d), e != NULL) {
                if (
                        (strcmp(e->d_name, ".")  != 0)
                     && (strcmp(e->d_name, "..") != 0)
                ) {
                        uvP(*files, vSsz(e->d_name));
                }
        }

        closedir(d);

        GC_RESUME();

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

        Value path = ARGx(0, VALUE_STRING);

        if (sN(path) >= PATH_MAX) {
                return NIL;
        }

        char in[PATH_MAX + 1];
        char out[PATH_MAX + 1];

        memcpy(in, ss(path), sN(path));
        in[sN(path)] = '\0';

        char *resolved = resolve_path(in, out);

        return (resolved != NULL) ? vSsz(out) : NIL;
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

        char const *path = TY_TMP_C_STR(ARGx(0, VALUE_STRING));
        i64 size = INT_ARG(1);

        return INTEGER(truncate_file(path, size));
}

inline static Value
xstatv(Ty *ty, int ret, StatStruct const *st)
{
        if (ret != 0)
               return NIL;

        Value atime;
        Value mtime;
        Value ctime;

        GC_STOP();

#if defined(__APPLE__) || defined(__MACH__)
        atime = REAL(timespec_seconds(&st->st_atimespec));
        mtime = REAL(timespec_seconds(&st->st_mtimespec));
        ctime = REAL(timespec_seconds(&st->st_ctimespec));
#elif defined(_WIN32)
        atime = REAL(((double)st->st_atime);
        mtime = REAL(((double)st->st_mtime);
        ctime = REAL(((double)st->st_ctime);
#else
        atime = REAL(timespec_seconds(&st->st_atim));
        mtime = REAL(timespec_seconds(&st->st_mtim));
        ctime = REAL(timespec_seconds(&st->st_ctim));
#endif

        GC_RESUME();

        return vTn(
                "dev", INTEGER(st->st_dev),
                "ino", INTEGER(st->st_ino),
                "mode", INTEGER(st->st_mode),
                "nlink", INTEGER(st->st_nlink),
                "uid", INTEGER(st->st_uid),
                "gid", INTEGER(st->st_gid),
                "rdev", INTEGER(st->st_rdev),
                "size", INTEGER(st->st_size),
#ifndef _WIN32
                "blocks", INTEGER(st->st_blocks),
                "blksize", INTEGER(st->st_blksize),
#endif
                "atime", atime,
                "mtime", mtime,
                "ctime", ctime
        );
}


BUILTIN_FUNCTION(os_fstat)
{
        ASSERT_ARGC("os.fstat()", 1);
        StatStruct s;
#ifdef _WIN32
        return xstatv(ty, _fstat64(INT_ARG(0), &s), &s);
#else
        return xstatv(ty, fstat(INT_ARG(0), &s), &s);
#endif
}

BUILTIN_FUNCTION(os_lstat)
{
#ifdef _WIN32
        NOT_ON_WINDOWS("os.lstat()");
#else
        ASSERT_ARGC("os.lstat()", 1);
        StatStruct s;
        char const *path = TY_TMP_C_STR(ARGx(0, VALUE_STRING));
        return xstatv(ty, lstat(path, &s), &s);
#endif
}

BUILTIN_FUNCTION(os_stat)
{
        ASSERT_ARGC("os.stat()", 1);
        StatStruct s;
        char const *path = TY_TMP_C_STR(ARGx(0, VALUE_STRING));
#ifdef _WIN32
        return xstatv(ty, _stat64(path, &s), &s);
#else
        return xstatv(ty, stat(path, &s), &s);
#endif
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
        int fd = INT_ARG(0);
        int op = INT_ARG(1);
        return INTEGER(lock_file(fd, op));
}

BUILTIN_FUNCTION(os_fcntl)
{
        ASSERT_ARGC("os.fcntl()", 2, 3);
#ifdef _WIN32
        NOT_ON_WINDOWS("os.fcntl()")
#else

        int fd = INT_ARG(0);
        int op = INT_ARG(1);

        if (argc == 2) {
                return INTEGER(fcntl(fd, op));
        }

        switch (op) {
        default:
        case F_DUPFD:
        case F_SETFD:
        case F_SETFL:
        case F_SETOWN:
#ifdef __APPLE__
        case F_DUPFD_CLOEXEC:
#else
        case F_SETSIG:
#endif
                return INTEGER(fcntl(fd, op, (int)INT_ARG(2)));
        }

        bP("operation not implemented");
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
        ASSERT_ARGC("os.isatty()", 1);
        return INTEGER(isatty(INT_ARG(0)));
}

BUILTIN_FUNCTION(os_ttyname)
{
        ASSERT_ARGC("os.ttyname()", 1);
        int fd = INT_ARG(0);
        char *name = TY_TMP();
        int ret = ttyname_r(fd, name, TY_TMP_N);
        if (ret != 0) {
                errno = ret;
                return NIL;
        }
        return vSsz(name);
}

BUILTIN_FUNCTION(os_terminal_size)
{
        ASSERT_ARGC("os.terminal-size()", 0, 1);

        int rows;
        int cols;
        bool ok;

        if (argc == 0) {
                ok = get_terminal_size(-1, &rows, &cols);
        } else {
                ok = get_terminal_size(INT_ARG(0), &rows, &cols);
        }

        return !ok ? NIL : vTn(
                "rows", INTEGER(rows),
                "cols", INTEGER(cols)
        );
}


BUILTIN_FUNCTION(termios_tcgetattr)
{
        ASSERT_ARGC("termios.tcgetattr()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcgetattr()");
#else
        struct termios t;

        if (tcgetattr(INT_ARG(0), &t) != 0) {
                return NIL;
        }

        Blob *cc = value_blob_new(ty);
        NOGC(cc);

        for (int i = 0; i < sizeof t.c_cc; ++i) {
                uvP(*cc, t.c_cc[i]);
        }

        Value v = vTn(
                "iflag",  INTEGER(t.c_iflag),
                "oflag",  INTEGER(t.c_oflag),
                "cflag",  INTEGER(t.c_cflag),
                "lflag",  INTEGER(t.c_lflag),
                "ispeed", INTEGER(t.c_ispeed),
                "ospeed", INTEGER(t.c_ospeed),
                "cc",     BLOB(cc)
        );

        OKGC(cc);

        return v;
#endif
}

BUILTIN_FUNCTION(termios_tcsetattr)
{
        ASSERT_ARGC("termios.tcsetattr()", 3);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcsetattr()");
#else
        if (ARG(0).type != VALUE_INTEGER) {
                zP("termios.tcsetattr(): expected integer but got: %s", VSC(&ARG(0)));
        }

        struct termios t;

        int fd    = INT_ARG(0);
        int flags = INT_ARG(1);

        if (tcgetattr(fd, &t) != 0) {
                return BOOLEAN(false);
        }

        Value attrs = ARGx(2, VALUE_TUPLE);

        Value *iflag  = tuple_get(&attrs, "iflag");
        Value *oflag  = tuple_get(&attrs, "oflag");
        Value *cflag  = tuple_get(&attrs, "cflag");
        Value *lflag  = tuple_get(&attrs, "lflag");
        Value *ispeed = tuple_get(&attrs, "ispeed");
        Value *ospeed = tuple_get(&attrs, "ospeed");
        Value *cc     = tuple_get(&attrs, "cc");

        if (iflag  != NULL && iflag->type  == VALUE_INTEGER) { t.c_iflag  = iflag->z; }
        if (oflag  != NULL && oflag->type  == VALUE_INTEGER) { t.c_oflag  = oflag->z; }
        if (cflag  != NULL && cflag->type  == VALUE_INTEGER) { t.c_cflag  = cflag->z; }
        if (lflag  != NULL && lflag->type  == VALUE_INTEGER) { t.c_lflag  = lflag->z; }
        if (ispeed != NULL && ispeed->type == VALUE_INTEGER) { t.c_ispeed = ispeed->z; }
        if (ospeed != NULL && ospeed->type == VALUE_INTEGER) { t.c_ospeed = ospeed->z; }

        if (cc != NULL && cc->type == VALUE_BLOB) {
                for (int i = 0; i < min(vN(*cc->blob), sizeof t.c_cc); ++i) {
                        t.c_cc[i] = v__(*cc->blob, i);
                }
        }

        return BOOLEAN(tcsetattr(fd, flags, &t) == 0);
#endif
}

BUILTIN_FUNCTION(termios_tcgetsid)
{
        ASSERT_ARGC("termios.tcgetsid()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.getsid()");
#else
        return INTEGER(tcgetsid(INT_ARG(0)));
#endif
}

BUILTIN_FUNCTION(termios_tcgetpgrp)
{
        ASSERT_ARGC("termios.tcgetpgrp()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcgetpgrp()");
#else
        return INTEGER(tcgetpgrp(INT_ARG(0)));
#endif
}

BUILTIN_FUNCTION(termios_tcsetpgrp)
{
        ASSERT_ARGC("termios.tcsetpgrp()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcsetpgrp()");
#else
        int fd = INT_ARG(0);
        pid_t pgrp = INT_ARG(1);
        return INTEGER(tcsetpgrp(fd, pgrp));
#endif
}

BUILTIN_FUNCTION(termios_tcsendbreak)
{
        ASSERT_ARGC("termios.tcsendbreak()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcsendbreak()");
#else
        int fd = INT_ARG(0);
        int duration = INT_ARG(1);
        return INTEGER(tcsendbreak(fd, duration));
#endif
}

BUILTIN_FUNCTION(termios_tcdrain)
{
        ASSERT_ARGC("termios.tcdrain()", 1);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcdrain()");
#else
        int fd = INT_ARG(0);
        return INTEGER(tcdrain(fd));
#endif
}

BUILTIN_FUNCTION(termios_tcflush)
{
        ASSERT_ARGC("termios.tcflush()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcflush()");
#else
        int fd = INT_ARG(0);
        int action = INT_ARG(1);
        return INTEGER(tcflush(fd, action));
#endif
}

BUILTIN_FUNCTION(termios_tcflow)
{
        ASSERT_ARGC("termios.tcflow()", 2);
#ifdef _WIN32
        NOT_ON_WINDOWS("termios.tcflow()");
#else
        int fd = INT_ARG(0);
        int action = INT_ARG(1);
        return INTEGER(tcflow(fd, action));
#endif
}

BUILTIN_FUNCTION(errno_get)
{
        ASSERT_ARGC("errno.get()", 0);
        return INTEGER(errno);
}

BUILTIN_FUNCTION(errno_str)
{
        ASSERT_ARGC_2("ss(errno)()", 0, 1);

        int e;

        if (argc == 0) {
                e = errno;
        } else {
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the argument to ss(errno)() must be an integer");
                e = ARG(0).z;
        }

        char const *s = strerror(e);

        return vSs(s, strlen(s));
}

BUILTIN_FUNCTION(time_gettime)
{
        ASSERT_ARGC_2("time.gettime()", 0, 1);

        clockid_t clk;
        if (argc == 1) {
                Value v = ARG(0);
                if (v.type != VALUE_INTEGER)
                        zP("the argument to time.gettime() must be an integer");
                clk = v.z;
        } else {
                clk = CLOCK_REALTIME;
        }

        struct timespec t = {0};
        clock_gettime(clk, &t);

        return timespec_tuple(ty, &t);
}

BUILTIN_FUNCTION(time_now)
{
        struct timespec t;
#ifdef _WIN32
        ASSERT_ARGC("time.now()", 0);
        GetCurrentTimespec(&t);
#else
        ASSERT_ARGC("time.now()", 0);
        clock_gettime(CLOCK_MONOTONIC, &t);
#endif
        i64 nsec = TY_1e9*t.tv_sec + (i64)t.tv_nsec;
        return REAL(nsec / 1.0e9);
}

BUILTIN_FUNCTION(time_utc)
{
        ASSERT_ARGC("time.utc()", 0);

        struct timespec t;
        i64 nsec;

        GetCurrentTimespec(&t);
        nsec = TY_1e9*t.tv_sec + (i64)t.tv_nsec;

        return REAL(nsec / 1.0e9);
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
                Value v = ARG(0);
                if (v.type != VALUE_INTEGER)
                        zP("the argument to time.utime() must be an integer");
                clk = v.z;
        } else {
                clk = CLOCK_REALTIME;
        }

        clock_gettime(clk, &t);
#endif
        return INTEGER((u64)t.tv_sec * 1000 * 1000 + (u64)t.tv_nsec / 1000);
}

BUILTIN_FUNCTION(time_localtime)
{
        ASSERT_ARGC_2("time.localtime()", 0, 1);

        time_t t;

        if (argc == 1) {
                Value v = ARG(0);
                if (v.type != VALUE_INTEGER) {
                        zP("the argument to time.localtime() must be an integer");
                }
                t = v.z;
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
                Value v = ARG(0);
                if (v.type != VALUE_INTEGER) {
                        zP("the argument to time.gmtime() must be an integer");
                }
                t = v.z;
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
        ASSERT_ARGC("time.strftime()", 1, 2);

        struct tm t = {0};

        Value fmt = ARGx(0, VALUE_STRING);

        if (argc == 2) {
                Value v = ARG(1);
                if (v.type == VALUE_INTEGER) {
                        time_t sec = v.z;
                        localtime_r(&sec, &t);
                } else if (v.type == VALUE_TUPLE) {
                        Value *vp;
                        if ((vp = tget_t(&v, "sec", VALUE_INTEGER)) != NULL)
                                t.tm_sec = vp->z;
                        if ((vp = tget_t(&v, "min", VALUE_INTEGER)) != NULL)
                                t.tm_min = vp->z;
                        if ((vp = tget_t(&v, "hour", VALUE_INTEGER)) != NULL)
                                t.tm_hour = vp->z;
                        if ((vp = tget_t(&v, "mday", VALUE_INTEGER)) != NULL)
                                t.tm_mday = vp->z;
                        if ((vp = tget_t(&v, "mon", VALUE_INTEGER)) != NULL)
                                t.tm_mon = vp->z;
                        if ((vp = tget_t(&v, "year", VALUE_INTEGER)) != NULL)
                                t.tm_year = vp->z;
                        if ((vp = tget_t(&v, "wday", VALUE_INTEGER)) != NULL)
                                t.tm_wday = vp->z;
                        if ((vp = tget_t(&v, "yday", VALUE_INTEGER)) != NULL)
                                t.tm_yday = vp->z;
                        if ((vp = tget_t(&v, "isdst", VALUE_INTEGER)) != NULL)
                                t.tm_isdst = vp->boolean;

                } else {
                        ARGx(1, VALUE_INTEGER, VALUE_TUPLE);
                        UNREACHABLE();
                }
        } else {
                time_t sec = time(NULL);
                localtime_r(&sec, &t);
        }

        char *tmp = TY_TMP();
        int n = strftime(tmp, TY_TMP_N, TY_TMP_C_STR_B(fmt), &t);

        if (n > 0) {
                return vSs(tmp, n);
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

        Value s = ARG(0);
        Value fmt = ARG(1);

        if (s.type != VALUE_STRING || fmt.type != VALUE_STRING) {
                zP("both arguments to time.strptime() must be strings");
        }

        B.count = 0;

        xvPn(B, ss(s), sN(s));
        xvP(B, '\0');

        xvPn(B, ss(fmt), sN(fmt));
        xvP(B, '\0');

        char const *sp = B.items;
        char const *fp = B.items + sN(s) + 1;

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
        Value v = ARG(0);

        if (v.type != VALUE_TUPLE) {
                zP("the argument to time.time() must be a named tuple");
        }

        Value *vp;

        if ((vp = tuple_get(&v, "sec")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_sec = vp->z;
        if ((vp = tuple_get(&v, "min")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_min = vp->z;
        if ((vp = tuple_get(&v, "hour")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_hour = vp->z;
        if ((vp = tuple_get(&v, "mday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_mday = vp->z;
        if ((vp = tuple_get(&v, "mon")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_mon = vp->z;
        if ((vp = tuple_get(&v, "year")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_year = vp->z;
        if ((vp = tuple_get(&v, "wday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_wday = vp->z;
        if ((vp = tuple_get(&v, "yday")) != NULL && vp->type == VALUE_INTEGER)
                t.tm_yday = vp->z;
        if ((vp = tuple_get(&v, "isdst")) != NULL && vp->type == VALUE_BOOLEAN)
                t.tm_isdst = vp->boolean;

        Value *utc = NAMED("utc");

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

        Value fd = ARG(0);
        if (fd.type != VALUE_INTEGER)
                zP("the first argument to stdio.fdopen() must be an integer");

        char mode[16] = "a+";
        if (argc == 2) {
                Value m = ARG(1);
                if (m.type != VALUE_STRING)
                        zP("the second argument to stdio.fdopen() must be a string");
                if (sN(m) >= sizeof mode)
                        zP("invalid mode string %s passed to stdio.fdopen()", VSC(&m));
                memcpy(mode, ss(m), sN(m));
                mode[sN(m)] = '\0';
        }

        FILE *f = fdopen(fd.z, mode);
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

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fgets() must be a pointer");

        FILE *fp = f.ptr;

        B.count = 0;

        int c;

        lGv(true);
        while ((c = fgetc(fp)) != EOF && c != '\n') {
                xvP(B, c);
        }
        lTk();

        if (B.count == 0 && c == EOF)
                return NIL;

        Value s;

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

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readSigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected integer as second argument to stdio.readSigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).z;
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

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeSigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        Value x;

        if (argc == 3) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected integer as second argument to stdio.writeSigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).z;
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
        case (sizeof (char)):      memcpy(b, &(char)     {x.z}, size); break;
        case (sizeof (short)):     memcpy(b, &(short)    {x.z}, size); break;
        case (sizeof (int)):       memcpy(b, &(int)      {x.z}, size); break;
        case (sizeof (long long)): memcpy(b, &(long long){x.z}, size); break;
        default: return BOOLEAN(false);
        }

        lGv(true);
        size_t n = fwrite(b, size, 1, fp);
        lTk();

        return BOOLEAN(n == 1);
}

BUILTIN_FUNCTION(stdio_read_unsigned)
{
        ASSERT_ARGC_2("stdio.readUnsigned()", 1, 2);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readUnsigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        if (argc == 2) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected integer as second argument to stdio.readUnsigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).z;
        } else {
                size = sizeof size;
        }

        uintmax_t k = 0;

        if (fread(&k, min(size, sizeof k), 1, fp) != 1) {
                return NIL;
        } else {
                return INTEGER(k);
        }
}

BUILTIN_FUNCTION(stdio_write_unsigned)
{
        ASSERT_ARGC_2("stdio.writeUnsigned()", 2, 3);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeUnsigned() must be a pointer");

        FILE *fp = f.ptr;

        int size;
        Value x;

        if (argc == 3) {
                if (ARG(1).type != VALUE_INTEGER) {
                        zP("expected integer as second argument to stdio.writeUnsigned() but got: %s", VSC(&ARG(1)));
                }
                size = ARG(1).z;
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
        case (sizeof (unsigned char)):      memcpy(b, &(unsigned char)     {x.z}, size); break;
        case (sizeof (unsigned short)):     memcpy(b, &(unsigned short)    {x.z}, size); break;
        case (sizeof (unsigned int)):       memcpy(b, &(unsigned int)      {x.z}, size); break;
        case (sizeof (unsigned long long)): memcpy(b, &(unsigned long long){x.z}, size); break;
        default: return BOOLEAN(false);
        }

        lGv(true);
        size_t n = fwrite(b, size, 1, fp);
        lTk();

        return BOOLEAN(n == 1);
}

BUILTIN_FUNCTION(stdio_read_double)
{
        ASSERT_ARGC("stdio.readDouble()", 1);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readDouble() must be a pointer");

        double x;
        FILE *fp = f.ptr;

        lGv(true);

        if (fread(&x, sizeof x, 1, fp) == 1) {
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

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.readFloat() must be a pointer");

        float x;
        FILE *fp = f.ptr;

        lGv(true);

        if (fread(&x, sizeof x, 1, fp) == 1) {
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

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeFloat() must be a pointer");

        Value x = ARG(1);
        if (x.type != VALUE_REAL)
                zP("the second argument to stdio.writeFloat() must be a float");

        FILE *fp = f.ptr;
        float fx = (float)x.real;

        lGv(true);
        size_t n = fwrite(&fx, sizeof fx, 1, fp);
        lTk();

        return BOOLEAN(n > 0);
}

BUILTIN_FUNCTION(stdio_write_double)
{
        ASSERT_ARGC("stdio.writeDouble()", 2);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.writeDouble() must be a pointer");

        Value x = ARG(1);
        if (x.type != VALUE_REAL)
                zP("the second argument to stdio.writeDouble() must be a float");

        FILE *fp = f.ptr;
        double fx = x.real;

        lGv(true);
        size_t n = fwrite(&fx, sizeof fx, 1, fp);
        lTk();

        return BOOLEAN(n > 0);
}

BUILTIN_FUNCTION(stdio_fread)
{
        ASSERT_ARGC("stdio.fread()", 2, 3);

        Value f = ARGx(0, VALUE_PTR);

        Value n = ARGx(1, VALUE_INTEGER);
        if (n.z < 0) {
                bP("got negative count: %"PRIiMAX, n.z);
        }

        Blob *b;
        bool existing_blob = (argc == 3) && ARG(2).type != VALUE_NIL;

        if (existing_blob) {
                b = ARGx(2, VALUE_BLOB).blob;
        } else {
                b = value_blob_new(ty);
        }

        NOGC(b);

        FILE *fp = f.ptr;
        intmax_t bytes = 0;
        int c;

        lGv(true);
        while (bytes < n.z && (c = fgetc(fp)) != EOF) {
                uvP(*b, c);
                bytes += 1;
        }
        lTk();

        OKGC(b);

        if (existing_blob) {
                return INTEGER(bytes);
        } else {
                if (b->count == 0 && n.z > 0 && c == EOF)
                        return NIL;

                return BLOB(b);
        }
}

BUILTIN_FUNCTION(stdio_slurp)
{
        ASSERT_ARGC("stdio.slurp()", 1);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.slurp() must be a pointer");

        FILE *fp = f.ptr;
        int c;

        B.count = 0;

        lGv(true);
        while ((c = fgetc(fp)) != EOF) {
                xvP(B, c);
        }
        lTk();

        if (c == EOF && B.count == 0)
                return NIL;

        Value s = vSs(B.items, B.count);

        return s;
}

BUILTIN_FUNCTION(stdio_fgetc)
{
        ASSERT_ARGC("stdio.fgetc()", 1);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.fgetc() must be a pointer");

        lGv(true);
        int c = fgetc(f.ptr);
        lTk();

        return (c == EOF) ? NIL : INTEGER(c);
}

BUILTIN_FUNCTION(stdio_fputc)
{
        ASSERT_ARGC("stdio.fputc()", 2);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the first argument to stdio.fputc() must be a pointer");

        if (ARG(1).type != VALUE_INTEGER) {
                zP("the second argument to stdio.fputc() must be an integer");
        }

        lGv(true);
        int c = fputc((int)ARG(1).z, f.ptr);
        lTk();

        return (c == EOF) ? NIL : INTEGER(c);
}

BUILTIN_FUNCTION(stdio_fwrite)
{
        ASSERT_ARGC("stdio.fwrite()", 2, 3);

        FILE *f = PTR_ARG(0);
        Value data = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_PTR, VALUE_INTEGER);
        usize len;

        isize ret;

        lGv(true);
        switch (data.type) {
        case VALUE_STRING:
                len = (argc == 3) ? INT_ARG(2) : sN(data);
                ret = fwrite(ss(data), 1, len, f);
                break;

        case VALUE_BLOB:
                len = (argc == 3) ? INT_ARG(2) : vN(*data.blob);
                ret = fwrite(vv(*data.blob), 1, vN(*data.blob), f);
                break;

        case VALUE_PTR:
                len = (argc == 3) ? INT_ARG(2) : strlen(data.ptr);
                ret = fwrite(data.ptr, 1, 1, f);
                break;

        case VALUE_INTEGER:
                len = (argc == 3) ? INT_ARG(2) : 1;
                ret = 0;
                for (usize i = 0; i < len; ++i) {
                        if (fputc((unsigned char)data.z, f) == EOF) {
                                ret = -1;
                                break;
                        }
                        ret += 1;
                }
                break;

        default:
                UNREACHABLE();
        }
        lTk();

        return INTEGER(ret);
}

BUILTIN_FUNCTION(stdio_puts)
{
        ASSERT_ARGC("stdio.puts()", 2);

        Value f = ARG(0);
        if (f.type != VALUE_PTR)
                zP("the argument to stdio.puts() must be a pointer");

        Value s = ARG(1);

        errno = 0;
        usize r;

        switch (s.type) {
        case VALUE_STRING:
                r = fwrite(ss(s), 1, sN(s), f.ptr);
                if (r < sN(s) && errno != 0)
                        return NIL;
                break;
        case VALUE_BLOB:
                r = fwrite(s.blob->items, 1, s.blob->count, f.ptr);
                if (r < s.blob->count && errno != 0)
                        return NIL;
                break;
        default:
                zP("the second argument to stdio.puts() must be a string or a blob");
        }

        if (fputc('\n', f.ptr) == EOF)
                return NIL;

        return INTEGER(r + 1);
}

BUILTIN_FUNCTION(stdio_fflush)
{
        ASSERT_ARGC("stdio.fflush()", 1);
        return (fflush(PTR_ARG(0)) == EOF) ? NIL : INTEGER(0);
}

BUILTIN_FUNCTION(stdio_fclose)
{
        ASSERT_ARGC("stdio.fclose()", 1);
        return (fclose(PTR_ARG(0)) == EOF) ? NIL : INTEGER(0);
}

BUILTIN_FUNCTION(stdio_clearerr)
{
        ASSERT_ARGC("stdio.clearerr()", 1);
        clearerr(PTR_ARG(0));
        return NIL;
}

BUILTIN_FUNCTION(stdio_setvbuf)
{
        ASSERT_ARGC("stdio.setvbuf()", 2);
        return INTEGER(setvbuf(PTR_ARG(0), NULL, INT_ARG(1), 0));
}

BUILTIN_FUNCTION(stdio_ftell)
{
        ASSERT_ARGC("stdio.ftell()", 1);
        return INTEGER(ftell(PTR_ARG(0)));
}

BUILTIN_FUNCTION(stdio_fseek)
{
        ASSERT_ARGC("stdio.fseek()", 3);

        FILE *fp     = PTR_ARG(0);
        i64   off    = INT_ARG(1);
        i32   whence = INT_ARG(2);

        return INTEGER(fseek(fp, off, whence));
}

BUILTIN_FUNCTION(object)
{
        ASSERT_ARGC("object()", 1, 2);

        Value obj;

        if (argc == 1) {
                Value class = ARGx(0, VALUE_CLASS);
                obj = NewInstance(class.class);
        } else {
                Value class = ARGx(0, VALUE_CLASS);
                Value old   = ARGx(1, VALUE_OBJECT);
                obj = OBJECT(old.object, class.class);
        }

        return obj;
}

BUILTIN_FUNCTION(bind)
{
        ASSERT_ARGC("bindMethod()", 2);

        Value f = ARG(0);
        Value x = ARG(1);

        Value *this;

        if (f.type == VALUE_METHOD) {
                this = mAo(sizeof x, GC_VALUE);
                *this = x;
                return METHOD(f.name, f.method, this);
        }

        if (
                (f.type == VALUE_FUNCTION)
             && (class_of(&f) != -1)
        ){
                this = mAo(2 * sizeof (Value), GC_VALUE);
                this[0] = x;
                this[1] = f;
                return METHOD(M_ID(name_of(&f)), &this[1], &this[0]);
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

        Value class = ARGx(0, VALUE_CLASS);
        Value name = ARGx(1, VALUE_STRING);
        Value f = ARGx(2, VALUE_FUNCTION);

        class_add_method(ty, class.class, TY_C_STR(name), f);

        return NIL;
}

BUILTIN_FUNCTION(apply)
{
        char const *_name__ = "apply()";

        if (argc == 0) {
                bP("called with no arguments");
        }

        Value fun0  = ARG(0);
        Value *self = NAMED("self");
        Value *kws  = NAMED("kwargs");

        Value fun;
        if (self != NULL && fun0.type == VALUE_METHOD) {
                fun = METHOD(fun0.name, &fun0, self);
        } else {
                fun = fun0;
        }

        for (int i = 1; i < argc; ++i) {
                vmP(&ARG(1));
        }

        return vm_call_ex(
                ty,
                &fun,
                argc - 1,
                kws,
                HAVE_FLAG("collect")
        );
}

BUILTIN_FUNCTION(type)
{
        ASSERT_ARGC("type()", 1);

        Value v = ARG(0);

        if (v.type == VALUE_TUPLE) {
                int n = v.count;

                if (n == 0) {
                        return v;
                }

                Value *types = mAo(n * sizeof (Value), GC_TUPLE);

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
        case VALUE_INTEGER:  return (Value) { .type = VALUE_CLASS, .class = CLASS_INT     };
        case VALUE_REAL:     return (Value) { .type = VALUE_CLASS, .class = CLASS_FLOAT   };
        case VALUE_STRING:   return (Value) { .type = VALUE_CLASS, .class = CLASS_STRING  };
        case VALUE_ARRAY:    return (Value) { .type = VALUE_CLASS, .class = CLASS_ARRAY   };
        case VALUE_DICT:     return (Value) { .type = VALUE_CLASS, .class = CLASS_DICT    };
        case VALUE_BLOB:     return (Value) { .type = VALUE_CLASS, .class = CLASS_BLOB    };
        case VALUE_OBJECT:   return (Value) { .type = VALUE_CLASS, .class = v.class       };
        case VALUE_BOOLEAN:  return (Value) { .type = VALUE_CLASS, .class = CLASS_BOOL    };
        case VALUE_REGEX:    return (Value) { .type = VALUE_CLASS, .class = CLASS_REGEX   };
        case VALUE_CLASS:    return (Value) { .type = VALUE_CLASS, .class = CLASS_CLASS   };
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_FOREIGN_FUNCTION:
        case VALUE_OPERATOR:
        case VALUE_FUNCTION:  return (Value) { .type = VALUE_CLASS, .class = CLASS_FUNCTION  };
        case VALUE_GENERATOR: return (Value) { .type = VALUE_CLASS, .class = CLASS_GENERATOR };
        case VALUE_TAG:       return (Value) { .type = VALUE_CLASS, .class = CLASS_TAG       };
        case VALUE_PTR:       return (Value) { .type = VALUE_CLASS, .class = CLASS_PTR       };
        default:
        case VALUE_NIL:      return NIL;
        }
}

BUILTIN_FUNCTION(subclass)
{
        ASSERT_ARGC("subclass?()", 2);

        Value sub   = ARGx(0, VALUE_CLASS);
        Value super = ARGx(1, VALUE_CLASS);

        return BOOLEAN(class_is_subclass(ty, sub.class, super.class));
}

BUILTIN_FUNCTION(members)
{
        ASSERT_ARGC("members()", 1);

        Value val = ARG(0);

        Dict *_members = dict_new(ty);
        Value members = DICT(_members);

        gP(&members);

        switch (val.type) {
        case VALUE_OBJECT:
                for (int i = 0; i < val.object->nslot; ++i) {
                        char const *key = M_NAME(v__(val.object->class->fields.ids, i));
                        dict_put_member(ty, _members, key, val.object->slots[i]);
                }
                if (val.object->dynamic != NULL) {
                        for (int i = 0; i < vN(val.object->dynamic->ids); ++i) {
                                char const *key = M_NAME(v__(val.object->dynamic->ids, i));
                                dict_put_member(ty, _members, key, v__(val.object->dynamic->values, i));
                        }
                }
                break;

        case VALUE_TUPLE:
                for (int i = 0; i < val.count; ++i) {
                        if (val.ids != NULL && val.ids[i] != -1) {
                                char const *key = M_NAME(val.ids[i]);
                                dict_put_member(ty, _members, key, val.items[i]);
                        } else {
                                dict_put_value(ty, _members, INTEGER(i), val.items[i]);
                        }
                }
                break;

        default:
                gX();
                return NIL;
        }

        gX();

        return members;
}

BUILTIN_FUNCTION(member)
{
        ASSERT_ARGC("member()", 2, 3);

        Value o = ARG(0);
        Value name = ARG(1);

        int id = M_ID(TY_TMP_C_STR(name));

        if (argc == 2) {
                Value v = GetMember(ty, o, id, false, true);
                return (v.type == VALUE_NONE) ? NIL : v;
        } else if (o.type == VALUE_OBJECT) {
                PutMember(o, id, ARG(2));
                return ARG(2);
        } else {
                bP("attempt to add member to non-object: %s", VSC(&o));
        }
}

BUILTIN_FUNCTION(finalizer)
{
        return NIL;
}

static Value
ffdoc(Ty *ty, Value const *ff)
{
        char const *_name;
        char const *_doc;
        char const *_proto;

        if (ff->xinfo == NULL) {
                _name  = NULL;
                _doc   = NULL;
                _proto = NULL;
        } else {
                _name  = ff->xinfo->name;
                _doc   = ff->xinfo->doc;
                _proto = ff->xinfo->proto;
        }

        GC_STOP();

        Value name  = (_name  == NULL) ? NIL : vSsz(_name);
        Value doc   = (_doc   == NULL) ? NIL : vSsz(_doc);
        Value proto = (_proto == NULL) ? NIL : vSsz(_proto);

        Value v = TRIPLE(name, proto, doc);

        GC_RESUME();

        return v;
}


static Value
fdoc(Ty *ty, Value const *f)
{
        char name_buf[512] = {0};

        char const *s = doc_of(f);
        char const *name = name_of(f);
        char const *proto = proto_of(f);

        GC_STOP();

        Value n;
        if (f->info[6] != -1) {
                snprintf(name_buf, sizeof name_buf, "%s.%s", class_name(ty, f->info[6]), name);
                n = vSs(name_buf, strlen(name_buf));
        } else if (name != NULL) {
                n = vSs(name, strlen(name));
        } else {
                n = NIL;
        }
        Value p = (proto == NULL) ? NIL : vSsz(proto);
        Value doc = (s == NULL) ? NIL : vSsz(s);

        Value v = TRIPLE(n, p, doc);

        GC_RESUME();

        return v;
}

static void
mdocs(Ty *ty, struct itable const *t, struct array *a)
{
        for (int i = 0; i < vN(t->values); ++i) {
                vAp(a, fdoc(ty, v_(t->values, i)));
        }
}

BUILTIN_FUNCTION(set_doc)
{
        ASSERT_ARGC("set-doc()", 1);

        Value f = ARGx(0, VALUE_FUNCTION, VALUE_FOREIGN_FUNCTION);

        Value *name  = NAMED("name");
        Value *proto = NAMED("proto");
        Value *doc   = NAMED("doc");

        if (f.xinfo == NULL) {
                f.xinfo = mAo0(sizeof (FunUserInfo), GC_ANY);
        }

        if (name != NULL && name->type != VALUE_NIL) {
                if (name->type != VALUE_STRING) {
                        zP("set-doc(): non-string passed as `name`: %s", VSC(name));
                }
                f.xinfo->name = TY_C_STR(*name);
        }

        if (proto != NULL && proto->type != VALUE_NIL) {
                if (proto->type != VALUE_STRING) {
                        zP("set-doc(): non-string passed as `proto`: %s", VSC(proto));
                }
                f.xinfo->proto = TY_C_STR(*proto);
        }

        if (doc != NULL && doc->type != VALUE_NIL) {
                if (doc->type != VALUE_STRING) {
                        zP("set-doc(): non-string passed as `doc`: %s", VSC(doc));
                }
                f.xinfo->doc = TY_C_STR(*doc);
        }

        return f;
}

BUILTIN_FUNCTION(doc)
{
        ASSERT_ARGC("doc()", 1, 2);

        switch (ARG(0).type) {
        case VALUE_FUNCTION:
                return fdoc(ty, &ARG(0));

        case VALUE_FOREIGN_FUNCTION:
                return ffdoc(ty, &ARG(0));

        case VALUE_CLASS:
        {
                GC_STOP();

                char const *s = class_doc(ty, ARG(0).class);
                char const *name = class_name(ty, ARG(0).class);
                Value v = vT(3);
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

        case VALUE_STRING:
                break;

        default:
                return NIL;
        }

        char const *id = TY_TMP_C_STR_A(ARG(0));
        char const *mod = (argc == 2)
                        ? TY_TMP_C_STR_B(ARGx(1, VALUE_STRING))
                        : NULL;

        Symbol *sym = compiler_lookup(ty, mod, id);

        if (sym == NULL || sym->doc == NULL) {
                return NIL;
        }

        return vSsz(sym->doc);
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

                Value const *f = FrameFun(ty, v_(*frames, i));

                if (is_hidden_fun(f)) {
                        continue;
                }

                char const *name = name_of(f);
                char const *ip = frames->items[i].ip;
                Expr const *e = compiler_find_expr(ty, ip - 1);

                Value entry = vT(5);

                entry.items[0] = *f;
                entry.items[1] = xSz(name);
                entry.items[2] = (e == NULL || e->mod == NULL) ? NIL : xSz(e->mod->path);
                entry.items[3] = (e == NULL) ? NIL : INTEGER(e->start.line);
                entry.items[4] = (e == NULL) ? NIL : INTEGER(e->start.col);

                vAp(avFrames, entry);
        }

        GC_RESUME();

        return ARRAY(avFrames);
}

BUILTIN_FUNCTION(ty_trace)
{
        ASSERT_ARGC("ty.trace()", 0);

        if (vN(ty->throw_stack) == 0) {
                return NIL;
        }

        ThrowCtx *ctx = v_L(ty->throw_stack);
        ThrowCtx *clone = mAo0(sizeof (ThrowCtx), GC_ANY);

        for (int i = 0; i < vN(*ctx); ++i) {
                xvP(*clone, v__(*ctx, i));
                if (DetailedExceptions) {
                        ValueVector locals = {0};
                        ValueVector *_locals = v_(ctx->locals, i);
                        xvPv(locals, *_locals);
                        xvP(clone->locals, locals);
                }
        }

        return TRACE(clone);
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
        ASSERT_ARGC("ty.gensym()", 0);
        return xSz(gensym(ty));
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
        char const *type = NULL;
        char const *tag  = NULL;

        Value start = make_location(ty, &t->start);
        Value end = make_location(ty, &t->end);

        switch (t->tag) {
        case TT_FIELD:     tag = "field";     break;
        case TT_TYPE:      tag = "type";      break;
        case TT_MACRO:     tag = "macro";     break;
        case TT_MEMBER:    tag = "member";    break;
        case TT_FUNC:      tag = "func";      break;
        case TT_MODULE:    tag = "module";    break;
        case TT_KEYWORD:   tag = "keyword";   break;
        case TT_PARAM:     tag = "param";     break;
        case TT_PUNCT:     tag = "punct";     break;
        case TT_CALL:      tag = "call";      break;
        case TT_OPERATOR:  tag = "operator";  break;
        default:                              break;
        }

        Value meta = (tag == NULL) ? NIL : xSz(tag);

#define T(name) (STRING_NOGC(#name, strlen(#name)))
        switch (t->type) {
        case TOKEN_IDENTIFIER:
                return vTn(
                        "type",   T(id),
                        "meta",   meta,
                        "start",  start,
                        "end",    end,
                        "id",     vSsz(t->identifier),
                        "module", (t->module == NULL) ? NIL : vSsz(t->module)
                );

        case TOKEN_INTEGER:
                return vTn(
                        "type",   T(int),
                        "meta",   meta,
                        "start",  start,
                        "end",    end,
                        "int",    INTEGER(t->integer)
                );

        case TOKEN_REAL:
                return vTn(
                        "type",   T(float),
                        "meta",   meta,
                        "start",  start,
                        "end",    end,
                        "float",  REAL(t->real)
                );

        case TOKEN_STRING:
                return vTn(
                        "type",   T(string),
                        "start",  start,
                        "end",    end,
                        "str",    vSsz(t->string)
                );

        case TOKEN_COMMENT:
                return vTn(
                        "type",    T(comment),
                        "start",   start,
                        "end",     end,
                        "comment", vSsz(t->comment)
                );

        case TOKEN_END:
                return NIL;

        case TOKEN_AND:             type = "&&";   break;
        case TOKEN_AND_EQ:          type = "&=";   break;
        case TOKEN_ARROW:           type = "->";   break;
        case TOKEN_AT:              type = "@";    break;
        case TOKEN_BANG:            type = "!";    break;
        case TOKEN_CHECK_MATCH:     type = "::";   break;
        case TOKEN_CMP:             type = "<=>";  break;
        case TOKEN_DBL_EQ:          type = "==";   break;
        case TOKEN_DEC:             type = "--";   break;
        case TOKEN_DIV_EQ:          type = "/=";   break;
        case TOKEN_DOT_DOT:         type = "..";   break;
        case TOKEN_DOT_DOT_DOT:     type = "...";  break;
        case TOKEN_DOT_MAYBE:       type = ".?";   break;
        case TOKEN_EQ:              type = "=";    break;
        case TOKEN_FAT_ARROW:       type = "=>";   break;
        case TOKEN_GEQ:             type = ">=";   break;
        case TOKEN_GT:              type = ">";    break;
        case TOKEN_INC:             type = "++";   break;
        case TOKEN_LEQ:             type = "<=";   break;
        case TOKEN_LT:              type = "<";    break;
        case TOKEN_MINUS_EQ:        type = "-=";   break;
        case TOKEN_MOD_EQ:          type = "%=";   break;
        case TOKEN_NOT_EQ:          type = "!=";   break;
        case TOKEN_OR:              type = "||";   break;
        case TOKEN_OR_EQ:           type = "|=";   break;
        case TOKEN_PLUS_EQ:         type = "+=";   break;
        case TOKEN_SHL:             type = "<<";   break;
        case TOKEN_SHL_EQ:          type = "<<=";  break;
        case TOKEN_SHR:             type = ">>";   break;
        case TOKEN_SHR_EQ:          type = ">>=";  break;
        case TOKEN_SQUIGGLY_ARROW:  type = "~>";   break;
        case TOKEN_STAR_EQ:         type = "*=";   break;
        case TOKEN_WTF:             type = "??";   break;
        case TOKEN_XOR_EQ:          type = "^=";   break;

        case TOKEN_TEMPLATE_BEGIN:
                type = "$$[";
                break;

        case TOKEN_TEMPLATE_END:
                type = "$$]";
                break;

        case '$$':
                type = "$$";
                break;

        case '$~>':
                type = "$~>";
                break;

        case TOKEN_KEYWORD:
                type = keyword_show(t->keyword);
                break;

        case TOKEN_SPECIAL_STRING:
        case TOKEN_FUN_SPECIAL_STRING:
                type = "f-string";
                break;

        case TOKEN_NEWLINE:
                type = "\\n";
                break;

        case TOKEN_DIRECTIVE:
                type = "pp";
                break;

        case TOKEN_REGEX:
                type = "regex";
                break;

        case TOKEN_USER_OP:
                type = intern(&xD.b_ops, t->operator)->name;
                break;
        }

#undef T

        int tlen;
        if (type == NULL) {
                char const *charset = "[](){}<>;:.,?`~=!@#$%^&*/()-_~+|\"\\\n";
                if ((type = strchr(charset, t->type)) == NULL) {
                        tlen = 0;
                } else {
                        tlen = 1;
                }
        } else {
                tlen = strlen(type);
        }

        return vTn(
                "type",   xSs(type, tlen),
                "meta",   meta,
                "start",  start,
                "end",    end
        );
}

static Value
make_tokens(Ty *ty, TokenVector const *ts)
{
        Array *a = vA();

        GC_STOP();

        for (isize i = 0; i < vN(*ts); ++i) {
                if (v_(*ts, i)->ctx != LEX_FAKE) {
                        vAp(a, make_token(ty, v_(*ts, i)));
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

        Module *mod;

        char *tmp = TY_TMP();

        switch (what.type) {
        case VALUE_STRING:
                xvP(B, '\0');
                xvPn(B, ss(what), sN(what));
                xvP(B, '\0');

                name = "(eval)";
                mod = compiler_compile_source(ty, B.items + 1, name);
                end = NULL;

                if (mod == NULL || mod->code == NULL) {
                        snprintf(tmp, TY_TMP_N, "%s", TyError(ty));
                        bP("%s", tmp);
                }

                code = mod->code;
                break;

        if (0) {
        case VALUE_GENERATOR:
                what = what.gen->f;
        }
        if (0) {
        case VALUE_METHOD:
                what = *what.method;
        }
        case VALUE_FUNCTION:
                if (class_of(&what) != -1) {
                        snprintf(
                                tmp,
                                TY_TMP_N,
                                "%s.%s%s",
                                class_name(ty, class_of(&what)),
                                name_of(&what),
                                proto_of(&what)
                        );
                } else {
                        snprintf(
                                tmp,
                                TY_TMP_N,
                                "%s%s",
                                name_of(&what),
                                proto_of(&what)
                        );
                }

                name = tmp;
                code = code_of(&what);
                end = code + code_size_of(&what);
                break;

        default:
                bP("I don't know how to disassemble that yet :( %s", VSC(&what));
        }

        byte_vector text = {0};
        DumpProgram(ty, &text, name, code, end, true);

        Value result = vSs(vv(text), vN(text));

        xvF(text);

        return result;
}

BUILTIN_FUNCTION(ty_coro)
{
        return TyActiveGenerator(ty);
}

BUILTIN_FUNCTION(eval)
{
        ASSERT_ARGC("ty.eval()", 1, 2);

        Scope *scope = (argc == 2) ? PTR_ARG(1) : NULL;

        if (ARG(0).type == VALUE_STRING) {
                B.count = 0;
                xvP(B, '\0');
                xvPn(B, EVAL_PROLOGUE, countof(EVAL_PROLOGUE) - 1);
                xvPn(B, ss(ARG(0)), sN(ARG(0)));
                xvPn(B, EVAL_EPILOGUE, countof(EVAL_EPILOGUE));
                Arena old = NewArena(1 << 26);
                Stmt **prog = parse(ty, vv(B) + 1, "(eval)");

                if (prog == NULL) {
                        char const *msg = TyError(ty);
                        Value e = Err(ty, vSsz(msg));
                        ReleaseArena(old);
                        vmE(&e);
                }

                Expr *e = (Expr *)prog[0];

                if (!compiler_symbolize_expression(ty, e, scope)) {
                        char const *msg = TyError(ty);
                        Value e = Err(ty, vSsz(msg));
                        ReleaseArena(old);
                        vmE(&e);
                }

                Value v;

                if (!tyeval(ty, e, &v)) {
                        ReleaseArena(old);
                        vmE(&v);
                }

                ReleaseArena(old);

                return v;
        } else {
                compiler_clear_location(ty);

                Value prog = ARG(0);
                Expr *expr = TyToCExpr(ty, &prog);
                if (
                        (expr == NULL)
                     || !compiler_symbolize_expression(ty, expr, scope)
                ) {
                        bP("%s", sfmt("%s", TyError(ty)));
                }

                Value v;

                if (!tyeval(ty, expr, &v)) {
                        vmE(&v);
                }

                return v;
        }
}

BUILTIN_FUNCTION(ty_text)
{
        char const *_name__ = "ty.text()";
        CHECK_ARGC(1);

        Value mod = ARGx(0, VALUE_STRING);
        char const *source = CompilerGetModuleSource(ty, TY_TMP_C_STR(mod));

        return (source != NULL) ? xSz(source) : NIL;
}

BUILTIN_FUNCTION(ty_tokens)
{
        char const *_name__ = "ty.tokens()";
        CHECK_ARGC(1);

        Value mod = ARGx(0, VALUE_STRING);

        TokenVector tokens;
        if (!CompilerGetModuleTokens(ty, &tokens, TY_TMP_C_STR(mod))) {
                return NIL;
        }

        return make_tokens(ty, &tokens);
}

BUILTIN_FUNCTION(ty_tokenize)
{
        ASSERT_ARGC("ty.tokenize()", 1);

        if (ARG(0).type != VALUE_STRING) {
                zP("ty.tokenize(): expected string but got: %s", VSC(&ARG(0)));
        }

        B.count = 0;
        xvP(B, '\0');
        xvPn(B, ss(ARG(0)), sN(ARG(0)));
        xvP(B, '\0');

        Arena old = NewArena(1 << 18);

        TokenVector tokens;
        if (!tokenize(ty, B.items + 1, &tokens)) {
                ReleaseArena(old);
                return NIL;
        }

        Value vTokens = make_tokens(ty, &tokens);

        ReleaseArena(old);

        return vTokens;
}

BUILTIN_FUNCTION(ty_scope)
{
        ASSERT_ARGC("ty.scope()", 0);

        Scope *scope = TyCompilerState(ty)->macro_scope;

        return (scope == NULL) ? NIL : PTR(scope);
}

BUILTIN_FUNCTION(ty_ctx)
{
        ASSERT_ARGC("ty.ctx()", 0);

        CompileState const *state = TyCompilerState(ty);

        Value scope = (state->macro_scope != NULL)
                    ? PTR(state->macro_scope)
                    : NIL;
        Value mod  = vSsz(state->module->name);
        Value path = vSsz(state->module->path);
        

        return vTn(
                "scope", scope,
                "mod", mod,
                "path", path
        );
}

static Value
ScopeDict(Ty *ty, Scope *scope, bool public_only)
{
        Dict *vars = dict_new(ty);

        GC_STOP();

        for (int i = 0; i < scope->size; ++i) {
                for (Symbol *sym = scope->table[i]; sym != NULL; sym = sym->next) {
                        if (!public_only || SymbolIsPublic(sym)) {
                                Value name = vSsz(sym->identifier);
                                Value entry;
                                if (SymbolIsNamespace(sym)) {
                                        entry = ScopeDict(ty, sym->scope, public_only);
                                } else {
                                        entry = vTn(
                                                "name", name,
                                                "type", type_to_ty(ty, sym->type),
                                                "value", *vm_global(ty, sym->i)
                                        );
                                }
                                dict_put_value(ty, vars, name, entry);
                        }
                }
        }

        GC_RESUME();

        return DICT(vars);
}

BUILTIN_FUNCTION(ty_module)
{
        ASSERT_ARGC("ty.module()", 0, 1);

        bool this = (argc == 0);
        Value name = !this ? ARGx(0, VALUE_STRING) : NIL;
        Module *mod = !this
                    ? CompilerGetModule(ty, TY_TMP_C_STR(name))
                    : CompilerCurrentModule(ty);

        if (mod == NULL) {
                return NIL;
        }

        return ScopeDict(ty, mod->scope, !this);
}

BUILTIN_FUNCTION(ty_parse)
{
        ASSERT_ARGC("ty.parse()", 1);

        Location stop;
        Value extra = NIL;

        bool resolve = HAVE_FLAG("resolve");

        char const *tokens_key = HAVE_FLAG("tokens")
                               ? "tokens"
                               : NULL;
        u32 flags = (
                TYC_PARSE
              | TYC_IMPORT_ALL
              | TYC_FORGIVING
              | TYC_NO_TYPES
              | (TYC_SHALLOW * !HAVE_FLAG("deep"))
              | (TYC_RESOLVE * resolve)
              | (TYC_TOKENS  * (tokens_key != NULL))
        );

        Value vTokens = NIL;
        Value result;

/* = */ GC_STOP(); /* ====================================================== */
        TYPES_OFF += 1;

        Arena volatile old = NewArena(1 << 22);
        char *source = TY_0_C_STR(ARGx(0, VALUE_STRING, VALUE_BLOB));

        if (TY_CATCH_ERROR()) {
                Value exc = TY_CATCH();
                ReleaseArena(old);
                TYPES_OFF -= 1;
                ty_free(source - 1);
                return Err(ty, exc);
        }

        Module *mod = TyCompileSource(ty, source, flags);

        Stmt **prog = mod->prog;
        TokenVector tokens = mod->tokens;

        if (prog == NULL) {
                Value last;
                char const *msg = TyError(ty);

                if (tokens_key) {
                        vTokens = make_tokens(ty, &tokens);
                }

                if (LastParsedExpr != NULL) {
                        last = CToTyExpr(ty, LastParsedExpr);
                        last = !IsNone(last) ? last : NIL;
                } else {
                        last = NIL;
                }

                extra = vTn(
                        "location", make_location(ty, &stop),
                        "msg",      vSsz(msg),
                        "last",     last,
                        tokens_key, vTokens
                );
        } else if (tokens_key) {
                vTokens = make_tokens(ty, &tokens);
                extra = vTn(tokens_key, vTokens);
        }

        if (prog == NULL || prog[0] == NULL) {
                result = Err(ty, extra);
                goto End;
        }

        if (
                (prog[1] == NULL)
             && (prog[0]->type == STATEMENT_EXPRESSION)
        ) {
                Value v = CToTyExpr(ty, prog[0]->expression);
                if (v.type == VALUE_NONE) {
                        result = Err(ty, extra);
                } else {
                        result = Ok(ty, PAIR(v, extra));
                }
                goto End;
        }

        if (prog[1] == NULL) {
                Value v = CToTyStmt(ty, prog[0]);
                if (v.type == VALUE_NONE) {
                        result = Err(ty, extra);
                } else {
                        result = Ok(ty, PAIR(v, extra));
                }
                goto End;
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

End:
        ty_free(source - 1);
        ReleaseArena(old);
        TY_CATCH_END();
        TYPES_OFF -= 1;
/* = */ GC_RESUME(); /* ==================================================== */

        return result;
}

BUILTIN_FUNCTION(ty_id)
{
        ASSERT_ARGC("ty.id()", 1);
        return INTEGER(ARG(0).src);
}

static Value
MethodSummary(Ty *ty, Type *t0, Expr const *fun)
{
        Type *u0 = fun->_type;

        if (t0 != NULL) {
                u0 = type_inst_for(ty, t0, u0);
        }

        return vTn(
                "name", vSsz(fun->name),
                "type", type_to_ty(ty, u0)
        );
}

BUILTIN_FUNCTION(ty_type_type)
{
        ASSERT_ARGC("ty.types.type()", 1);

        Value arg0 = ARG(0);
        Type *t0 = type_from_ty(ty, &arg0);

        return type_to_ty(ty, t0);
}

BUILTIN_FUNCTION(ty_type_info)
{
        ASSERT_ARGC("ty.types.info()", 1);

        Value arg0 = ARG(0);
        Type *t0 = type_from_ty(ty, &arg0);

        if (
                (TypeType(t0) != TYPE_CLASS)
             && (TypeType(t0) != TYPE_OBJECT)
        ) {
                return NIL;
        }

        if (t0->class->def == NULL) {
                return NIL;
        }

        ClassDefinition *def = &t0->class->def->class;

        GC_STOP();

        Array *methods = vA();
        Array *statics = vA();
        Array *fields = vA();
        Array *getters = vA();
        Array *setters = vA();
        Array *traits = vA();
        Array *params = vA();

        for (int i = 0; i < vN(def->methods); ++i) {
                vAp(methods, MethodSummary(ty, t0, v__(def->methods, i)));
        }

        for (int i = 0; i < vN(def->s_methods); ++i) {
                vAp(statics, MethodSummary(ty, t0, v__(def->s_methods, i)));
        }

        for (int i = 0; i < vN(def->getters); ++i) {
                vAp(getters, MethodSummary(ty, t0, v__(def->getters, i)));
        }

        for (int i = 0; i < vN(def->setters); ++i) {
                vAp(setters, MethodSummary(ty, t0, v__(def->setters, i)));
        }

        for (int i = 0; i < vN(def->fields); ++i) {
                Expr const *field = v__(def->fields, i);
                char const *name = (field->type == EXPRESSION_IDENTIFIER)
                                 ? field->identifier
                                 : field->target->identifier;
                Type *u0 = type_inst_for(ty, t0, field->_type);
                vAp(
                        fields,
                        vTn(
                                "name", vSsz(name),
                                "type", type_to_ty(ty, u0)
                        )
                );
        }

        for (int i = 0; i < vN(def->traits); ++i) {
                Type *tr0 = type_resolve(ty, v__(def->traits, i));
                vAp(traits, type_to_ty(ty, type_inst_for(ty, t0, tr0)));
        }

        for (int i = 0; i < vN(def->type_params); ++i) {
                vAp(params, type_to_ty(ty, v__(def->type_params, i)->symbol->type));
        }

        Value super;
        if (def->super != NULL) {
                super = type_to_ty(
                        ty,
                        type_inst_for(
                                ty,
                                t0,
                                type_resolve(ty, def->super)
                        )
                );
        } else {
                super = NIL;
        }

        Value info = vTn(
                "methods", ARRAY(methods),
                "statics", ARRAY(statics),
                "getters", ARRAY(getters),
                "setters", ARRAY(setters),
                "fields",  ARRAY(fields),
                "traits",  ARRAY(traits),
                "params",  ARRAY(params),
                "super",   super
        );

        GC_RESUME();

        return info;
}

BUILTIN_FUNCTION(ty_type_inst)
{
        char const *_name__ = "ty.types.inst()";

        CHECK_ARGC(1, 2);

        Value v0 = ARG(0);
        Type *t0 = type_from_ty(ty, &v0);

        if (argc == 1) {
                return type_to_ty(ty, type_inst(ty, t0));
        }

        U32Vector params = {0};
        TypeVector args = {0};

        Value subs = ARGx(1, VALUE_ARRAY);

        for (int i = 0; i < vN(*subs.array); ++i) {
                Type *a0;
                Value *sub = v_(*subs.array, i);
                if (sub->type == VALUE_TUPLE && sub->count == 2) {
                        a0 = type_from_ty(ty, &sub->items[1]);
                        sub = &sub->items[0];
                } else {
                        a0 = type_var(ty);
                }
                switch (sub->type) {
                case VALUE_INTEGER:
                        xvP(params, sub->z);
                        break;
                case VALUE_TYPE:
                        if (!type_is_tvar(as_type(sub))) {
                                zP(
                                        "%s: invalid type used as parameter "
                                        "in substitution list: %s",
                                        _name__,
                                        type_show(ty, as_type(sub))
                                );
                        }
                        xvP(params, as_type(sub)->id);
                        break;
                default:
                        if (
                                (tags_first(ty, sub->tags) == TyVarT)
                             && (unwrap(ty, sub).type == VALUE_INTEGER)
                        ) {
                                xvP(params, sub->z);
                        } else {
                                zP(
                                        "%s: invalid value used as parameter "
                                        "in substitution list: %s",
                                        _name__,
                                        VSC(sub)
                                );
                        }
                }
                xvP(args, a0);
        }

        Value result = type_to_ty(ty, type_inst0(ty, t0, &params, &args));

        xvF(params);
        xvF(args);

        return result;
}

BUILTIN_FUNCTION(ty_type_infer)
{
        ASSERT_ARGC("ty.types.infer()", 1);

        Value ast = ARG(0);
        Expr *expr = TyToCExpr(ty, &ast);

        if (!compiler_symbolize_expression(ty, expr, NULL)) {
                return NIL;
        }

        return type_to_ty(ty, expr->_type);
}

BUILTIN_FUNCTION(ty_type_check)
{
        char const *_name__ = "ty.types.check()";

        CHECK_ARGC(2);

        Value t0 = ARG(0);
        Value t1 = ARG(1);

        return BOOLEAN(
                type_check(
                        ty,
                        type_from_ty(ty, &t0),
                        type_from_ty(ty, &t1)
                )
        );
}

BUILTIN_FUNCTION(ty_type_show)
{
        ASSERT_ARGC("ty.types.show()", 1);

        Value t = ARG(0);
        Type *type = type_from_ty(ty, &t);

        return vSsz(type_show(ty, type));
}

BUILTIN_FUNCTION(ty_definition)
{
        char const *_name__ = "ty.definition()";

        CHECK_ARGC(1);

        return CToTyStmt(
                ty,
                class_get(ty, ARGx(0, VALUE_CLASS).class)->def
        );
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
                src = (Expr *)expr.ptr;
        }

        if (src == NULL || src->start.s == NULL || src->end.s == NULL) {
                return NIL;
        }

        GC_STOP();

        Value file = (src->mod != NULL)
                   ? vSsz(src->mod->path)
                   : NIL;

        Value result = vTn(
                "start", make_location(ty, &src->start),
                "end",   make_location(ty, &src->end),
                "file",  file,
                "mod",   (src->mod != NULL) ? xSz(src->mod->name) : NIL,
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

        Token t = parse_get_token(ty, argc == 0 ? 0 : ARG(0).z);
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
        ASSERT_ARGC("ty.parse.source()", 0, 1);

        Value vSrc = ARGx(0, VALUE_STRING, VALUE_BLOB);
        char *src = TY_0_C_STR(vSrc);
        Stmt **p = parse(ty, src, NULL);

        if (p == NULL) {
                char const *msg = TyError(ty);
                Value err = Err(ty, vSsz(msg));
                vmE(&err);
        }

        return (p[0] == NULL) ? NIL : tyexpr(ty, p[0], 0);
}


BUILTIN_FUNCTION(parse_expr)
{
        ASSERT_ARGC_2("ty.parse.expr()", 0, 1);

        int prec;

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("ty.parse.expr(): expected integer but got: %s", VSC(&ARG(0)));
                }
                prec = ARG(0).z;
        } else {
                prec = 0;
        }

        Value *resolve = NAMED("resolve");
        Value *raw = NAMED("raw");

        return parse_get_expr(
                ty,
                prec,
                (resolve != NULL) && value_truthy(ty, resolve),
                (raw != NULL) && value_truthy(ty, raw)
        );
}

BUILTIN_FUNCTION(parse_type)
{
        ASSERT_ARGC_2("ty.parse.type()", 0, 1);

        int prec;

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("ty.parse.type(): expected integer but got: %s", VSC(&ARG(0)));
                }
                prec = ARG(0).z;
        } else {
                prec = 0;
        }

        Value *resolve = NAMED("resolve");
        Value *raw = NAMED("raw");

        return parse_get_type(
                ty,
                prec,
                (resolve != NULL) && value_truthy(ty, resolve),
                (raw != NULL) && value_truthy(ty, raw)
        );
}

BUILTIN_FUNCTION(parse_stmt)
{
        ASSERT_ARGC_2("ty.parse.stmt()", 0, 1);

        int prec;

        Value *raw = NAMED("raw");

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("ty.parse.stmt(): expected integer but got: %s", VSC(&ARG(0)));
                }
                prec = ARG(0).z;
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
        ASSERT_ARGC("ty.parse.fail()", 1);
        ParseError(ty, "%s", TY_TMP_C_STR(ARGx(0, VALUE_STRING)));
        UNREACHABLE();
}

BUILTIN_FUNCTION(ptr_typed)
{
        ASSERT_ARGC("ptr.typed()", 2);

        if (ARG(0).type == VALUE_NIL) {
                return NIL;
        }

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

        Value p = ARG(0);

        if (p.type == VALUE_NIL) {
                return NIL;
        }

        if (p.type != VALUE_PTR) {
                zP("ptr.untyped(): expected pointer as first argument but got: %s", VSC(&p));
        }

        return GCPTR(p.ptr, p.gcptr);
}

BUILTIN_FUNCTION(ptr_from_int)
{
        ASSERT_ARGC("ptr.fromInt()", 1);
        return PTR((void *)(uintptr_t)INT_ARG(0));
}

BUILTIN_FUNCTION(tdb_eval)
{
        ASSERT_ARGC("tdb.eval()", 1);

        if (!DEBUGGING) return NIL;

        ty = TDB->ty;

        v0(B);
        xvP(B, '\0');
        xvPn(B, ss(ARG(0)), sN(ARG(0)));
        xvP(B, '\0');

        Arena old = NewArena(1 << 20);

        Stmt **prog = parse(ty, vv(B) + 1, "(eval)");
        if (prog == NULL) {
                char const *msg = TyError(ty);
                Value error = Err(ty, vSsz(msg));
                ReleaseArena(old);
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
             && tyeval(TDB->host, e, &v)
        ) {
                ReleaseArena(old);
                return Ok(ty, v);
        }

        *TDB->host = save;
// =====================================================================

        Value error = Err(ty, v);

        ReleaseArena(old);

        return error;
}

BUILTIN_FUNCTION(tdb_list)
{
        ASSERT_ARGC("tdb.list()", 0);
        TDB_MUST_NOT_BE(STOPPED);

        tdb_list(TDB->host);

        return NIL;
}

BUILTIN_FUNCTION(tdb_stack)
{
        ASSERT_ARGC("tdb.stack()", 1);
        isize i = INT_ARG(0);
        return (i >= 0 && i < vN(TDB->host->stack))
             ? Some(vvL(TDB->host->stack)[-i])
             : None;
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
        TDB_MUST_NOT_BE(STOPPED);
        return BOOLEAN(tdb_step_over(TDB->host));
}

BUILTIN_FUNCTION(tdb_into)
{
        ASSERT_ARGC("tdb.into()", 0);
        TDB_MUST_NOT_BE(STOPPED);
        return BOOLEAN(tdb_step_into(TDB->host));
}

BUILTIN_FUNCTION(tdb_step)
{
        ASSERT_ARGC("tdb.step()", 0);
        TDB_MUST_NOT_BE(STOPPED);
        return BOOLEAN(tdb_step_line(TDB->host));
}

BUILTIN_FUNCTION(tdb_backtrace)
{
        ASSERT_ARGC("tdb.backtrace()", 0);
        TDB_MUST_NOT_BE(STOPPED);

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
                   : (context->mod == NULL)  ? NIL
                   : xSz(context->mod->path);

        return (context == NULL) ? NIL : vTn(
                "prog",  prog,
                "file",  file,
                "expr",  expr
        );
}

BUILTIN_FUNCTION(tdb_insn)
{
        char const *_name__ = "tdb.insn()";
        CHECK_ARGC(1);
        TDB_MUST_NOT_BE(OFF);

        Value ip = ARGx(0, VALUE_PTR);
        u8 insn = *(u8 *)ip.ptr;

        return vTn(
                "name", xSz(GetInstructionName(insn))
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
                   : (context->mod == NULL)  ? NIL
                   : xSz(context->mod->path);

        Value mod = (context == NULL) ? NIL : xSz(GetExpressionModule(context));

        Value f = (TDB->host->st.frames.count > 0)
                ? *FrameFun(TDB->host, vvL(TDB->host->st.frames))
                : NIL;

        Value fp = (TDB->host->st.frames.count > 0)
                 ? INTEGER(vvL(TDB->host->st.frames)->fp)
                 : NIL;

        return vTn(
                "ip",    ip,
                "insn",  xSz(GetInstructionName(*(u8 *)ip.ptr)),
                "prog",  prog,
                "file",  file,
                "mod",   mod,
                "expr",  expr,
                "func",  f,
                "fp",    fp,
                "sp",    INTEGER(TDB->host->stack.count)
        );
}

/* vim: set sw=8 sts=8 expandtab: */
