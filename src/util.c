#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "polyfill_unistd.h"
#include <fcntl.h>
#include <limits.h>

#ifdef __APPLE__
#include <libproc.h>
#endif

#if defined(__FreeBSD__)
#include <sys/sysctl.h>
#endif

#ifdef _WIN32
 #include <windows.h>
 #include <shlwapi.h>
#else
 #include <libgen.h>
 #include <sys/mman.h>
 #include <sys/ioctl.h>
#endif

#if !defined(S_ISREG) && defined(S_IFMT) && defined(S_IFREG)
 #define S_ISREG(m) (((m) & S_IFMT) == S_IFREG)
 #define S_ISLNK(m) 0
#endif

#define STB_SPRINTF_IMPLEMENTATION

#include "panic.h"
#include "alloc.h"
#include "xd.h"
#include "vec.h"
#include "value.h"

char *
sclone(Ty *ty, char const *s)
{
        size_t n = strlen(s);
        char *new = mA(n + 1);
        memcpy(new, s, n + 1);
        return new;
}

char *
sclonea(Ty *ty, char const *s)
{
        size_t n = strlen(s);
        char *new = amA(n + 1);
        memcpy(new, s, n + 1);
        return new;
}

char *
fslurp(Ty *ty, FILE *f)
{
        byte_vector s = {0};

        vvP(s, '\0');
        for (int c; (c = fgetc(f)) != EOF;) {
                vvP(s, c);
        }
        vvP(s, '\0');

        return vv(s) + 1;
}

char *
slurp(Ty *ty, char const *path)
{
        int fd = open(path, O_RDONLY);
        if (fd == -1) {
                return NULL;
        }

        struct stat st;
        fstat(fd, &st);

        if (false && (S_ISREG(st.st_mode) || S_ISLNK(st.st_mode))) {
                int n = st.st_size;

#ifdef _WIN32
                void *p = VirtualAlloc(NULL, n, MEM_RESERVE, PAGE_READWRITE);
#else
                void *p = mmap(NULL, n, PROT_READ, MAP_SHARED, fd, 0);
#endif
                if (p == NULL) {
                        return NULL;
                }

                char *s = mA(n + 2);
                memcpy(s + 1, p, n);
                s[0] = s[n + 1] = '\0';

#ifdef _WIN32
                VirtualFree(p, n, MEM_RELEASE);
#else
                munmap(p, n);
#endif
                close(fd);

                return s + 1;
        } else {
                vec(char) s = {0};

                char b[1UL << 14];
                int r;

                vvP(s, '\0');
                while ((r = read(fd, b, sizeof b)) > 0) {
                        vvPn(s, b, r);
                }
                vvP(s, '\0');

                close(fd);

                return vv(s) + 1;
        }
}

bool
get_directory_where_chad_looks_for_runtime_dependencies(char *buffer)
{
#if defined(__APPLE__)
        pid_t pid = getpid();
        char path[PROC_PIDPATHINFO_MAXSIZE];

        if (proc_pidpath(pid, path, sizeof path) <= 0) {
                return false;
        }

        return dirname_r(path, buffer) != NULL;
#elif defined(__linux__)
        char path[PATH_MAX + 1], *dir;
        ssize_t len = readlink("/proc/self/exe", path, PATH_MAX);
        if (len <= 0)
                return false;
        path[len] = '\0';
        if ((dir = dirname(path)) == NULL)
                return false;
        strcpy(buffer, dir);
        return true;
#elif defined(_WIN32)
        DWORD len = GetModuleFileName(NULL, buffer, MAX_PATH);
        if (len == 0)
                return false;
        buffer[len] = '\0';
        PathRemoveFileSpecA(buffer);
        return true;
#elif defined(__FreeBSD__)
        int mib[4] = { CTL_KERN, KERN_PROC, KERN_PROC_PATHNAME, -1 };
        size_t len = PATH_MAX;
        return (sysctl(mib, 4, buffer, &len, NULL, 0) == 0);
#else
        return false;
#endif
}

char *
directory_of(char const *path, char *buf)
{
#if defined(__linux__) || defined(__FreeBSD__)
        strcpy(buf, path);
        return dirname(buf);
#elif defined(_WIN32)
        strcpy(buf, path);
        PathRemoveFileSpecA(buf);
        return buf;
#elif defined(__APPLE__)
        return dirname_r(path, buf);
#else
#error "directory_of() is not implemented for this platform"
#endif
}

Value
this_executable(Ty *ty)
{
#if defined(__APPLE__)
        pid_t pid = getpid();
        char path[PROC_PIDPATHINFO_MAXSIZE];

        if (proc_pidpath(pid, path, sizeof path) <= 0) {
                return NIL;
        }

        return vSsz(path);
#elif defined(__linux__)
        char path[PATH_MAX];
        ssize_t len = readlink("/proc/self/exe", path, sizeof path - 1);
        if (len <= 0)
                return NIL;
        return vSs(path, len);
#elif defined(_WIN32)
        char path[MAX_PATH];
        DWORD len = GetModuleFileName(NULL, path, MAX_PATH);
        if (len == 0)
                return NIL;
        return vSs(path, len);
#elif defined(__FreeBSD__)
        int mib[4] = { CTL_KERN, KERN_PROC, KERN_PROC_PATHNAME, -1 };
        char path[PATH_MAX];
        size_t len = sizeof path;
        if (sysctl(mib, 4, path, &len, NULL, 0) != 0)
                return NIL;
        return vSs(path, len - 1);
#else
        return NIL;
#endif
}

bool
get_terminal_size(int fd, int *rows, int *cols)
{
#ifdef _WIN32
        HANDLE hConsole = GetStdHandle(STD_OUTPUT_HANDLE);
        if (hConsole == INVALID_HANDLE_VALUE) {
                return false;
        }
        CONSOLE_SCREEN_BUFFER_INFO csbi;
        if (!GetConsoleScreenBufferInfo(hConsole, &csbi)) {
                return false;
        }

        *rows = csbi.srWindow.Bottom - csbi.srWindow.Top + 1;
        *cols = csbi.srWindow.Right - csbi.srWindow.Left + 1;

        return true;
#else
        bool open_dev_tty = (fd == -1);

        if (open_dev_tty) {
                fd = open("/dev/tty", O_RDONLY);
                if (fd == -1) {
                        return false;
                }
        }

        struct winsize ws;

        if (ioctl(fd, TIOCGWINSZ, &ws) == -1) {
                if (open_dev_tty) {
                        close(fd);
                }
                return false;
        }

        if (open_dev_tty) {
                close(fd);
        }

        *rows = ws.ws_row;
        *cols = ws.ws_col;

        return true;
#endif
}

int
vdump(byte_vector *b, char const *fmt, va_list ap)
{
        va_list ap_;

        for (;;) {
                int avail = b->capacity - b->count;
                int need;

                if (avail == 0) {
                        xvR(*b, max(b->capacity * 2, 256));
                        continue;
                }

                va_copy(ap_, ap);
                need = ty_vsnprintf(b->items + b->count, avail, fmt, ap_);
                va_end(ap_);

                if (1 + need >= avail) {
                        xvR(*b, max(b->capacity * 2, 256));
                        continue;
                }

                b->count += need;
                vvL(*b)[1] = '\0';

                return need;
        }
}

int
dump(byte_vector *b, char const *fmt, ...)
{
        va_list ap;

        for (;;) {
                isize avail = b->capacity - b->count;
                isize need;

                if (avail == 0) {
                        xvR(*b, max(b->capacity * 2, 256));
                        continue;
                }

                va_start(ap, fmt);
                need = ty_vsnprintf(b->items + b->count, avail, fmt, ap);
                va_end(ap);

                if (1 + need >= avail) {
                        xvR(*b, max(b->capacity * 2, 256));
                        continue;
                }

                b->count += need;
                vvL(*b)[1] = '\0';

                return need;
        }
}

int
avdump(Ty *ty, byte_vector *str, char const *fmt, va_list ap)
{
        va_list ap_;

        for (;;) {
                isize avail = vC(*str) - vN(*str);
                isize need;

                if (avail == 0) {
                        avR(*str, max(vC(*str) * 2, 256));
                        continue;
                }

                va_copy(ap_, ap);
                need = ty_vsnprintf(vZ(*str), avail, fmt, ap_);
                va_end(ap_);

                if (1 + need >= avail) {
                        avR(*str, max(vC(*str) * 2, 256));
                        continue;
                }

                str->count += need;
                *vZ(*str) = '\0';

                return need;
        }
}

int
(adump)(Ty *ty, byte_vector *str, char const *fmt, ...)
{
        int bytes;
        va_list ap;

        va_start(ap, fmt);
        bytes = avdump(ty, str, fmt, ap);
        va_end(ap);

        return bytes;
}

int
scvdump(Ty *ty, byte_vector *str, char const *fmt, va_list ap)
{
        va_list ap_;

        for (;;) {
                isize avail = vC(*str) - vN(*str);
                isize need;

                if (avail == 0) {
                        svR(*str, max(vC(*str) * 2, 256));
                        continue;
                }

                va_copy(ap_, ap);
                need = ty_vsnprintf(vZ(*str), avail, fmt, ap_);
                va_end(ap_);

                if (1 + need >= avail) {
                        svR(*str, max(vC(*str) * 2, 256));
                        continue;
                }

                str->count += need;
                *vZ(*str) = '\0';

                return need;
        }
}

int
(sxdf)(Ty *ty, byte_vector *str, char const *fmt, ...)
{
        isize bytes;
        va_list ap;

        va_start(ap, fmt);
        bytes = scvdump(ty, str, fmt, ap);
        va_end(ap);

        return bytes;
}

char *
(sfmt)(Ty *ty, char const *fmt, ...)
{
        byte_vector buf = {0};
        va_list ap;

        va_start(ap, fmt);
        scvdump(ty, &buf, fmt, ap);
        va_end(ap);

        return vv(buf);
}

const char *
(ifmt)(char const *fmt, ...)
{
        char const *str;
        byte_vector buf = {0};
        va_list ap;

        va_start(ap, fmt);
        vdump(&buf, fmt, ap);
        va_end(ap);
        str = intern(&xD.members, vv(buf))->name;
        xvF(buf);

        return str;
}

char *
xfmt(char const *fmt, ...)
{
        byte_vector buf = {0};
        va_list ap;

        va_start(ap, fmt);
        vdump(&buf, fmt, ap);
        va_end(ap);

        return vv(buf);
}

char *
(afmt)(Ty *ty, char const *fmt, ...)
{
        char *str;
        byte_vector buf = {0};
        va_list ap;

        SCRATCH_SAVE();
        va_start(ap, fmt);
        scvdump(ty, &buf, fmt, ap);
        str = sclonea(ty, v_(buf, 0));
        va_end(ap);
        SCRATCH_RESTORE();

        return str;
}

int
fspec_parse(char const **s, char const *end, struct fspec *out)
{
        int w = 0;
        int p = 0;

        out->alt     = false;
        out->blank   = false;
        out->justify = 1;
        out->sep     = false;
        out->sign    = false;
        out->xsep    = '\0';

        m0(out->fill);

        for (;;) {
                if (*out->fill == '\0') {
                        int bytes = term_fit_cols(*s, end - *s, 1);
                        if (UNLIKELY((end - *s) > 1 && (bytes == 0))) {
                                bytes = term_fit_cols(*s, end - *s, 2);
                        }
                        if (
                                   (*s + bytes < end)
                                && contains("<^>", (*s)[bytes])
                        ) {
                                memcpy(out->fill, *s, min(sizeof out->fill - 1, bytes));
                                *s += bytes;
                                continue;
                        }
                }

                switch (**s) {
                case '+':  out->sign    = true;    break;
                case '#':  out->alt     = true;    break;
                case '\'': out->sep     = true;    break;
                case ' ':  out->blank   = true;    break;
                case '-':  out->justify = -1;      break;
                case '<':  out->justify = -1;      break;
                case '^':  out->justify =  0;      break;
                case '>':  out->justify =  1;      break;
                case '0':  strcpy(out->fill, "0"); break;
                default:   goto FlagsComplete;
                }

                *s += 1;
        }

FlagsComplete:
        if (*out->fill == '\0') {
                strcpy(out->fill, " ");
        }

        if (*s < end && **s == '*') {
                if (w + 1 >= sizeof out->width) {
                        return -1;
                }
                out->width[w++] = *(*s)++;
        } else while (*s < end && isdigit(**s)) {
                if (w + 1 >= sizeof out->width) {
                        return -1;
                }
                out->width[w++] = *(*s)++;
        }

        if (*s < end && **s == '.') {
                if (p + 1 >= sizeof out->prec) {
                        return -1;
                }

                out->prec[p++] = *(*s)++;

                while (*s < end && **s == ' ') {
                        ++*s;
                }

                if (*s < end && **s == '*') {
                        if (p + 1 >= sizeof out->prec) {
                                return -1;
                        }
                        out->prec[p++] = *(*s)++;
                } else while (*s < end && isdigit(**s)) {
                        if (p + 1 >= sizeof out->prec) {
                                return -1;
                        }
                        out->prec[p++] = *(*s)++;
                }
        }

        if (*s < end && contains(" _,'", **s)) {
                out->xsep = *(*s)++;
        }

        while (*s < end && **s == ' ') {
                ++*s;
        }

        out->width[w] = '\0';
        out->prec[p]  = '\0';

        return (*s < end) ? *(*s)++ : '\0';
}

FspecPad
fspec_pad(char const *text, isize tlen, struct fspec const *spec)
{
        FspecPad r = {
                .left    = 0,
                .right   = 0,
                .fill    = spec->fill,
                .fill_sz = strlen(spec->fill)
        };

        if (r.fill_sz <= 0) {
                r.fill    = " ";
                r.fill_sz = 1;
        }

        if (!*spec->width) {
                return r;
        }

        int goal = atoi(spec->width);
        int curr = term_width(text, tlen);
        int pad  = max(0, goal - curr);

        switch (spec->justify) {
        case  1: r.left  = pad;                             break;
        case  0: r.left  = pad / 2; r.right = pad - r.left; break;
        case -1: r.right = pad;                             break;
        }

        int fw = term_width(r.fill, r.fill_sz);
        if (fw > 1) {
                r.left  /= fw;
                r.right /= fw;
        }

        return r;
}

/* vim: set sw=8 sts=8 expandtab: */
