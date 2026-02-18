#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "polyfill_unistd.h"
#include <fcntl.h>
#include <limits.h>

#ifdef __APPLE__
#include <libproc.h>
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

bool
contains(char const *s, char c)
{
        return (c != '\0') && (strchr(s, c) != NULL);
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
#else
        return false;
#endif
}

char *
directory_of(char const *path, char *buf)
{
#if defined(__APPLE__)
        return dirname_r(path, buf);
#elif defined(__linux__)
        strcpy(buf, path);
        return dirname(buf);
#elif defined(_WIN32)
        strcpy(buf, path);
        PathRemoveFileSpecA(buf);
        return buf;

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

                va_copy(ap_, ap);
                need = vsnprintf(b->items + b->count, avail, fmt, ap_);
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

                va_start(ap, fmt);
                need = vsnprintf(b->items + b->count, avail, fmt, ap);
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

                va_copy(ap_, ap);
                need = vsnprintf(vZ(*str), avail, fmt, ap_);
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

                va_copy(ap_, ap);
                need = vsnprintf(vZ(*str), avail, fmt, ap_);
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

/* vim: set sw=8 sts=8 expandtab: */
