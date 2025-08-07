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
#include <sys/mman.h>
#include <libgen.h>
#endif

#if !defined(S_ISREG) && defined(S_IFMT) && defined(S_IFREG)
#define S_ISREG(m) (((m) & S_IFMT) == S_IFREG)
#define S_ISLNK(m) 0
#endif

#include "panic.h"
#include "alloc.h"
#include "util.h"
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
        vec(char) s = {0};

        vvP(s, '\0');

        for (int c; (c = fgetc(f)) != EOF;) {
                vvP(s, c);
        }

        vvP(s, '\0');

        return s.items + 1;
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
                vec(char) s;
                vec_init(s);

                vvP(s, '\0');

                char b[1UL << 14];
                int r;

                while ((r = read(fd, b, sizeof b)) > 0) {
                        for (int i = 0; i < r; ++i) {
                                vvP(s, b[i]);
                        }
                }

                close(fd);

                vvP(s, '\0');

                return s.items + 1;
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
