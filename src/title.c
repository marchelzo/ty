#include <stdio.h>
#include <errno.h>
#include <string.h>

#if defined(__linux__)
#include <sys/prctl.h>
#elif defined(__APPLE__)
#include <crt_externs.h>
#endif

#include "title.h"
#include "ty.h"

extern char **environ;

char **TyArgv;
int    TyArgc;

static char *ArgvEnd;
static char *TitleBegin;
static char *TitleEnd;

static void
skipcomm(FILE *stat)
{
        for (int ch; (ch = fgetc(stat)) != '(';) {
                if (ch == EOF) {
                        return;
                }
        }

        for (int level = 1; level > 0;) {
                switch (fgetc(stat)) {
                default:              break;
                case '(': level += 1; break;
                case ')': level -= 1; break;
                case EOF: return;
                }
        }
}

static char *
GetEnvironEnd(void)
{
#if defined(__linux__)
        /*
         * See proc_pid_stat(5) for the cause of the brain cancer that follows.
         */
        FILE *stat = fopen("/proc/self/stat", "r");
        if (stat == NULL) {
                return NULL;
        }

        char  *buf = NULL;
        usize  cap = 0;

        if (getdelim(&buf, &cap, '\0', stat) < 0) {
                fclose(stat);
                free(buf);
                return NULL;
        }

        fclose(stat);

        char *comm_end = strrchr(buf, ')');
        if (comm_end == NULL) {
                free(buf);
                return NULL;
        }

        char *save;
        char *tok = strtok_r(comm_end + 1, " \t\n", &save);

        /* (3) state */
        if (tok == NULL) {
                free(buf);
                return NULL;
        }

        /* Skip (4) ppid through (50) env_start. */
        for (int field = 4; field < 51; ++field) {
                if (strtok_r(NULL, " \t\n", &save) == NULL) {
                        free(buf);
                        return NULL;
                }
        }

        /* (51) env_end */
        tok = strtok_r(NULL, " \t\n", &save);
        if (tok == NULL) {
                free(buf);
                return NULL;
        }

        errno = 0;

        char *end;
        umax addr = strtoumax(tok, &end, 10);

        bool bad = (end == tok)
                || (*end != '\0')
                || (errno == ERANGE)
                || (addr > UINTPTR_MAX);

        free(buf);

        return !bad ? (char *)(uptr)addr : NULL;
#elif defined(__APPLE__)
        char **argv = *_NSGetArgv();
        int    argc = *_NSGetArgc();

        char **envp = argv + argc + 1;

        while (*envp != NULL) {
                ++envp;
        }

        return envp[2];
#endif
}

static void
TyTitleMoveToSafety(void)
{
}

static void
TyTitleSetup(void)
{
        ArgvEnd = TyArgv[0] + strlen(TyArgv[0]);
        for (int i = 1; TyArgv[i] == ArgvEnd + 1; ++i) {
                ArgvEnd = TyArgv[i] + strlen(TyArgv[i]);
        }

        TitleBegin = TyArgv[0];
        TitleEnd   = GetEnvironEnd();

        if (TitleEnd == NULL) {
                TitleEnd = ArgvEnd + 1;
        }

        /*
         * Any `environ` entries that sill point into this region need to be
         * moved into allocated storage so they aren't clobbered if we call
         * setproctitle().
         */
        uptr beg = (uptr)TitleBegin;
        uptr end = (uptr)TitleEnd;

        for (usize i = 0; environ[i] != NULL; ++i) {
                uptr env_addr = (uptr)environ[i];
                if (env_addr >= beg && env_addr < end) {
                        environ[i] = S2(environ[i]);
                }
        }

        /*
         * On Darwin we do something similar for `argv` as well since external
         * modules may access it via `_NSGetArgv()`.
         */
#if defined(__APPLE__)
        char **clone = xtA(char *, TyArgc + 1);
        for (int i = 0; i < TyArgc; ++i) {
                clone[i] = S2(TyArgv[i]);
        }
        clone[TyArgc] = NULL;

        *_NSGetArgv() = clone;
#endif

}

void
TyTitleSet(char const *title, usize size)
{
        if (TitleBegin == NULL) {
                TyTitleSetup();
        }

        usize avail = TitleEnd - TitleBegin;
        usize keep  = zminu(size, avail);

        memset(TitleBegin, 0, avail);
        memcpy(TitleBegin, title, keep);

#if defined(__linux__)
        /*
         * If we can, we should update the kernel's argv/env metadata. These values
         * affect what readers of /proc/pid/{cmdline,environ} will see.
         *
         * If we don't have CAP_SYS_RESOURCE, this will fail, and writing title data
         * over the original `arg_end` will cause the kernel to realize we're doing
         * some kind of `setproctitle()` thing, and subsequent reads to /proc/pid/cmdline
         * will only see title data up to the first NUL in the original `argv` region.
         *
         * The kernel uses `arg_end[-1] != '\0'` to detect this, so we should make sure
         * that byte isn't NUL if we couldn't update the metadata.
         */
        uptr end = (uptr)TitleBegin + keep;
        bool err = (prctl(PR_SET_MM, PR_SET_MM_ARG_END,   end, 0, 0) < 0)
                || (prctl(PR_SET_MM, PR_SET_MM_ENV_START, end, 0, 0) < 0);
        *ArgvEnd += ('x' * err * !*ArgvEnd);
#endif
}
/* vim: set sts=8 sw=8 expandtab: */
