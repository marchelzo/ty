/*
 * Adapted from Cosmopolitan Libc's libc/proc/posix_spawn.c
 *
 * Copyright 2023 Justine Alexandra Roberts Tunney
 *
 * Permission to use, copy, modify, and/or distribute this software for
 * any purpose with or without fee is hereby granted, provided that the
 * above copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL
 * WARRANTIES WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE
 * AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL
 * DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR
 * PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER
 * TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
 * PERFORMANCE OF THIS SOFTWARE.
 */

#ifndef _WIN32

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <spawn.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#if defined(__linux__)
#include <sys/prctl.h>
#include <sys/syscall.h>
#endif

#include "ty/spawn.h"

extern char **environ;

#if defined(__APPLE__)
#define SPAWN_FORK() fork()
#else
#define SPAWN_FORK() vfork()
#endif

void
TySpawnInit(TySpawn *sp)
{
        sp->flags   = 0;
        sp->pgroup  = 0;
        sp->err     = 0;
        sp->nact    = 0;
        sp->nkeep   = 0;
        sp->rlimset = 0;
        sigemptyset(&sp->sigdef);
}

static struct spawn_act *
push(TySpawn *sp, int kind)
{
        if (sp->nact == TY_SPAWN_MAX_ACTIONS) {
                sp->err = E2BIG;
                return NULL;
        }

        struct spawn_act *a = &sp->act[sp->nact++];

        a->kind  = kind;
        a->fd    = -1;
        a->newfd = -1;
        a->oflag = 0;
        a->path  = NULL;

        return a;
}

void
spawn_close(TySpawn *sp, int fd)
{
        struct spawn_act *a = push(sp, SPAWN_ACT_CLOSE);
        if (a != NULL) {
                a->fd = fd;
        }
}

void
spawn_dup2(TySpawn *sp, int fd, int newfd)
{
        struct spawn_act *a = push(sp, SPAWN_ACT_DUP2);
        if (a != NULL) {
                a->fd    = fd;
                a->newfd = newfd;
        }
}

void
spawn_open(TySpawn *sp, int fd, char const *path, int oflag)
{
        struct spawn_act *a = push(sp, SPAWN_ACT_OPEN);
        if (a != NULL) {
                a->fd    = fd;
                a->path  = path;
                a->oflag = oflag;
        }
}

void
spawn_chdir(TySpawn *sp, char const *path)
{
        struct spawn_act *a = push(sp, SPAWN_ACT_CHDIR);
        if (a != NULL) {
                a->path = path;
        }
}

void
spawn_fchdir(TySpawn *sp, int fd)
{
        struct spawn_act *a = push(sp, SPAWN_ACT_FCHDIR);
        if (a != NULL) {
                a->fd = fd;
        }
}

void
spawn_setpgroup(TySpawn *sp, pid_t pgroup)
{
        sp->flags  |= SPAWN_SETPGROUP;
        sp->pgroup  = pgroup;
}

void
spawn_setsid(TySpawn *sp)
{
        sp->flags |= SPAWN_SETSID;
}

void
spawn_closefds(TySpawn *sp)
{
        push(sp, SPAWN_ACT_CLOSEFDS);
}

void
spawn_keep(TySpawn *sp, int fd)
{
        int i;

        if (fd < 0) {
                sp->err = EBADF;
                return;
        }

        if (fd <= 2) {
                return;
        }

        for (i = 0; i < sp->nkeep && sp->keep[i] < fd; ++i) {
                continue;
        }

        if (i < sp->nkeep && sp->keep[i] == fd) {
                return;
        }

        if (sp->nkeep == TY_SPAWN_MAX_KEEP) {
                sp->err = E2BIG;
                return;
        }

        memmove(&sp->keep[i + 1], &sp->keep[i], (sp->nkeep - i) * sizeof sp->keep[0]);
        sp->keep[i]  = fd;
        sp->nkeep   += 1;
}

void
spawn_sigdefault(TySpawn *sp, int sig)
{
        if (sigaddset(&sp->sigdef, sig) == -1) {
                sp->err = EINVAL;
                return;
        }

        sp->flags |= SPAWN_SETSIGDEF;
}

void
spawn_umask(TySpawn *sp, mode_t mask)
{
        sp->flags |= SPAWN_UMASK;
        sp->umask  = mask;
}

void
spawn_pdeathsig(TySpawn *sp, int sig)
{
        sp->flags     |= SPAWN_PDEATHSIG;
        sp->pdeathsig  = sig;
}

void
spawn_rlimit(TySpawn *sp, int resource, struct rlimit const *rlim)
{
        if (resource < 0 || resource >= TY_RLIM_N) {
                sp->err = EINVAL;
                return;
        }

        sp->rlimset        |= UINT64_C(1) << resource;
        sp->rlim[resource]  = *rlim;
}

static bool
evade(int *pw, int fd)
{
        if (*pw != fd) {
                return true;
        }

        int nfd = fcntl(*pw, F_DUPFD_CLOEXEC, fd + 1);
        if (nfd == -1) {
                return false;
        }

        *pw = nfd;

        return true;
}

static bool
closerange(int lo, int hi)
{
        struct rlimit nofile;

        if (lo > hi) {
                return true;
        }

#if defined(SYS_close_range)
        if (syscall(SYS_close_range, (unsigned)lo, (unsigned)hi, 0) == 0) {
                return true;
        }
        if (errno != ENOSYS) {
                return false;
        }
#endif

        rlim_t max = (rlim_t)1 << 20;

        if (
                (getrlimit(RLIMIT_NOFILE, &nofile) == 0)
             && (nofile.rlim_cur != RLIM_INFINITY)
        ) {
                max = nofile.rlim_cur;
        }

        if ((rlim_t)hi >= max) {
                hi = (int)(max - 1);
        }

        for (int fd = lo; fd <= hi; ++fd) {
                close(fd);
        }

        return true;
}

static bool
closefds(TySpawn const *sp, int pw)
{
        int skip[TY_SPAWN_MAX_KEEP + 1];
        int n = 0;
        int lo = 3;

        for (int i = 0; i < sp->nkeep; ++i) {
                if (pw < sp->keep[i] && (n == i)) {
                        skip[n++] = pw;
                }
                skip[n++] = sp->keep[i];
        }

        if (n == sp->nkeep) {
                skip[n++] = pw;
        }

        for (int i = 0; i < n; ++i) {
                if (skip[i] < lo) {
                        continue;
                }
                if (!closerange(lo, skip[i] - 1)) {
                        return false;
                }
                lo = skip[i] + 1;
        }

        if (!closerange(lo, INT_MAX)) {
                return false;
        }

        for (int i = 0; i < sp->nkeep; ++i) {
                if (fcntl(sp->keep[i], F_SETFD, 0) == -1) {
                        return false;
                }
        }

        return true;
}

static bool
perform(TySpawn const *sp, struct spawn_act const *a, int *pw)
{
        int t;

        switch (a->kind) {
        case SPAWN_ACT_CLOSE:
                if (!evade(pw, a->fd)) {
                        return false;
                }
                return (close(a->fd) == 0) || (errno == EBADF);

        case SPAWN_ACT_DUP2:
                if (!evade(pw, a->newfd)) {
                        return false;
                }
                if (a->fd == a->newfd) {
                        return fcntl(a->fd, F_SETFD, 0) != -1;
                }
                return dup2(a->fd, a->newfd) != -1;

        case SPAWN_ACT_OPEN:
                if (!evade(pw, a->fd)) {
                        return false;
                }
                if ((t = open(a->path, a->oflag, 0666)) == -1) {
                        return false;
                }
                if (t == a->fd) {
                        return true;
                }
                if (dup2(t, a->fd) == -1) {
                        close(t);
                        return false;
                }
                return close(t) == 0;

        case SPAWN_ACT_CHDIR:
                return chdir(a->path) == 0;

        case SPAWN_ACT_FCHDIR:
                return fchdir(a->fd) == 0;

        case SPAWN_ACT_CLOSEFDS:
                return closefds(sp, *pw);
        }

        errno = EINVAL;

        return false;
}

static int
execpath(char const *file, char const *path, char *const argv[], char *const envp[])
{
        char buf[PATH_MAX];
        size_t flen = strlen(file);
        bool eacces = false;

        if (path == NULL) {
                execve(file, argv, envp);
                return errno;
        }

        for (char const *p = path;; ++p) {
                char const *end = p;
                while (*end != '\0' && *end != ':') {
                        end += 1;
                }

                size_t dlen = end - p;

                if (dlen + flen + 2 <= sizeof buf) {
                        memcpy(buf, p, dlen);
                        if (dlen > 0) {
                                buf[dlen++] = '/';
                        }
                        memcpy(buf + dlen, file, flen + 1);

                        execve(buf, argv, envp);

                        switch (errno) {
                        case EACCES:
                                eacces = true;
                                break;

                        case ENOENT:
                        case ENOTDIR:
                        case ENAMETOOLONG:
                        case ELOOP:
                                break;

                        default:
                                return errno;
                        }
                }

                if (*end == '\0') {
                        break;
                }

                p = end;
        }

        return eacces ? EACCES : ENOENT;
}

static bool
resets(TySpawn const *sp, int sig, struct sigaction const *old)
{
        if (old->sa_handler == SIG_DFL) {
                return false;
        }

        if (old->sa_handler != SIG_IGN) {
                return true;
        }

        return (sp->flags & SPAWN_SETSIGDEF)
            && (sigismember(&sp->sigdef, sig) == 1);
}

static noreturn void
child(
        TySpawn const *sp,
        int pw,
        char const *file,
        char const *path,
        char *const argv[],
        char *const envp[],
        sigset_t const *mask,
        pid_t ppid
)
{
        struct sigaction dfl = { .sa_handler = SIG_DFL };
        struct sigaction old;
        int err;

        for (int sig = 1; sig < NSIG; ++sig) {
                if (
                        (sigaction(sig, NULL, &old) == 0)
                     && resets(sp, sig, &old)
                ) {
                        sigaction(sig, &dfl, NULL);
                }
        }

#if defined(__linux__)
        if (sp->flags & SPAWN_PDEATHSIG) {
                if (prctl(PR_SET_PDEATHSIG, sp->pdeathsig) == -1) {
                        goto Fail;
                }
                if (getppid() != ppid) {
                        _exit(127);
                }
        }
#endif

        if (sp->flags & SPAWN_UMASK) {
                umask(sp->umask);
        }

        if ((sp->flags & SPAWN_SETSID) && (setsid() == -1)) {
                goto Fail;
        }

        if (
                (sp->flags & SPAWN_SETPGROUP)
             && !((sp->flags & SPAWN_SETSID) && (sp->pgroup == 0))
             && (setpgid(0, sp->pgroup) == -1)
        ) {
                goto Fail;
        }

        for (int i = 0; i < sp->nact; ++i) {
                if (!perform(sp, &sp->act[i], &pw)) {
                        goto Fail;
                }
        }

        for (uint64_t set = sp->rlimset; set != 0; set &= set - 1) {
                int resource = __builtin_ctzll(set);
                if (setrlimit(resource, &sp->rlim[resource]) == -1) {
#if defined(__APPLE__) && defined(__aarch64__)
                        if (resource == RLIMIT_STACK && errno == EINVAL) {
                                continue;
                        }
#endif
                        goto Fail;
                }
        }

        sigprocmask(SIG_SETMASK, mask, NULL);

        errno = execpath(file, path, argv, envp);

Fail:
        err = errno;
        while (write(pw, &err, sizeof err) == -1 && errno == EINTR) {
                continue;
        }
        _exit(127);
}

#if defined(__APPLE__)
static bool
nativeable(TySpawn const *sp)
{
        if (sp->rlimset != 0 || (sp->flags & SPAWN_UMASK)) {
                return false;
        }

#if !defined(POSIX_SPAWN_CLOEXEC_DEFAULT)
        for (int i = 0; i < sp->nact; ++i) {
                if (sp->act[i].kind == SPAWN_ACT_CLOSEFDS) {
                        return false;
                }
        }
#endif

        return true;
}

static int
native(
        TySpawn const *sp,
        pid_t *pid,
        char const *file,
        char *const argv[],
        char *const envp[]
)
{
        posix_spawn_file_actions_t fa;
        posix_spawnattr_t sa;
        short flags = 0;
        int ret;

        posix_spawn_file_actions_init(&fa);
        posix_spawnattr_init(&sa);

        for (int i = 0; i < sp->nact; ++i) {
                struct spawn_act const *a = &sp->act[i];
                switch (a->kind) {
                case SPAWN_ACT_CLOSE:  posix_spawn_file_actions_addclose(&fa, a->fd);                         break;
                case SPAWN_ACT_DUP2:   posix_spawn_file_actions_adddup2(&fa, a->fd, a->newfd);                break;
                case SPAWN_ACT_OPEN:   posix_spawn_file_actions_addopen(&fa, a->fd, a->path, a->oflag, 0666); break;
                case SPAWN_ACT_CHDIR:  posix_spawn_file_actions_addchdir_np(&fa, a->path);                    break;
                case SPAWN_ACT_FCHDIR: posix_spawn_file_actions_addfchdir_np(&fa, a->fd);                     break;
#if defined(POSIX_SPAWN_CLOEXEC_DEFAULT)
                case SPAWN_ACT_CLOSEFDS:
                        flags |= POSIX_SPAWN_CLOEXEC_DEFAULT;
                        for (int fd = 0; fd <= 2; ++fd) {
                                posix_spawn_file_actions_addinherit_np(&fa, fd);
                        }
                        for (int k = 0; k < sp->nkeep; ++k) {
                                posix_spawn_file_actions_addinherit_np(&fa, sp->keep[k]);
                        }
                        break;
#endif
                }
        }

        if (sp->flags & SPAWN_SETPGROUP) {
                posix_spawnattr_setpgroup(&sa, sp->pgroup);
                flags |= POSIX_SPAWN_SETPGROUP;
        }

#if defined(POSIX_SPAWN_SETSID)
        if (sp->flags & SPAWN_SETSID) {
                flags |= POSIX_SPAWN_SETSID;
        }
#endif

        if (sp->flags & SPAWN_SETSIGDEF) {
                posix_spawnattr_setsigdefault(&sa, &sp->sigdef);
                flags |= POSIX_SPAWN_SETSIGDEF;
        }

        posix_spawnattr_setflags(&sa, flags);

        ret = posix_spawnp(pid, file, &fa, &sa, argv, (envp != NULL) ? envp : environ);

        posix_spawn_file_actions_destroy(&fa);
        posix_spawnattr_destroy(&sa);

        return ret;
}
#endif

int
TySpawnRun(
        TySpawn const *sp,
        pid_t *pid,
        char const *file,
        char *const argv[],
        char *const envp[]
)
{
        char const *path;
        pid_t ppid = getpid();
        sigset_t all;
        sigset_t old;
        pid_t cpid;
        ssize_t n;
        int pfd[2];
        int cerr;
        int err;

        if (sp->err != 0) {
                return sp->err;
        }

        if (*file == '\0') {
                return ENOENT;
        }

#if !defined(__linux__)
        if (sp->flags & SPAWN_PDEATHSIG) {
                return ENOTSUP;
        }
#endif

#if defined(__APPLE__)
        if (nativeable(sp)) {
                return native(sp, pid, file, argv, envp);
        }
#endif

        if (strchr(file, '/') != NULL) {
                path = NULL;
        } else if ((path = getenv("PATH")) == NULL) {
                path = "/bin:/usr/bin";
        }

        if (envp == NULL) {
                envp = environ;
        }

        if (pipe(pfd) == -1) {
                return errno;
        }

        if (
                (fcntl(pfd[0], F_SETFD, FD_CLOEXEC) == -1)
             || (fcntl(pfd[1], F_SETFD, FD_CLOEXEC) == -1)
        ) {
                err = errno;
                close(pfd[0]);
                close(pfd[1]);
                return err;
        }

        sigfillset(&all);
        pthread_sigmask(SIG_SETMASK, &all, &old);

        cpid = SPAWN_FORK();
        if (cpid == 0) {
                close(pfd[0]);
                child(sp, pfd[1], file, path, argv, envp, &old, ppid);
        }

        err = (cpid == -1) ? errno : 0;

        close(pfd[1]);

        if (cpid != -1) {
                do {
                        n = read(pfd[0], &cerr, sizeof cerr);
                } while (n == -1 && errno == EINTR);

                if (n == sizeof cerr) {
                        err = cerr;
                        while (waitpid(cpid, NULL, 0) == -1 && errno == EINTR) {
                                continue;
                        }
                } else {
                        *pid = cpid;
                }
        }

        close(pfd[0]);

        pthread_sigmask(SIG_SETMASK, &old, NULL);

        return err;
}

#endif
