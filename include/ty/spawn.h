#ifndef TYSPAWN_H_INCLUDED
#define TYSPAWN_H_INCLUDED

#include <signal.h>
#include <stdint.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/types.h>

#if defined(RLIM_NLIMITS)
#define TY_RLIM_N RLIM_NLIMITS
#elif defined(RLIMIT_NLIMITS)
#define TY_RLIM_N RLIMIT_NLIMITS
#else
#define TY_RLIM_N 16
#endif

#define TY_SPAWN_MAX_ACTIONS 32
#define TY_SPAWN_MAX_KEEP    32

enum {
        SPAWN_ACT_CLOSE,
        SPAWN_ACT_DUP2,
        SPAWN_ACT_OPEN,
        SPAWN_ACT_CHDIR,
        SPAWN_ACT_FCHDIR,
        SPAWN_ACT_CLOSEFDS
};

enum {
        SPAWN_SETPGROUP = 1 << 0,
        SPAWN_SETSID    = 1 << 1,
        SPAWN_SETSIGDEF = 1 << 2,
        SPAWN_UMASK     = 1 << 3,
        SPAWN_PDEATHSIG = 1 << 4
};

struct spawn_act {
        int         kind;
        int         fd;
        int         newfd;
        int         oflag;
        char const *path;
};

typedef struct tyspawn {
        int              flags;
        pid_t            pgroup;
        sigset_t         sigdef;
        mode_t           umask;
        int              pdeathsig;
        int              err;
        int              nact;
        struct spawn_act act[TY_SPAWN_MAX_ACTIONS];
        int              nkeep;
        int              keep[TY_SPAWN_MAX_KEEP];
        uint64_t         rlimset;
        struct rlimit    rlim[TY_RLIM_N];
} TySpawn;

void
TySpawnInit(TySpawn *sp);

void
spawn_close(TySpawn *sp, int fd);

void
spawn_dup2(TySpawn *sp, int fd, int newfd);

void
spawn_open(TySpawn *sp, int fd, char const *path, int oflag);

void
spawn_chdir(TySpawn *sp, char const *path);

void
spawn_fchdir(TySpawn *sp, int fd);

void
spawn_setpgroup(TySpawn *sp, pid_t pgroup);

void
spawn_setsid(TySpawn *sp);

void
spawn_closefds(TySpawn *sp);

void
spawn_keep(TySpawn *sp, int fd);

void
spawn_rlimit(TySpawn *sp, int resource, struct rlimit const *rlim);

void
spawn_sigdefault(TySpawn *sp, int sig);

void
spawn_umask(TySpawn *sp, mode_t mask);

void
spawn_pdeathsig(TySpawn *sp, int sig);

int
TySpawnRun(
        TySpawn const *sp,
        pid_t *pid,
        char const *file,
        char *const argv[],
        char *const envp[]
);

#endif
