#include <ctype.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <windows.h>
#include <shlobj.h>
#else
#include <pwd.h>
#include <unistd.h>
#endif

#include "dirs.h"

#if defined(_WIN32)
#define SEP       "\\"
#define HOME_VAR  "USERPROFILE"
#define USER_VAR  "USERNAME"
#define HOME_ROOT "C:\\Users\\"
#elif defined(__APPLE__)
#define SEP       "/"
#define HOME_VAR  "HOME"
#define USER_VAR  "USER"
#define HOME_ROOT "/Users/"
#else
#define SEP       "/"
#define HOME_VAR  "HOME"
#define USER_VAR  "USER"
#define HOME_ROOT "/home/"
#endif

char const *const DirNames[DIR_COUNT] = {
#define X(d) #d,
        TY_DIRS(X)
#undef X
};

static char const     *Dirs[DIR_COUNT];
static bool            Ready = false;
static pthread_mutex_t Lock  = PTHREAD_MUTEX_INITIALIZER;

static char const *const Vars[] = {
        HOME_VAR,
        USER_VAR,
        "TMPDIR",
        "HOMEDRIVE",
        "HOMEPATH",
        "APPDATA",
        "LOCALAPPDATA",
        "PUBLIC",
};

static char *
Join(char const *dir, char const *sub, usize n)
{
        if (dir == NULL) {
                return NULL;
        }

        usize m = strlen(dir) + sizeof SEP + n;
        char *p = malloc(m);

        snprintf(p, m, "%s" SEP "%.*s", dir, (int)n, sub);

        return p;
}

inline static char *
Sub(char const *dir, char const *sub)
{
        return Join(dir, sub, strlen(sub));
}

inline static bool
absolute(char const *p)
{
#ifdef _WIN32
        return (isalpha((u8)p[0]) && p[1] == ':')
            || (p[0] == '\\' && p[1] == '\\')
            || (p[0] == '/');
#else
        return (p[0] == '/');
#endif
}

static char const *
Temp(void)
{
        usize       n;
        char const *dir = dirs_tmp(&n);

        return strndup(dir, n);
}

static char const *
Xdg(char const *var, char const *dir, char const *sub)
{
        char const *p = getenv(var);

        return (p != NULL && absolute(p)) ? strdup(p)
             : (sub != NULL)              ? Sub(dir, sub)
             :                              NULL;
}

inline static bool
set(char const *s)
{
        return (s != NULL) && (*s != '\0');
}

static char const *
Runtime(void)
{
        char const *dir = Xdg("XDG_RUNTIME_DIR", NULL, NULL);
        return (dir != NULL) ? dir : Temp();
}

static char const *
Home(void)
{
        char const *home = getenv(HOME_VAR);
        char const *user = getenv(USER_VAR);
        char        buf[4096];

        if (set(home)) {
                return strdup(home);
        }

#ifdef _WIN32
        char const *drive = getenv("HOMEDRIVE");
        char const *path  = getenv("HOMEPATH");

        if (set(drive) && set(path)) {
                snprintf(buf, sizeof buf, "%s%s", drive, path);
                return strdup(buf);
        }

        if (SUCCEEDED(SHGetFolderPathA(NULL, CSIDL_PROFILE, NULL, 0, buf))) {
                return strdup(buf);
        }
#else
        struct passwd  pw;
        struct passwd *res = NULL;

        if (
                (getpwuid_r(getuid(), &pw, buf, sizeof buf, &res) == 0)
             && (res != NULL)
             && set(res->pw_dir)
        ) {
                return strdup(res->pw_dir);
        }

        user = set(user) ? user : getlogin();
#endif

        snprintf(buf, sizeof buf, HOME_ROOT "%s", set(user) ? user : "nobody");

        return strdup(buf);
}

#if !defined(_WIN32) && !defined(__APPLE__)
static struct {
        char const *key;
        int         dir;
} const UserDirs[] = {
        { "DESKTOP",     DIR_DESKTOP   },
        { "DOCUMENTS",   DIR_DOCUMENTS },
        { "DOWNLOAD",    DIR_DOWNLOADS },
        { "MUSIC",       DIR_AUDIO     },
        { "PICTURES",    DIR_PICTURES  },
        { "PUBLICSHARE", DIR_PUBLIC    },
        { "TEMPLATES",   DIR_TEMPLATES },
        { "VIDEOS",      DIR_VIDEOS    },
};

static void
UserDir(char const *line)
{
        char const *key = line + 4;
        char const *eq  = strstr(line, "_DIR=\"");
        char const *v;
        char const *end;

        if (strncmp(line, "XDG_", 4) != 0 || eq == NULL || eq < key) {
                return;
        }

        v   = eq + 6;
        end = strrchr(v, '"');

        if (end == NULL) {
                return;
        }

        for (usize i = 0; i < countof(UserDirs); ++i) {
                if (
                        (strlen(UserDirs[i].key) != (usize)(eq - key))
                     || (strncmp(UserDirs[i].key, key, eq - key) != 0)
                ) {
                        continue;
                }

                free((char *)Dirs[UserDirs[i].dir]);

                if (strncmp(v, "$HOME", 5) == 0 && (v[5] == '/' || v + 5 == end)) {
                        v += 5 + (v[5] == '/');
                        Dirs[UserDirs[i].dir] = Join(Dirs[DIR_HOME], v, end - v);
                } else {
                        Dirs[UserDirs[i].dir] = strndup(v, end - v);
                }

                return;
        }
}

static void
ReadUserDirs(void)
{
        char  line[4096];
        char *path = Sub(Dirs[DIR_CONFIG], "user-dirs.dirs");
        FILE *f    = (path != NULL) ? fopen(path, "r") : NULL;

        free(path);

        if (f == NULL) {
                return;
        }

        while (fgets(line, sizeof line, f) != NULL) {
                UserDir(line);
        }

        fclose(f);
}
#endif

static void
Init(void)
{
/* ========================================================================= */
#define D(d) Dirs[DIR_##d]
/* ------------------------------------------------------------------------- */
        D(HOME) = Home();

#if defined(_WIN32)
        D(CACHE)        = Xdg("LOCALAPPDATA", D(HOME), "AppData\\Local");
        D(CONFIG)       = Xdg("APPDATA",      D(HOME), "AppData\\Roaming");
        D(CONFIG_LOCAL) = D(CACHE);
        D(DATA)         = D(CONFIG);
        D(DATA_LOCAL)   = D(CACHE);
        D(PREFERENCES)  = D(CONFIG);
        D(EXECUTABLES)  = Sub(D(HOME), ".local\\bin");
        D(RUNTIME)      = Temp();
        D(STATE)        = D(DATA_LOCAL);

        D(AUDIO)        = Sub(D(HOME),  "Music");
        D(DESKTOP)      = Sub(D(HOME),  "Desktop");
        D(DOCUMENTS)    = Sub(D(HOME),  "Documents");
        D(DOWNLOADS)    = Sub(D(HOME),  "Downloads");
        D(FONTS)        = Sub(D(CACHE), "Microsoft\\Windows\\Fonts");
        D(PICTURES)     = Sub(D(HOME),  "Pictures");
        D(PUBLIC)       = Xdg("PUBLIC", D(HOME), "Public");
        D(TEMPLATES)    = Sub(D(CONFIG), "Microsoft\\Windows\\Templates");
        D(VIDEOS)       = Sub(D(HOME),  "Videos");
#elif defined(__APPLE__)
        char *lib = Sub(D(HOME), "Library");

        D(CACHE)        = Xdg("XDG_CACHE_HOME",  lib, "Caches");
        D(CONFIG)       = Xdg("XDG_CONFIG_HOME", lib, "Application Support");
        D(CONFIG_LOCAL) = D(CONFIG);
        D(DATA)         = Xdg("XDG_DATA_HOME",   lib, "Application Support");
        D(DATA_LOCAL)   = D(DATA);
        D(PREFERENCES)  = Sub(lib, "Preferences");
        D(EXECUTABLES)  = Xdg("XDG_BIN_HOME",    D(HOME), ".local/bin");
        D(RUNTIME)      = Runtime();
        D(STATE)        = Xdg("XDG_STATE_HOME",  lib,     "Application Support");

        D(AUDIO)        = Sub(D(HOME), "Music");
        D(DESKTOP)      = Sub(D(HOME), "Desktop");
        D(DOCUMENTS)    = Sub(D(HOME), "Documents");
        D(DOWNLOADS)    = Sub(D(HOME), "Downloads");
        D(FONTS)        = Sub(lib,     "Fonts");
        D(PICTURES)     = Sub(D(HOME), "Pictures");
        D(PUBLIC)       = Sub(D(HOME), "Public");
        D(TEMPLATES)    = Sub(D(HOME), "Templates");
        D(VIDEOS)       = Sub(D(HOME), "Movies");

        free(lib);
#else
        D(CACHE)        = Xdg("XDG_CACHE_HOME",  D(HOME), ".cache");
        D(CONFIG)       = Xdg("XDG_CONFIG_HOME", D(HOME), ".config");
        D(CONFIG_LOCAL) = D(CONFIG);
        D(DATA)         = Xdg("XDG_DATA_HOME",   D(HOME), ".local/share");
        D(DATA_LOCAL)   = D(DATA);
        D(PREFERENCES)  = D(CONFIG);
        D(EXECUTABLES)  = Xdg("XDG_BIN_HOME",    D(HOME), ".local/bin");
        D(RUNTIME)      = Runtime();
        D(STATE)        = Xdg("XDG_STATE_HOME",  D(HOME), ".local/state");
        D(FONTS)        = Sub(D(DATA), "fonts");

        D(AUDIO)        = Sub(D(HOME), "Music");
        D(DESKTOP)      = Sub(D(HOME), "Desktop");
        D(DOCUMENTS)    = Sub(D(HOME), "Documents");
        D(DOWNLOADS)    = Sub(D(HOME), "Downloads");
        D(PICTURES)     = Sub(D(HOME), "Pictures");
        D(PUBLIC)       = Sub(D(HOME), "Public");
        D(TEMPLATES)    = Sub(D(HOME), "Templates");
        D(VIDEOS)       = Sub(D(HOME), "Videos");

        ReadUserDirs();
#endif
/* ------------------------------------------------------------------------- */
#undef D
/* ========================================================================= */
}

char const *
dirs_tmp(usize *n)
{
#ifdef _WIN32
        static _Thread_local char buf[MAX_PATH + 1];
        DWORD       w    = GetTempPathA(sizeof buf, buf);
        char const *dir  = (w == 0 || w >= sizeof buf) ? "." : buf;
        char const *seps = "/\\";
#else
        char const *dir  = set(getenv("TMPDIR")) ? getenv("TMPDIR") : "/tmp";
        char const *seps = "/";
#endif

        *n = strlen(dir);

        while (*n > 1 && strchr(seps, dir[*n - 1]) != NULL) {
                *n -= 1;
        }

        return dir;
}

char const *
dirs_get(int which)
{
        char const *dir;

        pthread_mutex_lock(&Lock);

        if (!Ready) {
                Init();
                Ready = true;
        }

        dir = Dirs[which];

        pthread_mutex_unlock(&Lock);

        return dir;
}

bool
dirs_affected(char const *var)
{
        if (strncmp(var, "XDG_", 4) == 0) {
                return true;
        }

        for (usize i = 0; i < countof(Vars); ++i) {
                if (strcmp(var, Vars[i]) == 0) {
                        return true;
                }
        }

        return false;
}

void
dirs_reload(void)
{
        pthread_mutex_lock(&Lock);
        Init();
        Ready = true;
        pthread_mutex_unlock(&Lock);
}

bool
dirs_path(char *out, usize n, int which, char const *fmt, ...)
{
        char const *dir = dirs_get(which);
        va_list     ap;
        int         k;

        if (dir == NULL) {
                return false;
        }

        k = snprintf(out, n, "%s" SEP, dir);

        if (k < 0 || (usize)k >= n) {
                return false;
        }

        va_start(ap, fmt);
        int m = vsnprintf(out + k, n - k, fmt, ap);
        va_end(ap);

        return (m >= 0) && ((usize)m < n - k);
}

/* vim: set sts=8 sw=8 expandtab: */
