#include <ctype.h>
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

#include "ty/thread.h"
#include "xd.h"
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
static TyMutex Lock  = TY_MUTEX_INIT;

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

inline static char *
Sub(char const *dir, char const *sub)
{
        return xfmt("%s" SEP "%s", dir, sub);
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
Xdg(char const *var, char const *dir, char const *sub)
{
        char const *p = getenv(var);

        return (p != NULL && absolute(p)) ? S2(p)
             : (sub != NULL)              ? Sub(dir, sub)
             :                              NULL;
}

inline static bool
set(char const *s)
{
        return (s != NULL) && (*s != '\0');
}

static char const *
Temp(void)
{
        Bytes path = dirs_tmp();
        return S2n(bb(path), bN(path));
}

static char const *
Home(void)
{
        char buf[4096];

        char const *home = getenv(HOME_VAR);
        char const *user = getenv(USER_VAR);

        if (set(home)) {
                return S2(home);
        }

#ifdef _WIN32
        char const *drive = getenv("HOMEDRIVE");
        char const *path  = getenv("HOMEPATH");

        if (set(drive) && set(path)) {
                return xfmt("%s%s", drive, path);
        }

        if (SUCCEEDED(SHGetFolderPathA(NULL, CSIDL_PROFILE, NULL, 0, buf))) {
                return S2(buf);
        }
#else
        struct passwd  pw;
        struct passwd *res = NULL;

        if (
                (getpwuid_r(getuid(), &pw, buf, sizeof buf, &res) == 0)
             && (res != NULL)
             && set(res->pw_dir)
        ) {
                return S2(res->pw_dir);
        }

        user = set(user) ? user : getlogin();
#endif

        return xfmt("%s", set(user) ? user : "nobody");
}

static char const *
Runtime(void)
{
        char const *dir = Xdg("XDG_RUNTIME_DIR", NULL, NULL);
        return (dir != NULL) ? dir : Temp();
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
        char const *_key = line + 4;
        char const *eq  = strstr(line, "_DIR=\"");
        char const *val;
        char const *end;

        if (!s_eq_n(line, "XDG_", 4) || eq == NULL || eq < _key) {
                return;
        }

        val = eq + 6;
        end = strrchr(val, '"');

        if (end == NULL) {
                return;
        }

        Bytes key = BYTES(_key, eq - _key);

        for (usize i = 0; i < countof(UserDirs); ++i) {
                if (!bytes_eq(key, UserDirs[i].key)) {
                        continue;
                }

                ty_free((char *)Dirs[UserDirs[i].dir]);

                if (s_eq_n(val, "$HOME", 5) && (val[5] == '/' || val + 5 == end)) {
                        val += 5 + (val[5] == '/');
                        Dirs[UserDirs[i].dir] = xfmt("%s" SEP "%.*s", Dirs[DIR_HOME], (int)(end - val), val);
                } else {
                        Dirs[UserDirs[i].dir] = S2n(val, end - val);
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

        xmF(path);

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

        xmF(lib);
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
dirs_get(int which)
{
        char const *dir;

        TyMutexLock(&Lock);

        if (!Ready) {
                Init();
                Ready = true;
        }

        dir = Dirs[which];

        TyMutexUnlock(&Lock);

        return dir;
}

bool
dirs_affected(char const *var)
{
        if (s_eq_n(var, "XDG_", 4)) {
                return true;
        }

        for (usize i = 0; i < countof(Vars); ++i) {
                if (s_eq(var, Vars[i])) {
                        return true;
                }
        }

        return false;
}

void
dirs_reload(void)
{
        TyMutexLock(&Lock);
        Init();
        Ready = true;
        TyMutexUnlock(&Lock);
}

Bytes
dirs_tmp(void)
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

        usize n = strlen(dir);

        while (n > 1 && strchr(seps, dir[n - 1]) != NULL) {
                n -= 1;
        }

        return BYTES(dir, n);
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

        k = ty_snprintf(out, n, "%s" SEP, dir);

        if (k < 0 || (usize)k >= n) {
                return false;
        }

        va_start(ap, fmt);
        int m = ty_vsnprintf(out + k, n - k, fmt, ap);
        va_end(ap);

        return (m >= 0) && ((usize)m < n - k);
}

/* vim: set sts=8 sw=8 expandtab: */
