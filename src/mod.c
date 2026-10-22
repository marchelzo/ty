#include <errno.h>
#include <spawn.h>
#include <sys/wait.h>

#include <xxhash.h>

#include "mod.h"
#include "ty.h"
#include "table.h"
#include "value.h"
#include "vm.h"
#include "scope.h"
#include "compiler.h"
#include "dict.h"
#include "json.h"

#ifdef TY_EMBED_LIB
#include "bundle.h"
#endif

#define MANIFEST "ty.toml"
#define ENVFILE  ".ty/env.json"

extern char **environ;

void
mod_init(TY *ty)
{
        table_init(ty->ty, &ty->pkg);
        table_init(ty->ty, &ty->env);
}

static Array *
SearchPath(Ty *ty)
{
        return v_(Globals, NAMES.path)->array;
}

static u64
SearchGen(Ty *ty)
{
        Array *search = SearchPath(ty);
        u64 h = 0xcbf29ce484222325ULL ^ vN(*search);

        for (int i = 0; i < vN(*search); ++i) {
                Value const *dir = v_(*search, i);
                if (dir->type != VALUE_STRING) {
                        continue;
                }
                for (usize k = 0; k < sN(*dir); ++k) {
                        h = (h ^ (u8)ss(*dir)[k]) * 0x100000001b3ULL;
                }
                h = (h ^ '\n') * 0x100000001b3ULL;
        }

        return h;
}

static bool
InSearchPath(Ty *ty, char const *dir)
{
        Array *search = SearchPath(ty);

        for (int i = 0; i < vN(*search); ++i) {
                Value const *v = v_(*search, i);
                if (v->type == VALUE_STRING && vs_eq_z(*v, dir)) {
                        return true;
                }
        }

        return false;
}

static char const *
StartDir(Ty *ty, char const *from, char *buf, char *real)
{
        char *dir;

        if (from == NULL || strchr(from, '/') == NULL) {
                if ((dir = getcwd(buf, PATH_MAX)) == NULL) {
                        return "/";
                }
        } else {
                dir = directory_of(from, buf);
        }

        return (realpath(dir, real) != NULL) ? real : dir;
}

static Package *
NewPackage(Ty *ty, char const *dir, char const *manifest, u8 kind)
{
        Package *pkg = ty_malloc(sizeof *pkg);

        if (UNLIKELY(pkg == NULL)) {
                panic("out of memory");
        }

        *pkg = (Package) {
                .dir      = S2(dir),
                .manifest = S2N(manifest),
                .gen      = SearchGen(ty),
                .kind     = kind,
                .read     = (kind != PKG_DECLARED)
        };

        xvP(pkg->roots, pkg->dir);

        return pkg;
}

static Package *
EnvPackage(Ty *ty, char const *dir)
{
        Value const *hit = table_look(ty, &ty->ty->env, dir);
        return (hit == NULL) ? NULL : hit->ptr;
}

static Package *
FindPackage(Ty *ty, char const *from)
{
        char buf0[PATH_MAX + 1];
        char buf1[PATH_MAX + 1];
        char real[PATH_MAX + 1];
        char const *start = StartDir(ty, from, buf0, real);
        u64 gen = SearchGen(ty);

        Value const *hit = table_look(ty, &ty->ty->pkg, start);

        if (hit != NULL && ((Package *)hit->ptr)->gen == gen) {
                return hit->ptr;
        }

        ConstStringVector seen = {0};
        Package *pkg = NULL;
        char const *dir = start;

        SCRATCH_SAVE();
        for (;;) {
                dir = sfmt("%s", dir);
                svP(seen, dir);
                if ((pkg = EnvPackage(ty, dir)) != NULL) {
                        break;
                }
                if (InSearchPath(ty, dir)) {
                        pkg = NewPackage(ty, start, NULL, PKG_LIBRARY);
                        vN(seen) = 1;
                        break;
                }
                char const *base = s_eq(dir, "/") ? "" : dir;
                char const *manifest = sfmt("%s/" MANIFEST, base);
                if (access(manifest, R_OK) == 0) {
                        pkg = NewPackage(ty, dir, manifest, PKG_DECLARED);
                        break;
                }
                if (access(sfmt("%s/.git", base), F_OK) == 0) {
                        break;
                }
                char *up = directory_of(dir, buf1);
                if (s_eq(up, dir)) {
                        break;
                }
                dir = up;
        }

        if (pkg == NULL) {
                pkg = NewPackage(ty, start, NULL, PKG_IMPLICIT);
                vN(seen) = 1;
        }

        for (int i = 0; i < vN(seen); ++i) {
                Value *slot = table_look(ty, &ty->ty->pkg, v__(seen, i));
                if (slot != NULL) {
                        *slot = PTR(pkg);
                } else {
                        table_put(ty, &ty->ty->pkg, S2(v__(seen, i)), &PTR(pkg));
                }
        }
        SCRATCH_RESTORE();

        return pkg;
}

char const *
mod_root(Ty *ty, char const *path)
{
        if (path == NULL || strchr(path, '/') == NULL) {
                return NULL;
        }

        return FindPackage(ty, path)->dir;
}

char const *
mod_kind_name(Package const *pkg)
{
        switch (pkg->kind) {
        case PKG_DECLARED: return "declared";
        case PKG_LIBRARY:  return "library";
        default:           return "implicit";
        }
}

char const *
mod_native(Package const *pkg, char const *name)
{
        for (int i = 0; i + 1 < vN(pkg->natives); i += 2) {
                if (s_eq(v__(pkg->natives, i), name)) {
                        return v__(pkg->natives, i + 1);
                }
        }

        return NULL;
}

char *
mod_stamp(char const *path)
{
        byte_vector data = {0};
        char hex[17];

        if (!xslurp(path, &data)) {
                return NULL;
        }

        ty_snprintf(hex, sizeof hex, "%016llx", (unsigned long long)XXH3_64bits(vv(data), vN(data)));
        xvF(data);

        return S2(hex);
}

static Value const *
Field(Ty *ty, Value const *v, char const *name)
{
        return (v->type == VALUE_DICT) ? dict_get_member(ty, v->dict, name) : NULL;
}

static bool
IsA(Value const *v, int type)
{
        return (v != NULL) && (v->type == type);
}

static char const *
EnvPath(char const *base, char const *s, char *buf)
{
        char joined[PATH_MAX + 1];

        if (s[0] == '/') {
                return s;
        }

        ty_snprintf(joined, sizeof joined, "%s/%s", base, s);

        return (realpath(joined, buf) != NULL) ? buf : strcpy(buf, joined);
}

static bool
SameStamp(Ty *ty, char const *base, Value const *input)
{
        char buf[PATH_MAX + 1];

        if (
                !IsA(input, VALUE_ARRAY)
             || (vN(*input->array) != 2)
             || !IsA(v_(*input->array, 0), VALUE_STRING)
        ) {
                return false;
        }

        Value const *want = v_(*input->array, 1);
        char *have = mod_stamp(EnvPath(base, TY_TMP_C_STR(*v_(*input->array, 0)), buf));
        bool same = IsA(want, VALUE_STRING) ? (have != NULL && vs_eq_z(*want, have))
                  :                           (have == NULL);

        ty_free(have);

        return same;
}

static bool
EnvFresh(Ty *ty, char const *base, Value const *env)
{
        char buf[PATH_MAX + 1];

        Value const *version  = Field(ty, env, "version");
        Value const *inputs   = Field(ty, env, "inputs");
        Value const *packages = Field(ty, env, "packages");

        if (
                !IsA(version,  VALUE_INTEGER)
             || !IsA(inputs,   VALUE_ARRAY)
             || !IsA(packages, VALUE_ARRAY)
             || (version->z != 1)
        ) {
                return false;
        }

        vfor(*inputs->array, {
                if (!SameStamp(ty, base, it)) {
                        return false;
                }
        });

        vfor(*packages->array, {
                Value const *dir = Field(ty, it, "dir");
                if (!IsA(dir, VALUE_STRING) || access(EnvPath(base, TY_TMP_C_STR(*dir), buf), F_OK) != 0) {
                        return false;
                }
        });

        return true;
}

static Value
ReadEnv(Ty *ty, char const *path)
{
        byte_vector text = {0};
        Value env;

        if (!xslurp(path, &text)) {
                return NIL;
        }

        Value src = vSs(vv(text), vN(text));
        xvF(text);

        if (TY_CATCH_ERROR()) {
                (void)TY_CATCH();
                return NIL;
        }

        env = json_parse(ty, &src);

        TY_CATCH_END();

        return env;
}

static bool
SyncEnv(Package const *pkg)
{
        char self[PATH_MAX + 1];
        int status;
        pid_t pid;
        int n = 0;

        if (getenv("TY_NO_SYNC") != NULL || !executable_path(self, sizeof self)) {
                return false;
        }

#ifdef TY_EMBED_LIB
        if (bundle_dir() != NULL) {
                return false;
        }
#endif

        while (environ[n] != NULL) {
                n += 1;
        }

        char **envp = xmA((n + 2) * sizeof *envp);
        memcpy(envp, environ, n * sizeof *envp);
        envp[n]     = "TY_NO_SYNC=1";
        envp[n + 1] = NULL;

        char *argv[] = { self, "--pm", "sync", "--auto", "--project", (char *)pkg->dir, NULL };
        int rc = posix_spawn(&pid, self, NULL, NULL, argv, envp);

        xmF(envp);

        if (rc != 0) {
                return false;
        }

        while (waitpid(pid, &status, 0) < 0) {
                if (errno != EINTR) {
                        return false;
                }
        }

        return WIFEXITED(status) && (WEXITSTATUS(status) == 0);
}

static void
AdoptStrings(Ty *ty, char const *base, ConstStringVector *out, Value const *v)
{
        char buf[PATH_MAX + 1];

        if (!IsA(v, VALUE_ARRAY)) {
                return;
        }

        vfor(*v->array, {
                if (it->type == VALUE_STRING) {
                        xvP(*out, S2(EnvPath(base, TY_TMP_C_STR(*it), buf)));
                }
        });
}

static void
AdoptPairs(Ty *ty, char const *base, ConstStringVector *out, Value const *v, bool modules)
{
        char buf[PATH_MAX + 1];

        if (!IsA(v, VALUE_DICT)) {
                return;
        }

        dfor(v->dict, {
                if (key->type == VALUE_STRING && val->type == VALUE_STRING) {
                        xvP(*out, modules ? mod_name(ty, TY_TMP_C_STR(*key)) : S2(TY_TMP_C_STR(*key)));
                        xvP(*out, S2(EnvPath(base, TY_TMP_C_STR(*val), buf)));
                }
        });
}

static void
AdoptEnvPackage(Ty *ty, char const *base, Package *pkg, Value const *entry)
{
        v0(pkg->roots);
        v0(pkg->deps);
        v0(pkg->natives);

        AdoptStrings(ty, base, &pkg->roots,   Field(ty, entry, "roots"));
        AdoptPairs(  ty, base, &pkg->deps,    Field(ty, entry, "deps"),    true);
        AdoptPairs(  ty, base, &pkg->natives, Field(ty, entry, "natives"), false);

        if (vN(pkg->roots) == 0) {
                xvP(pkg->roots, pkg->dir);
        }

        pkg->read = true;
}

static void
LoadEnv(Ty *ty, Package *pkg)
{
        char path[PATH_MAX + 1];
        char manifest[PATH_MAX + 1];
        char buf[PATH_MAX + 1];
        Value env;

        ty_snprintf(path, sizeof path, "%s/" ENVFILE, pkg->dir);

        GC_STOP();

        env = ReadEnv(ty, path);

        if (!EnvFresh(ty, pkg->dir, &env)) {
                bool synced = SyncEnv(pkg);
                env = synced ? ReadEnv(ty, path) : NIL;
                if (!synced || !EnvFresh(ty, pkg->dir, &env)) {
                        GC_RESUME();
                        if (getenv("TY_NO_SYNC") != NULL) {
                                zP("%s: the package environment is out of date; run `tpm sync`", pkg->manifest);
                        }
                        zP("%s: `tpm sync` failed", pkg->manifest);
                }
        }

        vfor(*Field(ty, &env, "packages")->array, {
                Value const *dir = Field(ty, it, "dir");
                if (!IsA(dir, VALUE_STRING)) {
                        continue;
                }
                char const *d = EnvPath(pkg->dir, TY_TMP_C_STR(*dir), buf);
                Package *p = s_eq(d, pkg->dir) ? pkg : EnvPackage(ty, d);
                if (p == NULL) {
                        ty_snprintf(manifest, sizeof manifest, "%s/" MANIFEST, d);
                        p = NewPackage(ty, d, manifest, PKG_DECLARED);
                } else if (p != pkg) {
                        continue;
                }
                AdoptEnvPackage(ty, pkg->dir, p, it);
                table_put(ty, &ty->ty->env, p->dir, &PTR(p));
        });

        GC_RESUME();
}

static void
PackageRead(Ty *ty, Package *pkg)
{
        if (pkg->read || pkg->reading) {
                return;
        }

        pkg->reading = true;

        if (TY_CATCH_ERROR()) {
                pkg->reading = false;
                TY_RETHROW();
        }

        LoadEnv(ty, pkg);

        TY_CATCH_END();

        pkg->reading = false;
        pkg->read = true;
}

Package *
mod_package(Ty *ty, char const *from)
{
        Package *pkg = FindPackage(ty, from);
        PackageRead(ty, pkg);
        return pkg;
}

static char const *
Probe(ConstStringVector *tried, char const *fmt, ...)
{
        char path[PATH_MAX + 1];
        char real[PATH_MAX + 1];
        va_list ap;

        va_start(ap, fmt);
        ty_vsnprintf(path, sizeof path, fmt, ap);
        va_end(ap);

        if (tried != NULL) {
                xvP(*tried, S2(path));
        }

        if (
                (access(path, R_OK) != 0)
             || (realpath(path, real) == NULL)
        ) {
                return NULL;
        }

        return S2(real);
}

static char const *
ProbeSearchPath(Ty *ty, char const *name, ConstStringVector *tried)
{
        Array *search = SearchPath(ty);
        char const *hit;

        for (int i = 0; i < vN(*search); ++i) {
                Value const *dir = v_(*search, i);
                if (dir->type != VALUE_STRING) {
                        continue;
                }
                hit = Probe(tried, "%.*s/%s.ty", (int)sN(*dir), ss(*dir), name);
                if (hit != NULL) {
                        return hit;
                }
        }

        return NULL;
}

static char const *
ProbeDeps(Package const *pkg, char const *name, ConstStringVector *tried)
{
        for (int i = 0; i + 1 < vN(pkg->deps); i += 2) {
                char const *dep = v__(pkg->deps, i);
                char const *dir = v__(pkg->deps, i + 1);
                usize n = strlen(dep);
                if (!s_eq_n(name, dep, n)) {
                        continue;
                }
                switch (name[n]) {
                case '\0': return Probe(tried, "%s.ty", dir);
                case '/':  return Probe(tried, "%s/%s.ty", dir, name + n + 1);
                }
        }

        return NULL;
}

static char const *
ProbeRoots(Package const *pkg, char const *name, ConstStringVector *tried)
{
        char const *hit;

        for (int i = 0; i < vN(pkg->roots); ++i) {
                hit = Probe(tried, "%s/%s.ty", v__(pkg->roots, i), name);
                if (hit != NULL) {
                        return hit;
                }
        }

        return NULL;
}

char const *
mod_resolve(Ty *ty, char const *name, char const *from, bool library, ConstStringVector *tried)
{
        char buf[PATH_MAX + 1];
        char real[PATH_MAX + 1];

        if (library) {
                return ProbeSearchPath(ty, name, tried);
        }

        if (s_eq_n(name, "./", 2)) {
                return Probe(tried, "%s/%s.ty", StartDir(ty, from, buf, real), name + 2);
        }

        Package *pkg = mod_package(ty, from);

        if (s_eq_n(name, "../", 3)) {
                return Probe(tried, "%s/%s.ty", pkg->dir, name);
        }

        switch (pkg->kind) {
        case PKG_DECLARED:
                return ProbeDeps(pkg, name, tried)
                    ?: ProbeRoots(pkg, name, tried)
                    ?: ProbeSearchPath(ty, name, tried);

        default:
                return ProbeSearchPath(ty, name, tried)
                    ?: ProbeRoots(pkg, name, tried);
        }
}

char const *
mod_rival(Ty *ty, char const *name, char const *from, char const *path, bool *library)
{
        char const *lib;
        char const *own;
        char const *rival = NULL;

        if (
                (path == NULL)
             || s_eq_n(name, "./", 2)
             || s_eq_n(name, "../", 3)
        ) {
                return NULL;
        }

        Package *pkg = mod_package(ty, from);

        lib = ProbeSearchPath(ty, name, NULL);
        own = ProbeDeps(pkg, name, NULL) ?: ProbeRoots(pkg, name, NULL);

        bool rivals = (lib != NULL) && (own != NULL) && !s_eq(lib, own);

        if (rivals && s_eq(path, own)) {
                rival    = lib;
                *library = true;
        } else if (rivals && s_eq(path, lib)) {
                rival    = own;
                *library = false;
        }

        if (lib != rival) {
                ty_free((void *)lib);
        }

        if (own != rival) {
                ty_free((void *)own);
        }

        return rival;
}

char *
mod_name(Ty *ty, char const *dotted)
{
        byte_vector name = {0};
        char const *s = dotted;

        if (strchr(s, '/') != NULL) {
                return S2(s);
        }

        if (*s == '.') {
                xvP(name, '.');
                xvP(name, '/');
                for (s += 1; *s == '.'; ++s) {
                        xvPn(name, "../", 3);
                }
        }

        while (s_eq_n(s, "super.", 6)) {
                xvPn(name, "../", 3);
                s += 6;
        }

        for (; *s != '\0'; ++s) {
                xvP(name, (*s == '.') ? '/' : *s);
        }

        xvP(name, '\0');

        return vv(name);
}

/* vim: set sts=8 sw=8 expandtab: */
