#include "mod.h"
#include "ty.h"
#include "table.h"
#include "value.h"
#include "vm.h"
#include "scope.h"
#include "compiler.h"

#define MANIFEST "__pkg__.ty"

void
mod_init(TY *ty)
{
        table_init(ty->ty, &ty->pkg);
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

static char const *
PackagePath(Ty *ty, Package const *pkg, char const *what, Value const *v)
{
        char path[PATH_MAX + 1];
        char real[PATH_MAX + 1];
        char const *home = getenv("HOME");

        if (v->type != VALUE_STRING) {
                zP("%s: %s must hold strings, found %s", pkg->manifest, what, VSC(v));
        }

        int n = (int)sN(*v);
        char const *s = (char const *)ss(*v);

        if (n > 0 && s[0] == '/') {
                ty_snprintf(path, sizeof path, "%.*s", n, s);
        } else if (n > 1 && s[0] == '~' && s[1] == '/' && home != NULL) {
                ty_snprintf(path, sizeof path, "%s%.*s", home, n - 1, s + 1);
        } else {
                ty_snprintf(path, sizeof path, "%s/%.*s", pkg->dir, n, s);
        }

        return S2((realpath(path, real) != NULL) ? real : path);
}

static Value const *
ManifestConstant(Ty *ty, Module const *mod, char const *name)
{
        Symbol *sym = scope_local_lookup(ty, mod->scope, name);
        return (sym == NULL) ? NULL : vm_global(ty, sym->i);
}

static void
ReadRoots(Ty *ty, Package *pkg, Value const *roots)
{
        if (roots == NULL || roots->type == VALUE_NIL) {
                return;
        }

        v0(pkg->roots);

        switch (roots->type) {
        case VALUE_STRING:
                xvP(pkg->roots, PackagePath(ty, pkg, "ROOTS", roots));
                break;

        case VALUE_ARRAY:
                for (int i = 0; i < vN(*roots->array); ++i) {
                        xvP(pkg->roots, PackagePath(ty, pkg, "ROOTS", v_(*roots->array, i)));
                }
                break;

        default:
                zP("%s: ROOTS must be a String or Array[String], found %s", pkg->manifest, VSC(roots));
        }
}

static void
ReadDeps(Ty *ty, Package *pkg, Value const *deps)
{
        if (deps == NULL || deps->type == VALUE_NIL) {
                return;
        }

        if (deps->type != VALUE_DICT) {
                zP("%s: DEPS must be a Dict[String, String], found %s", pkg->manifest, VSC(deps));
        }

        v0(pkg->deps);

        dfor(deps->dict, {
                if (key->type != VALUE_STRING) {
                        zP("%s: DEPS must be keyed by strings, found %s", pkg->manifest, VSC(key));
                }
                xvP(pkg->deps, mod_name(ty, TY_TMP_C_STR(*key)));
                xvP(pkg->deps, PackagePath(ty, pkg, "DEPS", val));
        });
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

        Module *mod = compiler_load_manifest(ty, pkg->manifest);

        ReadRoots(ty, pkg, ManifestConstant(ty, mod, "ROOTS"));
        ReadDeps(ty, pkg, ManifestConstant(ty, mod, "DEPS"));

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
