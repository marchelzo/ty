#ifdef TY_EMBED_LIB

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <spawn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#if defined(__APPLE__)
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#else
#include <link.h>
#endif

#include <xxhash.h>

#include "ty.h"
#include "vm.h"
#include "xd.h"
#include "compiler.h"
#include "mod.h"
#include "bundle.h"

extern char **environ;

typedef struct {
        char **items;
        int    n;
} List;

typedef struct {
        char  *data;
        usize  n;
        usize  cap;
} Buf;

typedef struct {
        char *rel;
        char *path;
        u32   mode;
} File;

typedef struct {
        File *items;
        int   n;
} Files;

static List Before;

static void
lput(List *l, char const *s)
{
        l->items = realloc(l->items, (l->n + 1) * sizeof *l->items);
        l->items[l->n++] = strdup(s);
}

static bool
lhas(List const *l, char const *s)
{
        for (int i = 0; i < l->n; ++i) {
                if (strcmp(l->items[i], s) == 0) {
                        return true;
                }
        }

        return false;
}

static void
bput(Buf *b, void const *p, usize n)
{
        if (b->n + n > b->cap) {
                b->cap  = 2 * (b->n + n);
                b->data = realloc(b->data, b->cap);
        }

        memcpy(b->data + b->n, p, n);
        b->n += n;
}

static void
bputs(Buf *b, char const *s)
{
        bput(b, s, strlen(s));
}

static char *
cat(char const *a, char const *b)
{
        char *s = malloc(strlen(a) + strlen(b) + 1);
        strcpy(s, a);
        strcat(s, b);
        return s;
}

static bool
fput(Files *fs, char const *rel, char const *path, u32 mode)
{
        for (int i = 0; i < fs->n; ++i) {
                if (strcmp(fs->items[i].rel, rel) == 0) {
                        return strcmp(fs->items[i].path, path) == 0;
                }
        }

        fs->items = realloc(fs->items, (fs->n + 1) * sizeof *fs->items);
        fs->items[fs->n++] = (File) {
                .rel  = strdup(rel),
                .path = strdup(path),
                .mode = mode
        };

        return true;
}

static bool
regular(char const *path)
{
        struct stat st;
        return (stat(path, &st) == 0) && S_ISREG(st.st_mode);
}

static char const *
base(char const *path)
{
        char const *slash = strrchr(path, '/');
        return (slash == NULL) ? path : slash + 1;
}

static char const *
under(char const *path, char const *dir)
{
        usize n = strlen(dir);

        if (n == 1 && dir[0] == '/') {
                return (path[0] == '/') ? path + 1 : NULL;
        }

        if (strncmp(path, dir, n) == 0 && path[n] == '/') {
                return path + n + 1;
        }

        return NULL;
}

static void
parent(char *dir)
{
        char *slash = strrchr(dir, '/');

        if (slash == NULL || slash == dir) {
                strcpy(dir, "/");
        } else {
                *slash = '\0';
        }
}

#if defined(__APPLE__)
static void
images(List *out)
{
        u32 n = _dyld_image_count();

        for (u32 i = 0; i < n; ++i) {
                char const *name = _dyld_get_image_name(i);
                if (name != NULL) {
                        lput(out, name);
                }
        }
}
#else
static int
image(struct dl_phdr_info *info, size_t size, void *ctx)
{
        (void)size;

        if (info->dlpi_name != NULL && info->dlpi_name[0] != '\0') {
                lput(ctx, info->dlpi_name);
        }

        return 0;
}

static void
images(List *out)
{
        dl_iterate_phdr(image, out);
}
#endif

static bool
system_lib(char const *path)
{
        static char const *const prefixes[] = {
#if defined(__APPLE__)
                "/usr/lib/",
                "/System/",
                "/Library/Apple/",
#else
                "/lib/",
                "/lib32/",
                "/lib64/",
                "/usr/lib/",
                "/usr/lib32/",
                "/usr/lib64/",
#endif
        };

        for (usize i = 0; i < countof(prefixes); ++i) {
                if (strncmp(path, prefixes[i], strlen(prefixes[i])) == 0) {
                        return true;
                }
        }

        return false;
}

void
bundle_snapshot(void)
{
        images(&Before);
}

static void
search_dirs(List *out)
{
        Array *search = v_(Globals, NAMES.path)->array;
        char dir[PATH_MAX];

        for (usize i = 0; i < vN(*search); ++i) {
                Value v = v__(*search, i);
                if (v.type != VALUE_STRING) {
                        continue;
                }
                snprintf(dir, sizeof dir, "%.*s", (int)sN(v), ss(v));
                lput(out, dir);
        }
}

static char const *
lib_rel(List const *dirs, char const *path, char const *name, char *buf, usize cap)
{
        for (int i = 0; i < dirs->n; ++i) {
                snprintf(buf, cap, "%s/%s.ty", dirs->items[i], name);
                if (strcmp(buf, path) == 0) {
                        snprintf(buf, cap, "lib/%s.ty", name);
                        return buf;
                }
        }

        return NULL;
}

static bool
collect_modules(Ty *ty, char const *script, Files *files, char *entry, usize cap)
{
        List dirs = {0};
        List app  = {0};
        char embedded[PATH_MAX];
        char real[PATH_MAX];
        char rel[PATH_MAX];
        char root[PATH_MAX];
        bool have_embedded = false;

        search_dirs(&dirs);

        if (embedded_lib_dir(rel, sizeof rel) && realpath(rel, embedded) != NULL) {
                have_embedded = true;
        }

        if (realpath(script, real) == NULL) {
                fprintf(stderr, "ty --bundle: %s: %s\n", script, strerror(errno));
                return false;
        }

        lput(&app, real);

        ModuleVector const *mods = TyActiveModules(ty);

        for (usize i = 0; i < vN(*mods); ++i) {
                Module const *mod = v__(*mods, i);

                if (
                        (mod->path == NULL)
                     || (mod->name == NULL)
                     || (realpath(mod->path, real) == NULL)
                     || !regular(real)
                ) {
                        continue;
                }

                if (have_embedded && under(real, embedded) != NULL) {
                        continue;
                }

                if (lib_rel(&dirs, real, mod->name, rel, sizeof rel) != NULL) {
                        if (!fput(files, rel, real, 0644)) {
                                fprintf(stderr, "ty --bundle: conflicting files for %s\n", rel);
                                return false;
                        }
                } else if (!lhas(&app, real)) {
                        lput(&app, real);
                }
        }

        int nsrc = app.n;
        for (int i = 0; i < nsrc; ++i) {
                char const *r = mod_root(ty, app.items[i]);
                if (r == NULL) {
                        continue;
                }
                snprintf(real, sizeof real, "%s/__pkg__.ty", r);
                if (regular(real) && !lhas(&app, real)) {
                        lput(&app, real);
                }
        }

        snprintf(root, sizeof root, "%s", app.items[0]);
        parent(root);

        for (int i = 1; i < app.n; ++i) {
                while (under(app.items[i], root) == NULL) {
                        parent(root);
                }
        }

        for (int i = 0; i < app.n; ++i) {
                snprintf(rel, sizeof rel, "app/%s", under(app.items[i], root));
                if (!fput(files, rel, app.items[i], 0644)) {
                        fprintf(stderr, "ty --bundle: conflicting files for %s\n", rel);
                        return false;
                }
                if (i == 0) {
                        snprintf(entry, cap, "%s", rel);
                }
        }

        return true;
}

static void
add_native(Files *files, List *origs, char const *name, char const *real)
{
        char rel[PATH_MAX];

        for (int i = 0; i < files->n; ++i) {
                if (strcmp(files->items[i].path, real) == 0) {
                        return;
                }
        }

        snprintf(rel, sizeof rel, "native/%s", base(name));
        for (int k = 1; !fput(files, rel, real, 0755); ++k) {
                snprintf(rel, sizeof rel, "native/%d-%s", k, base(name));
        }

        lput(origs, name);
        lput(origs, rel);
}

static bool
collect_natives(Files *files, List *origs, char **extra, int nextra)
{
        List after = {0};
        char real[PATH_MAX];

        for (int i = 0; i < nextra; ++i) {
                if (realpath(extra[i], real) == NULL || !regular(real)) {
                        fprintf(stderr, "ty --bundle: %s: not a file\n", extra[i]);
                        return false;
                }
                add_native(files, origs, extra[i], real);
        }

        images(&after);

        for (int i = 0; i < after.n; ++i) {
                char const *name = after.items[i];

                if (
                        lhas(&Before, name)
                     || system_lib(name)
                     || (realpath(name, real) == NULL)
                     || !regular(real)
                ) {
                        continue;
                }

                add_native(files, origs, name, real);
        }

        return true;
}

static bool
build_payload(Files const *files, Buf *out)
{
        for (int i = 0; i < files->n; ++i) {
                File const *f = &files->items[i];
                usize n;
                char *data = slurp(f->path, &n);

                if (data == NULL) {
                        fprintf(stderr, "ty --bundle: %s: %s\n", f->path, strerror(errno));
                        return false;
                }

                BundleEntry e = {
                        .len  = (u32)strlen(f->rel),
                        .mode = f->mode,
                        .size = n
                };

                bput(out, &e, sizeof e);
                bput(out, f->rel, e.len);
                bput(out, data, n);
        }

        return true;
}

#if defined(__APPLE__)
static struct segment_command_64 *
find_linkedit(char *img)
{
        struct mach_header_64 *mh = (void *)img;
        char *p = img + sizeof *mh;

        for (u32 i = 0; i < mh->ncmds; ++i) {
                struct load_command *lc = (void *)p;
                if (lc->cmd == LC_SEGMENT_64) {
                        struct segment_command_64 *seg = (void *)p;
                        if (strncmp(seg->segname, "__LINKEDIT", sizeof seg->segname) == 0) {
                                return seg;
                        }
                }
                p += lc->cmdsize;
        }

        return NULL;
}

static bool
strip_signature(char *img, usize n, usize *keep)
{
        struct mach_header_64 *mh = (void *)img;

        if (n < sizeof *mh || mh->magic != MH_MAGIC_64) {
                fprintf(stderr, "ty --bundle: unsupported executable format\n");
                return false;
        }

        char *cmds = img + sizeof *mh;
        char *end  = cmds + mh->sizeofcmds;
        char *p    = cmds;

        for (u32 i = 0; i < mh->ncmds; ++i) {
                struct load_command *lc = (void *)p;

                if (lc->cmd != LC_CODE_SIGNATURE) {
                        p += lc->cmdsize;
                        continue;
                }

                struct linkedit_data_command *sig = (void *)p;
                u32 size = lc->cmdsize;

                if (sig->dataoff < *keep) {
                        *keep = sig->dataoff;
                }

                memmove(p, p + size, (usize)(end - (p + size)));
                memset(end - size, 0, size);
                mh->ncmds      -= 1;
                mh->sizeofcmds -= size;

                return true;
        }

        return false;
}

static bool
codesign(char const *path, char const *ident)
{
        char *argv[] = {
                "codesign",
                "-s", "-",
                "-f",
                "-i", (char *)ident,
                (char *)path,
                NULL
        };
        pid_t pid;
        int status;

        if (posix_spawn(&pid, "/usr/bin/codesign", NULL, NULL, argv, environ) != 0) {
                return false;
        }

        while (waitpid(pid, &status, 0) < 0) {
                if (errno != EINTR) {
                        return false;
                }
        }

        return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}
#endif

static bool
write_all(int fd, void const *p, usize n)
{
        char const *s = p;

        while (n > 0) {
                ssize_t w = write(fd, s, n);
                if (w < 0 && errno == EINTR) {
                        continue;
                }
                if (w <= 0) {
                        return false;
                }
                s += w;
                n -= (usize)w;
        }

        return true;
}

static bool
write_bundle(char const *out, Buf const *payload)
{
        char self[PATH_MAX];
        char tmp[PATH_MAX];
        BundleTrailer old;
        BundleTrailer t;
        usize n;
        bool sign = false;

        if (!executable_path(self, sizeof self)) {
                fprintf(stderr, "ty --bundle: cannot locate the ty executable\n");
                return false;
        }

        char *img = slurp(self, &n);
        if (img == NULL) {
                fprintf(stderr, "ty --bundle: %s: %s\n", self, strerror(errno));
                return false;
        }

        usize keep = n;

        int fd = open(self, O_RDONLY | O_CLOEXEC);
        if (fd >= 0 && bundle_locate(fd, &old)) {
                keep = old.offset;
        }
        if (fd >= 0) {
                close(fd);
        }

#if defined(__APPLE__)
        sign = strip_signature(img, n, &keep);

        struct segment_command_64 *linkedit = find_linkedit(img);
        if (linkedit == NULL || linkedit->fileoff > keep) {
                fprintf(stderr, "ty --bundle: executable has no usable __LINKEDIT segment\n");
                return false;
        }
#endif

        usize pad = (16 - ((keep + payload->n + sizeof t) % 16)) % 16;
        usize end = keep + payload->n + pad + sizeof t;

#if defined(__APPLE__)
        linkedit->filesize = end - linkedit->fileoff;
        linkedit->vmsize   = (linkedit->filesize + 0x3FFF) & ~(u64)0x3FFF;
#endif

        memset(&t, 0, sizeof t);
        memcpy(t.magic, TY_BUNDLE_MAGIC, sizeof t.magic);
        t.offset = keep;
        t.size   = payload->n;
        t.hash   = XXH3_64bits(payload->data, payload->n);
        t.flags  = TY_BUNDLE_RUN;

        snprintf(tmp, sizeof tmp, "%s.tmp.%ld", out, (long)getpid());

        fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0755);
        if (fd < 0) {
                fprintf(stderr, "ty --bundle: %s: %s\n", tmp, strerror(errno));
                return false;
        }

        static char const zeros[16];

        bool ok = write_all(fd, img, keep)
               && write_all(fd, payload->data, payload->n)
               && write_all(fd, zeros, pad)
               && write_all(fd, &t, sizeof t);

        if (close(fd) != 0 || !ok) {
                fprintf(stderr, "ty --bundle: %s: %s\n", tmp, strerror(errno));
                unlink(tmp);
                return false;
        }

#if defined(__APPLE__)
        if (sign && !codesign(tmp, base(out))) {
                fprintf(stderr, "ty --bundle: codesign failed for %s\n", tmp);
                unlink(tmp);
                return false;
        }
#endif

        if (rename(tmp, out) != 0) {
                fprintf(stderr, "ty --bundle: %s: %s\n", out, strerror(errno));
                unlink(tmp);
                return false;
        }

        return true;
}

static char *
default_output(char const *script)
{
        char const *name = base(script);
        usize n = strlen(name);

        if (n > 3 && strcmp(name + n - 3, ".ty") == 0) {
                char *out = strdup(name);
                out[n - 3] = '\0';
                return out;
        }

        return cat(name, ".out");
}

int
bundle_create(
        Ty *ty,
        char const *script,
        char const *out,
        char **flags,
        int nflags,
        char **extra,
        int nextra
)
{
        Files files = {0};
        List natives = {0};
        Buf manifest = {0};
        Buf payload = {0};
        char entry[PATH_MAX];
        char a[PATH_MAX];
        char b[PATH_MAX];

        if (out == NULL || *out == '\0') {
                out = default_output(script);
        }

        if (
                (realpath(script, a) != NULL)
             && (realpath(out, b) != NULL)
             && (strcmp(a, b) == 0)
        ) {
                fprintf(stderr, "ty --bundle: refusing to overwrite %s\n", script);
                return 1;
        }

        char *source = slurp(script, NULL);
        if (source == NULL) {
                fprintf(stderr, "ty --bundle: %s: %s\n", script, strerror(errno));
                return 1;
        }

        if (!vm_load_program(ty, source, script)) {
                fprintf(stderr, "%s\n", TyError(ty));
                return 1;
        }

        if (!collect_modules(ty, script, &files, entry, sizeof entry)) {
                return 1;
        }

        if (!collect_natives(&files, &natives, extra, nextra)) {
                return 1;
        }

        bputs(&manifest, "entry\t");
        bputs(&manifest, entry);
        bputs(&manifest, "\n");

        for (int i = 0; i < nflags; ++i) {
                if (strpbrk(flags[i], "\t\n") != NULL) {
                        fprintf(stderr, "ty --bundle: unsupported option: %s\n", flags[i]);
                        return 1;
                }
                bputs(&manifest, "flag\t");
                bputs(&manifest, flags[i]);
                bputs(&manifest, "\n");
        }

        for (int i = 0; i < natives.n; i += 2) {
                bputs(&manifest, "native\t");
                bputs(&manifest, natives.items[i + 1]);
                bputs(&manifest, "\t");
                bputs(&manifest, natives.items[i]);
                bputs(&manifest, "\n");
        }

        BundleEntry e = {
                .len  = (u32)strlen(".manifest"),
                .mode = 0644,
                .size = manifest.n
        };

        bput(&payload, &e, sizeof e);
        bputs(&payload, ".manifest");
        bput(&payload, manifest.data, manifest.n);

        if (!build_payload(&files, &payload)) {
                return 1;
        }

        if (!write_bundle(out, &payload)) {
                return 1;
        }

        int nmods = 0;
        for (int i = 0; i < files.n; ++i) {
                nmods += (strncmp(files.items[i].rel, "native/", 7) != 0);
        }

        fprintf(
                stderr,
                "ty --bundle: wrote %s (%d module%s, %d native librar%s, %zu KiB payload)\n",
                out,
                nmods,
                (nmods == 1) ? "" : "s",
                natives.n / 2,
                (natives.n == 2) ? "y" : "ies",
                (payload.n + 1023) / 1024
        );

        return 0;
}

#endif
