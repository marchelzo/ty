#ifdef TY_EMBED_LIB

#include <dirent.h>
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
#include <elf.h>
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
                ty_snprintf(dir, sizeof dir, "%.*s", (int)sN(v), ss(v));
                lput(out, dir);
        }
}

static char const *
lib_rel(List const *dirs, char const *path, char const *name, char *buf, usize cap)
{
        for (int i = 0; i < dirs->n; ++i) {
                ty_snprintf(buf, cap, "%s/%s.ty", dirs->items[i], name);
                if (strcmp(buf, path) == 0) {
                        ty_snprintf(buf, cap, "lib/%s.ty", name);
                        return buf;
                }
        }

        return NULL;
}

static bool
gather(Ty *ty, List const *dirs, Files *files, List *app)
{
        char embedded[PATH_MAX];
        char real[PATH_MAX];
        char rel[PATH_MAX];
        bool have_embedded = false;

        if (embedded_lib_dir(rel, sizeof rel) && realpath(rel, embedded) != NULL) {
                have_embedded = true;
        }

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

                if (lib_rel(dirs, real, mod->name, rel, sizeof rel) != NULL) {
                        if (!fput(files, rel, real, 0644)) {
                                fprintf(stderr, "ty --bundle: conflicting files for %s\n", rel);
                                return false;
                        }
                } else if (!lhas(app, real)) {
                        lput(app, real);
                }
        }

        return true;
}

static bool
add_data(List *app, char const *path)
{
        char real[PATH_MAX];
        char sub[PATH_MAX];
        struct stat st;
        struct dirent *e;
        DIR *d;

        if (realpath(path, real) == NULL || stat(real, &st) != 0) {
                fprintf(stderr, "ty --bundle: %s: %s\n", path, strerror(errno));
                return false;
        }

        if (S_ISREG(st.st_mode)) {
                if (!lhas(app, real)) {
                        lput(app, real);
                }
                return true;
        }

        if (!S_ISDIR(st.st_mode) || (d = opendir(real)) == NULL) {
                fprintf(stderr, "ty --bundle: %s: not a file or directory\n", path);
                return false;
        }

        while ((e = readdir(d)) != NULL) {
                if (e->d_name[0] == '.') {
                        continue;
                }
                ty_snprintf(sub, sizeof sub, "%s/%s", real, e->d_name);
                if (!add_data(app, sub)) {
                        closedir(d);
                        return false;
                }
        }

        closedir(d);

        return true;
}

static bool
place_app(List *app, Files *files, char *entry, usize cap)
{
        char rel[PATH_MAX];
        char root[PATH_MAX];
        struct stat st;

        ty_snprintf(root, sizeof root, "%s", app->items[0]);
        parent(root);

        for (int i = 1; i < app->n; ++i) {
                while (under(app->items[i], root) == NULL) {
                        parent(root);
                }
        }

        for (int i = 0; i < app->n; ++i) {
                u32 mode = (stat(app->items[i], &st) == 0) ? (st.st_mode & 0777) : 0644;
                ty_snprintf(rel, sizeof rel, "app/%s", under(app->items[i], root));
                if (!fput(files, rel, app->items[i], mode)) {
                        fprintf(stderr, "ty --bundle: conflicting files for %s\n", rel);
                        return false;
                }
                if (i == 0) {
                        ty_snprintf(entry, cap, "%s", rel);
                }
        }

        return true;
}

static void
add_packages(Ty *ty, List *app)
{
        char real[PATH_MAX];
        int n = app->n;

        for (int i = 0; i < n; ++i) {
                char const *r = mod_root(ty, app->items[i]);
                if (r == NULL) {
                        continue;
                }
                ty_snprintf(real, sizeof real, "%s/__pkg__.ty", r);
                if (regular(real) && !lhas(app, real)) {
                        lput(app, real);
                }
        }
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

        ty_snprintf(rel, sizeof rel, "native/%s", base(name));
        for (int k = 1; !fput(files, rel, real, 0755); ++k) {
                ty_snprintf(rel, sizeof rel, "native/%d-%s", k, base(name));
        }

        lput(origs, name);
        lput(origs, rel);
}

static void
loaded(List *out)
{
        List after = {0};
        char real[PATH_MAX];

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

                lput(out, name);
        }
}

static bool
collect_natives(Files *files, List *origs, char **extra, int nextra)
{
        List libs = {0};
        char real[PATH_MAX];

        for (int i = 0; i < nextra; ++i) {
                if (realpath(extra[i], real) == NULL || !regular(real)) {
                        fprintf(stderr, "ty --bundle: %s: not a file\n", extra[i]);
                        return false;
                }
                add_native(files, origs, extra[i], real);
        }

        loaded(&libs);

        for (int i = 0; i < libs.n; ++i) {
                if (realpath(libs.items[i], real) != NULL) {
                        add_native(files, origs, libs.items[i], real);
                }
        }

        return true;
}

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
load(Ty *ty, char const *script)
{
        char *source = slurp(script, NULL);

        if (source == NULL) {
                fprintf(stderr, "ty --bundle: %s: %s\n", script, strerror(errno));
                return false;
        }

        if (!vm_load_program(ty, source, script)) {
                fprintf(stderr, "%s\n", TyError(ty));
                return false;
        }

        return true;
}

int
bundle_scan(Ty *ty, char const *script, int fd)
{
        List dirs = {0};
        List app  = {0};
        List libs = {0};
        Files files = {0};
        Buf out = {0};
        char real[PATH_MAX];

        if (!load(ty, script)) {
                return 1;
        }

        search_dirs(&dirs);

        if (!gather(ty, &dirs, &files, &app)) {
                return 1;
        }

        loaded(&libs);

        for (int i = 0; i < files.n; ++i) {
                bputs(&out, "lib\t");
                bputs(&out, files.items[i].rel);
                bputs(&out, "\t");
                bputs(&out, files.items[i].path);
                bputs(&out, "\n");
        }

        for (int i = 0; i < app.n; ++i) {
                bputs(&out, "app\t");
                bputs(&out, app.items[i]);
                bputs(&out, "\n");
        }

        for (int i = 0; i < libs.n; ++i) {
                if (realpath(libs.items[i], real) == NULL) {
                        continue;
                }
                bputs(&out, "native\t");
                bputs(&out, libs.items[i]);
                bputs(&out, "\t");
                bputs(&out, real);
                bputs(&out, "\n");
        }

        return write_all(fd, out.data, out.n) ? 0 : 1;
}

static bool
absorb(char *text, Files *files, List *app, List *origs)
{
        char *save = NULL;

        for (char *line = strtok_r(text, "\n", &save); line != NULL; line = strtok_r(NULL, "\n", &save)) {
                char *a = strchr(line, '\t');
                char *b = (a == NULL) ? NULL : strchr(a + 1, '\t');

                if (a == NULL) {
                        continue;
                }

                *a++ = '\0';
                if (b != NULL) {
                        *b++ = '\0';
                }

                if (strcmp(line, "app") == 0) {
                        if (!lhas(app, a)) {
                                lput(app, a);
                        }
                } else if (b == NULL) {
                        continue;
                } else if (strcmp(line, "lib") == 0) {
                        if (!fput(files, a, b, 0644)) {
                                fprintf(stderr, "ty --bundle: conflicting files for %s\n", a);
                                return false;
                        }
                } else if (strcmp(line, "native") == 0) {
                        add_native(files, origs, a, b);
                }
        }

        return true;
}

static bool
scan(BundleSpec const *spec, char const *script, Files *files, List *app, List *origs)
{
        char self[PATH_MAX];
        char opt[64];
        char chunk[4096];
        Buf text = {0};
        pid_t pid;
        int status;
        int p[2];
        int k = 0;

        if (!executable_path(self, sizeof self)) {
                fprintf(stderr, "ty --bundle: cannot locate the ty executable\n");
                return false;
        }

        if (pipe(p) != 0) {
                fprintf(stderr, "ty --bundle: pipe: %s\n", strerror(errno));
                return false;
        }

        fcntl(p[0], F_SETFD, FD_CLOEXEC);
        ty_snprintf(opt, sizeof opt, "--bundle-scan=%d", p[1]);

        char **argv = malloc((spec->nflags + 4) * sizeof *argv);

        argv[k++] = self;
        for (int i = 0; i < spec->nflags; ++i) {
                argv[k++] = spec->flags[i];
        }
        argv[k++] = opt;
        argv[k++] = (char *)script;
        argv[k]   = NULL;

        int rc = posix_spawn(&pid, self, NULL, NULL, argv, environ);

        close(p[1]);
        free(argv);

        if (rc != 0) {
                fprintf(stderr, "ty --bundle: %s: %s\n", self, strerror(rc));
                close(p[0]);
                return false;
        }

        for (;;) {
                ssize_t n = read(p[0], chunk, sizeof chunk);
                if (n < 0 && errno == EINTR) {
                        continue;
                }
                if (n <= 0) {
                        break;
                }
                bput(&text, chunk, (usize)n);
        }

        close(p[0]);

        while (waitpid(pid, &status, 0) < 0) {
                if (errno != EINTR) {
                        status = -1;
                        break;
                }
        }

        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
                fprintf(stderr, "ty --bundle: failed to scan %s\n", script);
                return false;
        }

        bput(&text, "", 1);

        return absorb(text.data, files, app, origs);
}

#if !defined(__APPLE__)
static bool
at(Elf64_Phdr const *ph, int nph, u64 vaddr, usize n, u64 *out)
{
        for (int i = 0; i < nph; ++i) {
                if (
                        (ph[i].p_type == PT_LOAD)
                     && (vaddr >= ph[i].p_vaddr)
                     && (vaddr < ph[i].p_vaddr + ph[i].p_filesz)
                ) {
                        *out = vaddr - ph[i].p_vaddr + ph[i].p_offset;
                        return *out < n;
                }
        }

        return false;
}

static void
linkage(char const *path, List *soname, List *needed)
{
        Elf64_Ehdr const *eh;
        Elf64_Phdr const *ph;
        Elf64_Dyn const *dyn = NULL;
        usize ndyn = 0;
        u64 strtab = 0;
        u64 off;
        usize n;

        char *img = slurp(path, &n);
        if (img == NULL) {
                return;
        }

        eh = (void *)img;

        if (
                (n < sizeof *eh)
             || (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0)
             || (eh->e_ident[EI_CLASS] != ELFCLASS64)
             || (eh->e_phoff + (u64)eh->e_phnum * sizeof *ph > n)
        ) {
                return;
        }

        ph = (void *)(img + eh->e_phoff);

        for (int i = 0; i < eh->e_phnum; ++i) {
                if (ph[i].p_type == PT_DYNAMIC && ph[i].p_offset + ph[i].p_filesz <= n) {
                        dyn  = (void *)(img + ph[i].p_offset);
                        ndyn = ph[i].p_filesz / sizeof *dyn;
                }
        }

        for (usize i = 0; i < ndyn && dyn[i].d_tag != DT_NULL; ++i) {
                if (dyn[i].d_tag == DT_STRTAB) {
                        strtab = dyn[i].d_un.d_ptr;
                }
        }

        if (dyn == NULL || !at(ph, eh->e_phnum, strtab, n, &strtab)) {
                return;
        }

        for (usize i = 0; i < ndyn && dyn[i].d_tag != DT_NULL; ++i) {
                off = strtab + dyn[i].d_un.d_val;
                if (off >= n || memchr(img + off, '\0', n - off) == NULL) {
                        continue;
                }
                switch (dyn[i].d_tag) {
                case DT_SONAME: lput(soname, img + off); break;
                case DT_NEEDED: lput(needed, img + off); break;
                }
        }
}
#else
static void
linkage(char const *path, List *soname, List *needed)
{
        (void)path;
        (void)soname;
        (void)needed;
}
#endif

static char const *
fpath(Files const *files, char const *rel)
{
        for (int i = 0; i < files->n; ++i) {
                if (strcmp(files->items[i].rel, rel) == 0) {
                        return files->items[i].path;
                }
        }

        return NULL;
}

static void
order_natives(Files const *files, List *natives)
{
        int n = natives->n / 2;
        List *needs = calloc(n, sizeof *needs);
        List *names = calloc(n, sizeof *names);
        bool *done = calloc(n, sizeof *done);
        List out = {0};

        for (int i = 0; i < n; ++i) {
                char const *rel = natives->items[2 * i + 1];
                char const *path = fpath(files, rel);
                lput(&names[i], base(rel));
                if (path != NULL) {
                        linkage(path, &names[i], &needs[i]);
                }
        }

        while (out.n < natives->n) {
                int pick = -1;

                for (int i = 0; i < n && pick < 0; ++i) {
                        bool ready = !done[i];
                        for (int j = 0; ready && j < n; ++j) {
                                if (done[j] || j == i) {
                                        continue;
                                }
                                for (int k = 0; ready && k < needs[i].n; ++k) {
                                        ready = !lhas(&names[j], needs[i].items[k]);
                                }
                        }
                        if (ready) {
                                pick = i;
                        }
                }

                for (int i = 0; i < n && pick < 0; ++i) {
                        if (!done[i]) {
                                pick = i;
                        }
                }

                done[pick] = true;
                lput(&out, natives->items[2 * pick]);
                lput(&out, natives->items[2 * pick + 1]);
        }

        *natives = out;
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

        ty_snprintf(tmp, sizeof tmp, "%s.tmp.%ld", out, (long)getpid());

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
bundle_create(Ty *ty, BundleSpec const *spec)
{
        Files files = {0};
        List natives = {0};
        List dirs = {0};
        List app = {0};
        Buf manifest = {0};
        Buf payload = {0};
        char entry[PATH_MAX];
        char a[PATH_MAX];
        char b[PATH_MAX];
        char const *script = spec->script;
        char const *out = spec->out;
        char **flags = spec->flags;
        int nflags = spec->nflags;

        if (out == NULL || *out == '\0') {
                out = default_output(script);
        }

        if (strcmp(base(out), "ty") == 0) {
                fprintf(stderr, "ty --bundle: a bundle cannot be named ty\n");
                return 1;
        }

        if (
                (realpath(script, a) != NULL)
             && (realpath(out, b) != NULL)
             && (strcmp(a, b) == 0)
        ) {
                fprintf(stderr, "ty --bundle: refusing to overwrite %s\n", script);
                return 1;
        }

        if (realpath(script, a) == NULL) {
                fprintf(stderr, "ty --bundle: %s: %s\n", script, strerror(errno));
                return 1;
        }

        lput(&app, a);

        if (!load(ty, script)) {
                return 1;
        }

        search_dirs(&dirs);

        if (!gather(ty, &dirs, &files, &app)) {
                return 1;
        }

        if (!collect_natives(&files, &natives, spec->natives, spec->nnatives)) {
                return 1;
        }

        for (int i = 0; i < spec->nscripts; ++i) {
                if (!scan(spec, spec->scripts[i], &files, &app, &natives)) {
                        return 1;
                }
        }

        add_packages(ty, &app);

        for (int i = 0; i < spec->nfiles; ++i) {
                if (!add_data(&app, spec->files[i])) {
                        return 1;
                }
        }

        if (!place_app(&app, &files, entry, sizeof entry)) {
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

        order_natives(&files, &natives);

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
                "ty --bundle: wrote %s (%d file%s, %d native librar%s, %zu KiB payload)\n",
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
