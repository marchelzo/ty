#ifdef TY_EMBED_LIB

#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#if defined(__APPLE__)
#include <mach-o/loader.h>
#endif

#include <xxhash.h>

#include "ty.h"
#include "xd.h"
#include "bundle.h"

struct embedded_file {
        char const *path;
        char const *data;
        size_t      size;
};

extern struct embedded_file const TyEmbeddedLib[];
extern size_t const TyEmbeddedLibCount;
extern char const TyEmbeddedLibHash[];

typedef struct {
        char *path;
        char *orig;
        void *handle;
} Native;

static struct {
        bool         init;
        BundleState  state;
        char const  *error;
        u64          flags;
        char         dir[PATH_MAX];
        char         entry[PATH_MAX];
        char         self[PATH_MAX];
        char         ty[PATH_MAX];
        char const **args;
        int          nargs;
        Native      *natives;
        int          nnatives;
} B;

static bool
mkdirs(char *path)
{
        for (char *p = path + 1; *p != '\0'; ++p) {
                if (*p != '/') {
                        continue;
                }

                *p = '\0';
                int rc = mkdir(path, 0755);
                *p = '/';

                if (rc != 0 && errno != EEXIST) {
                        return false;
                }
        }

        return (mkdir(path, 0755) == 0) || (errno == EEXIST);
}

static bool
xwrite(int fd, char const *s, size_t n)
{
        while (n > 0) {
                ssize_t w = write(fd, s, n);
                if (w < 0 && errno == EINTR) {
                        continue;
                }
                if (w <= 0) {
                        return false;
                }
                s += w;
                n -= (size_t)w;
        }

        return true;
}

static bool
xpread(int fd, void *buf, size_t n, off_t off)
{
        char *p = buf;

        while (n > 0) {
                ssize_t r = pread(fd, p, n, off);
                if (r < 0 && errno == EINTR) {
                        continue;
                }
                if (r <= 0) {
                        return false;
                }
                p   += r;
                n   -= (size_t)r;
                off += r;
        }

        return true;
}

bool
bundle_put_file(char const *dir, char const *rel, void const *data, usize n, u32 mode)
{
        char path[PATH_MAX];
        char tmp[PATH_MAX];
        int k;

        k = snprintf(path, sizeof path, "%s/%s", dir, rel);
        if (k < 0 || (size_t)k >= sizeof path) {
                return false;
        }

        char *slash = strrchr(path, '/');
        *slash = '\0';
        bool ok = mkdirs(path);
        *slash = '/';

        if (!ok) {
                return false;
        }

        k = snprintf(tmp, sizeof tmp, "%s.%ld", path, (long)getpid());
        if (k < 0 || (size_t)k >= sizeof tmp) {
                return false;
        }

        int fd = open(tmp, O_WRONLY | O_CREAT | O_TRUNC, (mode_t)mode);
        if (fd < 0) {
                return false;
        }

        ok = xwrite(fd, data, n);

        if (close(fd) != 0 || !ok || rename(tmp, path) != 0) {
                unlink(tmp);
                return false;
        }

        return true;
}

static bool
cache_root(char *out, usize cap)
{
        char const *xdg  = getenv("XDG_CACHE_HOME");
        char const *home = getenv("HOME");
        int n;

        if (xdg != NULL && *xdg != '\0') {
                n = snprintf(out, cap, "%s/ty", xdg);
        } else if (home != NULL && *home != '\0') {
                n = snprintf(out, cap, "%s/.cache/ty", home);
        } else {
                return false;
        }

        return (n >= 0) && ((size_t)n < cap);
}

static bool
stamped(char const *dir)
{
        char stamp[PATH_MAX];
        int n = snprintf(stamp, sizeof stamp, "%s/.complete", dir);

        return (n >= 0)
            && ((size_t)n < sizeof stamp)
            && (access(stamp, F_OK) == 0);
}

static bool
stamp(char const *dir)
{
        return bundle_put_file(dir, ".complete", "", 0, 0644);
}

bool
embedded_lib_dir(char *out, usize cap)
{
        char root[PATH_MAX];
        int n;

        if (!cache_root(root, sizeof root)) {
                return false;
        }

        n = snprintf(out, cap, "%s/embedded/%s/lib", root, TyEmbeddedLibHash);
        if (n < 0 || (size_t)n >= cap) {
                return false;
        }

        if (stamped(out)) {
                return true;
        }

        if (!mkdirs(out)) {
                return false;
        }

        for (size_t i = 0; i < TyEmbeddedLibCount; ++i) {
                struct embedded_file const *f = &TyEmbeddedLib[i];
                if (!bundle_put_file(out, f->path, f->data, f->size, 0644)) {
                        return false;
                }
        }

        return stamp(out);
}

static bool
trailer_at(int fd, off_t off, off_t limit, BundleTrailer *out)
{
        if (off < 0 || off + (off_t)sizeof *out > limit) {
                return false;
        }

        if (!xpread(fd, out, sizeof *out, off)) {
                return false;
        }

        return (memcmp(out->magic, TY_BUNDLE_MAGIC, sizeof out->magic) == 0)
            && (out->offset <= (u64)off)
            && (out->size <= (u64)off - out->offset);
}

#if defined(__APPLE__)
static off_t
signature_offset(int fd)
{
        struct mach_header_64 mh;
        off_t found = -1;

        if (!xpread(fd, &mh, sizeof mh, 0) || mh.magic != MH_MAGIC_64) {
                return -1;
        }

        char *cmds = malloc(mh.sizeofcmds);
        if (cmds == NULL || !xpread(fd, cmds, mh.sizeofcmds, sizeof mh)) {
                free(cmds);
                return -1;
        }

        u32 off = 0;
        for (u32 i = 0; i < mh.ncmds; ++i) {
                struct load_command lc;
                if (off + sizeof lc > mh.sizeofcmds) {
                        break;
                }
                memcpy(&lc, cmds + off, sizeof lc);
                if (lc.cmdsize < sizeof lc || off + lc.cmdsize > mh.sizeofcmds) {
                        break;
                }
                if (lc.cmd == LC_CODE_SIGNATURE) {
                        struct linkedit_data_command sig;
                        memcpy(&sig, cmds + off, sizeof sig);
                        found = (off_t)sig.dataoff;
                        break;
                }
                off += lc.cmdsize;
        }

        free(cmds);

        return found;
}
#endif

bool
bundle_locate(int fd, BundleTrailer *out)
{
        struct stat st;

        if (fstat(fd, &st) != 0) {
                return false;
        }

        off_t end = st.st_size;

        if (trailer_at(fd, end - (off_t)sizeof *out, end, out)) {
                return true;
        }

#if defined(__APPLE__)
        off_t sig = signature_offset(fd);
        if (sig > 0 && trailer_at(fd, sig - (off_t)sizeof *out, sig, out)) {
                return true;
        }
#endif

        return false;
}

static bool
safe_rel(char const *rel)
{
        if (rel[0] == '\0' || rel[0] == '/') {
                return false;
        }

        for (char const *p = rel; *p != '\0'; ++p) {
                if (
                        (p[0] == '.')
                     && (p[1] == '.')
                     && (p == rel || p[-1] == '/')
                     && (p[2] == '/' || p[2] == '\0')
                ) {
                        return false;
                }
        }

        return true;
}

static bool
unpack(int fd, BundleTrailer const *t)
{
        char *data = malloc(t->size + 1);
        char rel[PATH_MAX];
        u64 off = 0;

        if (data == NULL) {
                B.error = "out of memory";
                return false;
        }

        if (!xpread(fd, data, t->size, (off_t)t->offset)) {
                B.error = "failed to read payload";
                goto Fail;
        }

        if (XXH3_64bits(data, t->size) != t->hash) {
                B.error = "payload checksum mismatch";
                goto Fail;
        }

        if (!mkdirs(B.dir)) {
                B.error = "failed to create cache directory";
                goto Fail;
        }

        while (off < t->size) {
                BundleEntry e;

                if (t->size - off < sizeof e) {
                        goto Corrupt;
                }

                memcpy(&e, data + off, sizeof e);
                off += sizeof e;

                if (e.len >= sizeof rel || t->size - off < e.len) {
                        goto Corrupt;
                }

                memcpy(rel, data + off, e.len);
                rel[e.len] = '\0';
                off += e.len;

                if (t->size - off < e.size || !safe_rel(rel)) {
                        goto Corrupt;
                }

                if (!bundle_put_file(B.dir, rel, data + off, e.size, e.mode & 0777)) {
                        B.error = "failed to write bundled file";
                        goto Fail;
                }

                off += e.size;
        }

        if (!stamp(B.dir)) {
                B.error = "failed to write bundled file";
                goto Fail;
        }

        free(data);
        return true;

Corrupt:
        B.error = "corrupt payload";
Fail:
        free(data);
        return false;
}

static char *
slurp_text(char const *path)
{
        FILE *f = fopen(path, "rb");
        char *s = NULL;
        long n;

        if (f == NULL) {
                return NULL;
        }

        if (fseek(f, 0, SEEK_END) == 0 && (n = ftell(f)) >= 0) {
                rewind(f);
                s = malloc((size_t)n + 1);
                if (s != NULL && fread(s, 1, (size_t)n, f) == (size_t)n) {
                        s[n] = '\0';
                } else {
                        free(s);
                        s = NULL;
                }
        }

        fclose(f);

        return s;
}

static bool
read_manifest(void)
{
        char path[PATH_MAX];

        snprintf(path, sizeof path, "%s/.manifest", B.dir);

        char *text = slurp_text(path);
        if (text == NULL) {
                return false;
        }

        for (char *line = strtok(text, "\n"); line != NULL; line = strtok(NULL, "\n")) {
                char *a = strchr(line, '\t');
                if (a == NULL) {
                        continue;
                }
                *a++ = '\0';

                if (strcmp(line, "entry") == 0) {
                        snprintf(B.entry, sizeof B.entry, "%s/%s", B.dir, a);
                } else if (strcmp(line, "flag") == 0) {
                        B.args = realloc(B.args, (B.nargs + 1) * sizeof *B.args);
                        B.args[B.nargs++] = strdup(a);
                } else if (strcmp(line, "native") == 0) {
                        char *orig = strchr(a, '\t');
                        if (orig == NULL) {
                                continue;
                        }
                        *orig++ = '\0';
                        char *full = malloc(strlen(B.dir) + strlen(a) + 2);
                        sprintf(full, "%s/%s", B.dir, a);
                        B.natives = realloc(B.natives, (B.nnatives + 1) * sizeof *B.natives);
                        B.natives[B.nnatives++] = (Native) {
                                .path   = full,
                                .orig   = strdup(orig),
                                .handle = NULL
                        };
                }
        }

        free(text);

        return true;
}

static char const *
base(char const *path)
{
        char const *slash = strrchr(path, '/');
        return (slash == NULL) ? path : slash + 1;
}

static bool
install_ty(char const *self)
{
        char bin[PATH_MAX];
        usize n;

        snprintf(B.ty, sizeof B.ty, "%s/bin/ty", B.dir);

        if (access(B.ty, X_OK) == 0) {
                return true;
        }

        snprintf(bin, sizeof bin, "%s/bin", B.dir);

        if (mkdirs(bin) && link(self, B.ty) == 0) {
                return true;
        }

        char *data = slurp(self, &n);
        if (data == NULL) {
                return false;
        }

        return bundle_put_file(B.dir, "bin/ty", data, n, 0755);
}

static void
bundle_init(void)
{
        BundleTrailer t;
        char self[PATH_MAX];
        char root[PATH_MAX];
        int fd = -1;

        if (B.init) {
                return;
        }

        B.init  = true;
        B.state = BUNDLE_NONE;

        char const *off = getenv("TY_NO_BUNDLE");
        if (off != NULL && *off != '\0') {
                return;
        }

        if (!executable_path(self, sizeof self)) {
                return;
        }

        snprintf(B.self, sizeof B.self, "%s", self);

        fd = open(self, O_RDONLY | O_CLOEXEC);
        if (fd < 0) {
                return;
        }

        if (!bundle_locate(fd, &t)) {
                close(fd);
                return;
        }

        B.state = BUNDLE_BROKEN;
        B.flags = t.flags;

        if (!cache_root(root, sizeof root)) {
                B.error = "no cache directory (set HOME or XDG_CACHE_HOME)";
                goto Done;
        }

        snprintf(B.dir, sizeof B.dir, "%s/bundles/%016llx", root, (unsigned long long)t.hash);

        if (!stamped(B.dir) && !unpack(fd, &t)) {
                goto Done;
        }

        if (!install_ty(self)) {
                B.error = "failed to install bundled ty";
                goto Done;
        }

        if (!read_manifest()) {
                B.error = "missing manifest";
                goto Done;
        }

        B.state = BUNDLE_READY;

Done:
        close(fd);
}

BundleState
bundle_state(void)
{
        bundle_init();
        return B.state;
}

char const *
bundle_dir(void)
{
        bundle_init();
        return (B.state == BUNDLE_READY) ? B.dir : NULL;
}

char const *
bundle_ty(void)
{
        bundle_init();
        return (B.state == BUNDLE_READY) ? B.ty : NULL;
}

char const *
bundle_entry(void)
{
        bundle_init();

        if (
                (B.state != BUNDLE_READY)
             || !(B.flags & TY_BUNDLE_RUN)
             || (B.entry[0] == '\0')
             || (strcmp(base(B.self), "ty") == 0)
        ) {
                return NULL;
        }

        return B.entry;
}

char const *
bundle_error(void)
{
        bundle_init();
        return (B.error != NULL) ? B.error : "unknown error";
}

int
bundle_flags(char const *const **out)
{
        bundle_init();
        *out = B.args;
        return B.nargs;
}

static usize
stem(char const *name)
{
        char const *dot = strchr(name, '.');
        return (dot == NULL) ? strlen(name) : (usize)(dot - name);
}

static bool
same_stem(char const *a, char const *b)
{
        usize n = stem(a);
        return (n > 0) && (n == stem(b)) && (memcmp(a, b, n) == 0);
}

char const *
bundle_native(char const *path)
{
        if (path == NULL || bundle_dir() == NULL || B.nnatives == 0) {
                return NULL;
        }

        for (int i = 0; i < B.nnatives; ++i) {
                if (strcmp(path, B.natives[i].orig) == 0) {
                        return B.natives[i].path;
                }
        }

        for (int i = 0; i < B.nnatives; ++i) {
                if (strcmp(base(path), base(B.natives[i].orig)) == 0) {
                        return B.natives[i].path;
                }
        }

        for (int i = 0; i < B.nnatives; ++i) {
                if (same_stem(base(path), base(B.natives[i].orig))) {
                        return B.natives[i].path;
                }
        }

        return NULL;
}

void
bundle_preload(void)
{
        bool progress = true;

        if (bundle_dir() == NULL) {
                return;
        }

        while (progress) {
                progress = false;
                for (int i = 0; i < B.nnatives; ++i) {
                        if (B.natives[i].handle != NULL) {
                                continue;
                        }
                        B.natives[i].handle = dlopen(B.natives[i].path, RTLD_NOW | RTLD_GLOBAL);
                        progress |= (B.natives[i].handle != NULL);
                }
        }
}

#endif
