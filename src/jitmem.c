#include <sys/mman.h>
#include <unistd.h>
#include <pthread.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>

#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#endif

#include "ty/thread.h"
#include "lir.h"

enum {
        JM_REGION_SIZE = 128 << 20,
        JM_MIN_SHIFT = 6,
        JM_MAX_SHIFT = 16,
        JM_NCLASS = JM_MAX_SHIFT - JM_MIN_SHIFT + 1,
        JM_NBUCKET = 4096
};

typedef struct jm_region {
        void *rw;
        void *rx;
        usize live;
        bool retired;
        struct jm_region *next;
} JmRegion;

typedef struct jm_chunk {
        void *rw;
        void *rx;
        usize offset;
        usize size;
        usize requested;
        JmRegion *pool;
        struct jm_chunk *next;
} JmChunk;

static TySpinLock Lock = TY_MUTEX_INIT;
static pthread_once_t Once = PTHREAD_ONCE_INIT;
static JmChunk *Active[JM_NBUCKET];
static JmChunk *Classes[JM_NCLASS];
static JmChunk *Extents;
static JmChunk *Retired;
static JmRegion *Regions;
static JmRegion *Pool;
static u8 *RegionRW;
static u8 *RegionRX;
static bool RegionTried;
static bool ForkReady;
static JitMemStats Stats;
static _Thread_local u32 WriteDepth;

static usize
bucket(void const *rx)
{
        return ((uptr)rx >> JM_MIN_SHIFT) & (JM_NBUCKET - 1);
}

static JmChunk **
find(void const *rx)
{
        JmChunk **p = &Active[bucket(rx)];
        while (*p != NULL && (*p)->rx != rx) {
                p = &(*p)->next;
        }
        return p;
}

static i32
size_class(usize size)
{
        u32 shift = JM_MIN_SHIFT;
        usize n = (usize)1 << shift;
        while (n < size && shift < JM_MAX_SHIFT) {
                ++shift;
                n <<= 1;
        }
        return size <= n ? (i32)(shift - JM_MIN_SHIFT) : -1;
}

static void
insert_extent(JmChunk *c)
{
        JmChunk **p = &Extents;
        JmChunk *prev = NULL;
        JmChunk *next;
        while (*p != NULL && (*p)->offset < c->offset) {
                prev = *p;
                p = &(*p)->next;
        }
        c->next = *p;
        *p = c;
        next = c->next;
        if (next != NULL && c->offset + c->size == next->offset) {
                c->size += next->size;
                c->next = next->next;
                free(next);
        }
        if (prev != NULL && prev->offset + prev->size == c->offset) {
                prev->size += c->size;
                prev->next = c->next;
                free(c);
        }
}

static void
reclaim_classes(void)
{
        for (u32 i = 0; i < JM_NCLASS; ++i) {
                while (Classes[i] != NULL) {
                        JmChunk *c = Classes[i];
                        Classes[i] = c->next;
                        insert_extent(c);
                }
        }
}

static void
fork_prepare(void)
{
        TySpinLockLock(&Lock);
}

static void
fork_parent(void)
{
        TySpinLockUnlock(&Lock);
}

static void
fork_child(void)
{
        TySpinLockInit(&Lock);
        WriteDepth = 0;
#if defined(__linux__)
        if (Pool != NULL) {
                Pool->retired = true;
                munmap(Pool->rw, JM_REGION_SIZE);
                Pool->rw = NULL;
        }
        for (u32 i = 0; i < JM_NCLASS; ++i) {
                while (Classes[i] != NULL) {
                        JmChunk *c = Classes[i];
                        Classes[i] = c->next;
                        c->next = Retired;
                        Retired = c;
                }
        }
        while (Extents != NULL) {
                JmChunk *c = Extents;
                Extents = c->next;
                c->next = Retired;
                Retired = c;
        }
        Pool = NULL;
        RegionRW = NULL;
        RegionRX = NULL;
        RegionTried = false;
#endif
}

static void
initialize(void)
{
        ForkReady = pthread_atfork(fork_prepare, fork_parent, fork_child) == 0;
}

static void
region_init(void)
{
        JmChunk *e;
        JmRegion *pool;
        void *rw = MAP_FAILED;
        void *rx = MAP_FAILED;
        if (!ForkReady) {
                return;
        }
        e = calloc(1, sizeof *e);
        pool = calloc(1, sizeof *pool);
        if (e == NULL || pool == NULL) {
                free(e);
                free(pool);
                return;
        }
#if defined(__APPLE__) && defined(MAP_JIT)
        rw = mmap(NULL, JM_REGION_SIZE, PROT_READ | PROT_WRITE | PROT_EXEC,
                  MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT, -1, 0);
        rx = rw;
#elif defined(__linux__)
        int fd = memfd_create("ty-jit", MFD_CLOEXEC);
        if (fd != -1) {
                if (ftruncate(fd, JM_REGION_SIZE) == 0) {
                        rw = mmap(NULL, JM_REGION_SIZE, PROT_READ | PROT_WRITE,
                                  MAP_SHARED, fd, 0);
                        if (rw != MAP_FAILED) {
                                rx = mmap(NULL, JM_REGION_SIZE, PROT_READ | PROT_EXEC,
                                          MAP_SHARED, fd, 0);
                        }
                }
                close(fd);
        }
#endif
        if (rw == MAP_FAILED || rx == MAP_FAILED) {
                if (rw != MAP_FAILED) {
                        munmap(rw, JM_REGION_SIZE);
                }
                free(e);
                free(pool);
                return;
        }
        RegionRW = rw;
        RegionRX = rx;
        pool->rw   = rw;
        pool->rx   = rx;
        pool->next = Regions;
        Regions = pool;
        Pool = pool;
        e->size = JM_REGION_SIZE;
        Extents = e;
        Stats.allocated += JM_REGION_SIZE;
}

static JmChunk *
region_alloc(usize n)
{
        JmChunk **p = &Extents;
        JmChunk *c;
        JmChunk *e;
        while (*p != NULL && (*p)->size < n) {
                p = &(*p)->next;
        }
        e = *p;
        if (e == NULL) {
                return NULL;
        }
        if (e->size == n) {
                *p = e->next;
                c = e;
        } else {
                c = calloc(1, sizeof *c);
                if (c == NULL) {
                        return NULL;
                }
                c->offset = e->offset;
                c->size   = n;
                e->offset += n;
                e->size -= n;
        }
        c->rw   = RegionRW + c->offset;
        c->rx   = RegionRX + c->offset;
        c->pool = Pool;
        return c;
}

static JmChunk *
map_one(usize size)
{
        JmChunk *c;
        usize page;
        usize n;
        void *p;
        long pagesize = sysconf(_SC_PAGESIZE);
        if (pagesize <= 0) {
                return NULL;
        }
        page = pagesize;
        if (size > SIZE_MAX - page + 1) {
                return NULL;
        }
        n = (size + page - 1) / page * page;
        c = calloc(1, sizeof *c);
        if (c == NULL) {
                return NULL;
        }
#if defined(__APPLE__) && defined(MAP_JIT)
        p = mmap(NULL, n, PROT_READ | PROT_WRITE | PROT_EXEC,
                 MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT, -1, 0);
#else
        p = mmap(NULL, n, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
#endif
        if (p == MAP_FAILED) {
                free(c);
                return NULL;
        }
        c->rw    = p;
        c->rx    = p;
        c->size  = n;
        Stats.allocated += n;
        return c;
}

JitMapping
jm_alloc(usize size)
{
        JmChunk *c = NULL;
        usize n;
        i32 cls;
        JitMapping result = {0};
        if (size == 0 || size > SIZE_MAX - 63) {
                return result;
        }
        pthread_once(&Once, initialize);
        cls = size_class(size);
        n = cls < 0 ? (size + 63) & ~(usize)63 : (usize)1 << (JM_MIN_SHIFT + cls);
        TySpinLockLock(&Lock);
        while (Retired != NULL) {
                JmChunk *c = Retired;
                Retired = c->next;
                free(c);
        }
        if (!RegionTried) {
                RegionTried = true;
                region_init();
        }
        if (cls >= 0 && Classes[cls] != NULL) {
                c = Classes[cls];
                Classes[cls] = c->next;
        } else if (RegionRX != NULL) {
                c = region_alloc(n);
                if (c == NULL) {
                        reclaim_classes();
                        c = region_alloc(n);
                }
        }
        if (c == NULL) {
                c = map_one(n);
        }
        if (c != NULL) {
                usize h = bucket(c->rx);
                c->requested = size;
                c->next      = Active[h];
                Active[h]    = c;
                Stats.used += c->size;
                ++Stats.nchunks;
                if (c->pool != NULL) {
                        ++c->pool->live;
                }
                result.rw = c->rw;
                result.rx = c->rx;
        }
        TySpinLockUnlock(&Lock);
        return result;
}

void
jm_write_begin(void)
{
#if defined(__APPLE__) && defined(__aarch64__)
        if (WriteDepth++ == 0) {
                pthread_jit_write_protect_np(0);
        }
#else
        ++WriteDepth;
#endif
}

bool
jm_write_end(void *rx, usize size)
{
        JmChunk *c;
        bool ok;
        if (WriteDepth == 0) {
                return false;
        }
        --WriteDepth;
#if defined(__APPLE__) && defined(__aarch64__)
        if (WriteDepth == 0) {
                pthread_jit_write_protect_np(1);
        }
#endif
        TySpinLockLock(&Lock);
        c = *find(rx);
        ok = c != NULL && size <= c->requested
          && (c->pool == NULL || !c->pool->retired);
#if !(defined(__APPLE__) && defined(MAP_JIT))
        if (ok && c->pool == NULL) {
                ok = mprotect(c->rx, c->size, PROT_READ | PROT_EXEC) == 0;
        }
#endif
        TySpinLockUnlock(&Lock);
        if (ok) {
#ifdef __APPLE__
                sys_icache_invalidate(rx, size);
#else
                __builtin___clear_cache(rx, (u8 *)rx + size);
#endif
        }
        return ok;
}

void
jm_free(void *rx)
{
        JmChunk **p;
        JmChunk *c;
        i32 cls;
        if (rx == NULL) {
                return;
        }
        TySpinLockLock(&Lock);
        p = find(rx);
        c = *p;
        if (c == NULL) {
                TySpinLockUnlock(&Lock);
                return;
        }
        *p = c->next;
        Stats.used -= c->size;
        --Stats.nchunks;
        if (c->pool == NULL) {
                munmap(c->rx, c->size);
                Stats.allocated -= c->size;
                free(c);
        } else {
                --c->pool->live;
                if (c->pool->retired) {
                        free(c);
                        TySpinLockUnlock(&Lock);
                        jm_trim();
                        return;
                }
                cls = size_class(c->size);
                if (cls >= 0) {
                        c->next = Classes[cls];
                        Classes[cls] = c;
                } else {
                        insert_extent(c);
                }
        }
        TySpinLockUnlock(&Lock);
}

void
jm_trim(void)
{
        JmRegion **p;
        TySpinLockLock(&Lock);
        while (Retired != NULL) {
                JmChunk *c = Retired;
                Retired = c->next;
                free(c);
        }
        if (Pool != NULL && Pool->live == 0) {
                reclaim_classes();
                while (Extents != NULL) {
                        JmChunk *c = Extents;
                        Extents = c->next;
                        free(c);
                }
                Pool->retired = true;
                Pool = NULL;
                RegionRX = NULL;
                RegionRW = NULL;
                RegionTried = false;
        }
        p = &Regions;
        while (*p != NULL) {
                JmRegion *pool = *p;
                if (pool->retired && pool->live == 0) {
                        *p = pool->next;
                        munmap(pool->rx, JM_REGION_SIZE);
                        if (pool->rw != NULL && pool->rw != pool->rx) {
                                munmap(pool->rw, JM_REGION_SIZE);
                        }
                        Stats.allocated -= JM_REGION_SIZE;
                        free(pool);
                } else {
                        p = &pool->next;
                }
        }
        TySpinLockUnlock(&Lock);
}

JitMemStats
jm_stats(void)
{
        JitMemStats result;
        TySpinLockLock(&Lock);
        result = Stats;
        TySpinLockUnlock(&Lock);
        return result;
}

void
jm_perf(void *rx, usize size, char const *name)
{
        char path[64];
        char prefix[64];
        char const *enabled = getenv("TY_JIT_PERF_MAP");
        int fd;
        int n;
        usize len;
        usize total;
        char *line;
        if (enabled == NULL || strcmp(enabled, "1") != 0) {
                return;
        }
        name = name == NULL ? "" : name;
        len = strcspn(name, "\r\n");
        n = snprintf(prefix, sizeof prefix, "%lx %zx ", (unsigned long)(uptr)rx, size);
        if (n < 0 || len > SIZE_MAX - (usize)n - 1) {
                return;
        }
        total = n + len + 1;
        line = malloc(total);
        if (line == NULL) {
                return;
        }
        memcpy(line, prefix, n);
        memcpy(line + n, name, len);
        line[total - 1] = '\n';
        snprintf(path, sizeof path, "/tmp/perf-%ld.map", (long)getpid());
        TySpinLockLock(&Lock);
        fd = open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0600);
        if (fd != -1) {
                usize off = 0;
                while (off < total) {
                        ssize_t written = write(fd, line + off, total - off);
                        if (written > 0) {
                                off += written;
                        } else if (written < 0 && errno == EINTR) {
                                continue;
                        } else {
                                break;
                        }
                }
                close(fd);
        }
        TySpinLockUnlock(&Lock);
        free(line);
}
