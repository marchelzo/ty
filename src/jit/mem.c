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
#include "jit/lir.h"

#if defined(__APPLE__) && defined(MAP_JIT)
  #define JM_MAP_JIT 1
#else
  #define JM_MAP_JIT 0
#endif

enum {
        JM_REGION = 128 << 20,
        JM_SHIFT  = 6,
        JM_ALIGN  = 1 << JM_SHIFT,
        JM_BUCKET = 4096
};

typedef struct region {
        void          *rw;
        void          *rx;
        usize          live;
        bool           retired;
        struct region *next;
} Region;

typedef struct chunk {
        void         *rw;
        void         *rx;
        usize         offset;
        usize         size;
        usize         requested;
        Region       *pool;
        struct chunk *next;
} Chunk;

#define new0(T) ((T *)alloc0(sizeof (T)))

#define RW   (PROT_READ | PROT_WRITE)
#define RX   (PROT_READ | PROT_EXEC)
#define RWX  (PROT_READ | PROT_WRITE | PROT_EXEC)
#define ANON (MAP_PRIVATE | MAP_ANONYMOUS)

static TySpinLock          Lock = TY_MUTEX_INIT;
static pthread_once_t      Once = PTHREAD_ONCE_INIT;
static Chunk              *Active[JM_BUCKET];
static Chunk              *Extents;
static Chunk              *Retired;
static Region             *Regions;
static Region             *Pool;
static u8                 *RegionRW;
static u8                 *RegionRX;
static bool                RegionTried;
static bool                ForkReady;
static JitMemStats         Stats;
static _Thread_local u32   WriteDepth;

inline static void
lock(void)
{
        TySpinLockLock(&Lock);
}

inline static void
unlock(void)
{
        TySpinLockUnlock(&Lock);
}

inline static usize
roundup(usize n, usize a)
{
        return (n + a - 1) / a * a;
}

inline static bool
perfmap(void)
{
        char const *env = getenv("TY_JIT_PERF_MAP");
        return (env != NULL) && s_eq(env, "1");
}

static Chunk **
find(void const *rx)
{
        Chunk **p = &Active[((uptr)rx >> JM_SHIFT) & (JM_BUCKET - 1)];

        while (*p != NULL && (*p)->rx != rx) {
                p = &(*p)->next;
        }

        return p;
}

static void
drain(Chunk **list)
{
        while (*list != NULL) {
                Chunk *c = *list;
                *list = c->next;
                xmF(c);
        }
}

static void
absorb(Chunk *c, Chunk *next)
{
        if (next != NULL && c->offset + c->size == next->offset) {
                c->size += next->size;
                c->next  = next->next;
                xmF(next);
        }
}

static void
insert_extent(Chunk *c)
{
        Chunk **p    = &Extents;
        Chunk  *prev = NULL;

        while (*p != NULL && (*p)->offset < c->offset) {
                prev = *p;
                p    = &prev->next;
        }

        c->next = *p;
        *p      = c;

        absorb(c, c->next);

        if (prev != NULL) {
                absorb(prev, c);
        }
}

static void
fork_child(void)
{
        TySpinLockInit(&Lock);
        WriteDepth = 0;

#if defined(__linux__)
        if (Pool != NULL) {
                Pool->retired = true;
                munmap(Pool->rw, JM_REGION);
                Pool->rw = NULL;
        }

        while (Extents != NULL) {
                Chunk *c = Extents;
                Extents  = c->next;
                c->next  = Retired;
                Retired  = c;
        }

        Pool        = NULL;
        RegionRW    = NULL;
        RegionRX    = NULL;
        RegionTried = false;
#endif
}

static void
initialize(void)
{
        ForkReady = (pthread_atfork(lock, unlock, fork_child) == 0);
}

static void *
map(usize n, int prot, int flags, int fd)
{
        return mmap(NULL, n, prot, flags, fd, 0);
}

static bool
map_region(void **rw, void **rx)
{
        *rw = MAP_FAILED;
        *rx = MAP_FAILED;

#if JM_MAP_JIT
        *rw = *rx = map(JM_REGION, RWX, ANON | MAP_JIT, -1);
#elif defined(__linux__)
        if (perfmap()) {
                *rw = *rx = map(JM_REGION, RWX, ANON, -1);
                return *rw != MAP_FAILED;
        }

        int fd = memfd_create("ty-jit", MFD_CLOEXEC);

        if (fd == -1) {
                return false;
        }

        if (ftruncate(fd, JM_REGION) == 0) {
                *rw = map(JM_REGION, RW, MAP_SHARED, fd);
        }

        if (*rw != MAP_FAILED) {
                *rx = map(JM_REGION, RX, MAP_SHARED, fd);
        }

        close(fd);
#endif

        if (*rx == MAP_FAILED && *rw != MAP_FAILED) {
                munmap(*rw, JM_REGION);
        }

        return *rx != MAP_FAILED;
}

static void
region_init(void)
{
        void *rw;
        void *rx;

        if (!ForkReady || !map_region(&rw, &rx)) {
                return;
        }

        Region *pool = new0(Region);

        pool->rw   = rw;
        pool->rx   = rx;
        pool->next = Regions;

        Regions  = pool;
        Pool     = pool;
        RegionRW = rw;
        RegionRX = rx;

        Extents       = new0(Chunk);
        Extents->size = JM_REGION;

        Stats.allocated += JM_REGION;
}

static Chunk *
region_alloc(usize n)
{
        Chunk **p = &Extents;

        while (*p != NULL && (*p)->size < n) {
                p = &(*p)->next;
        }

        Chunk *e = *p;
        Chunk *c;

        if (e == NULL) {
                return NULL;
        }

        if (e->size == n) {
                *p = e->next;
                c  = e;
        } else {
                c          = new0(Chunk);
                c->offset  = e->offset;
                c->size    = n;
                e->offset += n;
                e->size   -= n;
        }

        c->rw   = RegionRW + c->offset;
        c->rx   = RegionRX + c->offset;
        c->pool = Pool;

        return c;
}

static Chunk *
map_one(usize size)
{
        long page = sysconf(_SC_PAGESIZE);

        if (page <= 0 || size > SIZE_MAX - page + 1) {
                return NULL;
        }

        usize n = roundup(size, page);

#if JM_MAP_JIT
        void *p = map(n, RWX, ANON | MAP_JIT, -1);
#else
        void *p = map(n, RW, ANON, -1);
#endif

        if (p == MAP_FAILED) {
                return NULL;
        }

        Chunk *c = new0(Chunk);

        c->rw   = p;
        c->rx   = p;
        c->size = n;

        Stats.allocated += n;

        return c;
}

JitMapping
jm_alloc(usize size)
{
        JitMapping out = {0};

        if (size == 0 || size > SIZE_MAX - (JM_ALIGN - 1)) {
                return out;
        }

        pthread_once(&Once, initialize);

        usize n = roundup(size, JM_ALIGN);

        lock();

        drain(&Retired);

        if (!RegionTried) {
                RegionTried = true;
                region_init();
        }

        Chunk *c = (RegionRX != NULL) ? region_alloc(n) : NULL;

        if (c == NULL) {
                c = map_one(n);
        }

        if (c != NULL) {
                Chunk **head = find(c->rx);

                c->requested = size;
                c->next      = *head;
                *head        = c;

                Stats.used    += c->size;
                Stats.nchunks += 1;

                if (c->pool != NULL) {
                        c->pool->live += 1;
                }

                out = (JitMapping) { .rw = c->rw, .rx = c->rx };
        }

        unlock();

        return out;
}

void
jm_write_begin(void)
{
#if defined(__APPLE__) && defined(__aarch64__)
        if (WriteDepth == 0) {
                pthread_jit_write_protect_np(0);
        }
#endif
        WriteDepth += 1;
}

bool
jm_write_end(void *rx, usize size)
{
        if (WriteDepth == 0) {
                return false;
        }

        WriteDepth -= 1;

#if defined(__APPLE__) && defined(__aarch64__)
        if (WriteDepth == 0) {
                pthread_jit_write_protect_np(1);
        }
#endif

        lock();

        Chunk *c  = *find(rx);
        bool   ok = (c != NULL)
                 && (size <= c->requested)
                 && (c->pool == NULL || !c->pool->retired);

#if !JM_MAP_JIT
        if (ok && c->pool == NULL) {
                ok = (mprotect(c->rx, c->size, RX) == 0);
        }
#endif

        unlock();

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
        if (rx == NULL) {
                return;
        }

        lock();

        Chunk **p = find(rx);
        Chunk  *c = *p;

        if (c == NULL) {
                unlock();
                return;
        }

        Region *pool = c->pool;
        bool    trim = (pool != NULL) && pool->retired;

        *p = c->next;

        Stats.used    -= c->size;
        Stats.nchunks -= 1;

        if (pool == NULL) {
                munmap(c->rx, c->size);
                Stats.allocated -= c->size;
                xmF(c);
        } else if (trim) {
                pool->live -= 1;
                xmF(c);
        } else {
                pool->live -= 1;
                insert_extent(c);
        }

        unlock();

        if (trim) {
                jm_trim();
        }
}

static void
unmap_region(Region *pool)
{
        munmap(pool->rx, JM_REGION);

        if (pool->rw != NULL && pool->rw != pool->rx) {
                munmap(pool->rw, JM_REGION);
        }

        Stats.allocated -= JM_REGION;
        xmF(pool);
}

void
jm_trim(void)
{
        lock();

        drain(&Retired);

        if (Pool != NULL && Pool->live == 0) {
                drain(&Extents);
                Pool->retired = true;
                Pool          = NULL;
                RegionRX      = NULL;
                RegionRW      = NULL;
                RegionTried   = false;
        }

        for (Region **p = &Regions; *p != NULL;) {
                Region *pool = *p;
                if (pool->retired && pool->live == 0) {
                        *p = pool->next;
                        unmap_region(pool);
                } else {
                        p = &pool->next;
                }
        }

        unlock();
}

JitMemStats
jm_stats(void)
{
        lock();
        JitMemStats out = Stats;
        unlock();

        return out;
}

static void
writeall(int fd, char const *p, usize n)
{
        while (n > 0) {
                ssize_t w = write(fd, p, n);
                if (w > 0) {
                        p += w;
                        n -= w;
                } else if (w == 0 || errno != EINTR) {
                        return;
                }
        }
}

void
jm_perf(void *rx, usize size, char const *name)
{
        if (!perfmap()) {
                return;
        }

        name = (name != NULL) ? name : "";

        int  len = strcspn(name, "\r\n");
        char path[64];

#define LINE "%lx %zx %.*s\n", (unsigned long)(uptr)rx, size, len, name
        int  n = ty_snprintf(NULL, 0, LINE);
        char line[n + 1];
        ty_snprintf(line, sizeof line, LINE);
#undef LINE

        ty_snprintf(path, sizeof path, "/tmp/perf-%ld.map", (long)getpid());

        lock();

        int fd = open(path, O_WRONLY | O_CREAT | O_APPEND | O_CLOEXEC, 0600);

        if (fd != -1) {
                writeall(fd, line, n);
                close(fd);
        }

        unlock();
}
