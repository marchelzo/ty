#include <stdlib.h>
#include <string.h>

#include "qcache.h"

#ifndef _WIN32
#include "ty/thread.h"

static TyMutex CacheLock = TY_MUTEX_INIT;
static void *Cache[8];
static usize NCache;
#endif

#if defined(__linux__) && defined(__GLIBC__) && __has_include(<sys/rseq.h>)
#if defined(__x86_64__) || defined(__aarch64__)
#define TY_QUEUE_RSEQ 1
#include <sys/rseq.h>

#pragma weak __rseq_offset
#pragma weak __rseq_size

struct cpu_cache {
        _Alignas(64) void *items[4];
        usize count;
};

_Static_assert(sizeof (struct cpu_cache) == 64, "CPU cache stride");
_Static_assert(offsetof(struct cpu_cache, count) == 32, "CPU cache count offset");

static struct cpu_cache CpuCache[1024];
static pthread_once_t RseqOnce = PTHREAD_ONCE_INIT;
static bool RseqEnabled;

static void
rseq_init(void)
{
        char const *s = getenv("TY_RSEQ");
        RseqEnabled = (&__rseq_size != NULL)
                   && (&__rseq_offset != NULL)
                   && (__rseq_size >= 20)
                   && (s == NULL || strcmp(s, "0") != 0);
}

static struct rseq *
rseq_area(void)
{
        pthread_once(&RseqOnce, rseq_init);
        if (!RseqEnabled) {
                return NULL;
        }
        struct rseq *r = (void *)((char *)__builtin_thread_pointer() + __rseq_offset);
        if ((i32)*(volatile u32 *)&r->cpu_id < 0) {
                return NULL;
        }
        return r;
}

static void *
cpu_take(struct rseq *r)
{
        void *p;
#if defined(__x86_64__)
        __asm__ volatile (
                ".pushsection __rseq_cs,\"aw\"\n"
                ".balign 32\n"
                "300: .long 0, 0\n"
                ".quad 301f, 302f-301f, 303f\n"
                ".popsection\n"
                "xor %[p], %[p]\n"
                "lea 300b(%%rip), %%rax\n"
                "mov %%rax, 8(%[r])\n"
                "301: mov 4(%[r]), %%ecx\n"
                "cmp $1024, %%ecx\n"
                "jae 302f\n"
                "shl $6, %%rcx\n"
                "add %[cache], %%rcx\n"
                "mov 32(%%rcx), %%rdx\n"
                "test %%rdx, %%rdx\n"
                "jz 302f\n"
                "dec %%rdx\n"
                "mov (%%rcx,%%rdx,8), %[p]\n"
                "mov %%rdx, 32(%%rcx)\n"
                "302: movq $0, 8(%[r])\n"
                ".pushsection __rseq_failure,\"ax\"\n"
                ".byte 0x0f, 0xb9, 0x3d\n"
                ".long 0x53053053\n"
                "303: xor %[p], %[p]\n"
                "jmp 302b\n"
                ".popsection\n"
                : [p] "=&r" (p)
                : [r] "r" (r), [cache] "r" (CpuCache)
                : "rax", "rcx", "rdx", "memory", "cc"
        );
#elif defined(__aarch64__)
        __asm__ volatile (
                ".pushsection __rseq_cs,\"aw\"\n"
                ".balign 32\n"
                "300: .long 0, 0\n"
                ".quad 301f, 302f-301f, 303f\n"
                ".popsection\n"
                "mov %[p], xzr\n"
                "adrp x9, 300b\n"
                "add x9, x9, :lo12:300b\n"
                "str x9, [%[r], #8]\n"
                "301: ldr w10, [%[r], #4]\n"
                "cmp w10, #1024\n"
                "b.hs 302f\n"
                "add x9, %[cache], x10, lsl #6\n"
                "ldr x10, [x9, #32]\n"
                "cbz x10, 302f\n"
                "sub x10, x10, #1\n"
                "ldr %[p], [x9, x10, lsl #3]\n"
                "str x10, [x9, #32]\n"
                "302: str xzr, [%[r], #8]\n"
                ".pushsection __rseq_failure,\"ax\"\n"
                ".long 0xd428bc00\n"
                "303: mov %[p], xzr\n"
                "b 302b\n"
                ".popsection\n"
                : [p] "=&r" (p)
                : [r] "r" (r), [cache] "r" (CpuCache)
                : "x9", "x10", "memory", "cc"
        );
#endif
        return p;
}

static bool
cpu_put(struct rseq *r, void *p)
{
        int ok;
#if defined(__x86_64__)
        __asm__ volatile (
                ".pushsection __rseq_cs,\"aw\"\n"
                ".balign 32\n"
                "300: .long 0, 0\n"
                ".quad 301f, 302f-301f, 303f\n"
                ".popsection\n"
                "xor %k[ok], %k[ok]\n"
                "lea 300b(%%rip), %%rax\n"
                "mov %%rax, 8(%[r])\n"
                "301: mov 4(%[r]), %%ecx\n"
                "cmp $1024, %%ecx\n"
                "jae 302f\n"
                "shl $6, %%rcx\n"
                "add %[cache], %%rcx\n"
                "mov 32(%%rcx), %%rdx\n"
                "cmp $4, %%rdx\n"
                "jae 302f\n"
                "mov %[p], (%%rcx,%%rdx,8)\n"
                "inc %%rdx\n"
                "mov $1, %k[ok]\n"
                "mov %%rdx, 32(%%rcx)\n"
                "302: movq $0, 8(%[r])\n"
                ".pushsection __rseq_failure,\"ax\"\n"
                ".byte 0x0f, 0xb9, 0x3d\n"
                ".long 0x53053053\n"
                "303: xor %k[ok], %k[ok]\n"
                "jmp 302b\n"
                ".popsection\n"
                : [ok] "=&r" (ok)
                : [r] "r" (r), [cache] "r" (CpuCache), [p] "r" (p)
                : "rax", "rcx", "rdx", "memory", "cc"
        );
#elif defined(__aarch64__)
        __asm__ volatile (
                ".pushsection __rseq_cs,\"aw\"\n"
                ".balign 32\n"
                "300: .long 0, 0\n"
                ".quad 301f, 302f-301f, 303f\n"
                ".popsection\n"
                "mov %w[ok], wzr\n"
                "adrp x9, 300b\n"
                "add x9, x9, :lo12:300b\n"
                "str x9, [%[r], #8]\n"
                "301: ldr w10, [%[r], #4]\n"
                "cmp w10, #1024\n"
                "b.hs 302f\n"
                "add x9, %[cache], x10, lsl #6\n"
                "ldr x10, [x9, #32]\n"
                "cmp x10, #4\n"
                "b.hs 302f\n"
                "str %[p], [x9, x10, lsl #3]\n"
                "add x10, x10, #1\n"
                "mov %w[ok], #1\n"
                "str x10, [x9, #32]\n"
                "302: str xzr, [%[r], #8]\n"
                ".pushsection __rseq_failure,\"ax\"\n"
                ".long 0xd428bc00\n"
                "303: mov %w[ok], wzr\n"
                "b 302b\n"
                ".popsection\n"
                : [ok] "=&r" (ok)
                : [r] "r" (r), [cache] "r" (CpuCache), [p] "r" (p)
                : "x9", "x10", "memory", "cc"
        );
#endif
        return ok;
}
#endif
#endif

void *
queue_cache_take(void)
{
#ifdef TY_QUEUE_RSEQ
        struct rseq *r = rseq_area();
        if (r != NULL) {
                void *p = cpu_take(r);
                if (p != NULL) {
                        return p;
                }
        }
#endif
        void *p = NULL;
#ifndef _WIN32
        TyMutexLock(&CacheLock);
        if (NCache != 0) {
                p = Cache[--NCache];
        }
        TyMutexUnlock(&CacheLock);
#endif
        return p;
}

bool
queue_cache_put(void *p)
{
#ifdef TY_QUEUE_RSEQ
        struct rseq *r = rseq_area();
        if (r != NULL && cpu_put(r, p)) {
                return true;
        }
#endif
        bool ok = false;
#ifndef _WIN32
        TyMutexLock(&CacheLock);
        if (NCache < countof(Cache)) {
                Cache[NCache++] = p;
                ok = true;
        }
        TyMutexUnlock(&CacheLock);
#endif
        return ok;
}

u32
queue_cpu_hint(u32 fallback)
{
#ifdef TY_QUEUE_RSEQ
        struct rseq *r = rseq_area();
        if (r != NULL) {
                return *(volatile u32 *)&r->cpu_id;
        }
#endif
        return fallback;
}
