#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include <unistd.h>
#include <sys/wait.h>

#include "lir.h"

static u32 checks;
static u32 failures;

#define CHECK(expr) do { \
        ++checks; \
        if (!(expr)) { \
                fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, #expr); \
                ++failures; \
        } \
} while (0)

static usize
write_function(JitMapping m, i32 value)
{
#if defined(__aarch64__)
        u32 words[] = { 0x52800000 | ((u32)value << 5), 0xd65f03c0 };
        memcpy(m.rw, words, sizeof words);
        return sizeof words;
#elif defined(__x86_64__)
        u8 bytes[] = { 0xb8, value, 0, 0, 0, 0xc3 };
        memcpy(m.rw, bytes, sizeof bytes);
        return sizeof bytes;
#else
        memcpy(m.rw, &value, sizeof value);
        return sizeof value;
#endif
}

static i32
call_function(JitMapping m)
{
#if defined(__aarch64__) || defined(__x86_64__)
        return ((i32 (*)(void))m.rx)();
#else
        return *(i32 *)m.rx;
#endif
}

static void
check_execute(void)
{
        JitMapping m = jm_alloc(64);
        CHECK(m.rx != NULL && m.rw != NULL);
        jm_write_begin();
        usize n = write_function(m, 42);
        CHECK(jm_write_end(m.rx, n));
        CHECK(call_function(m) == 42);
        CHECK(!jm_write_end(m.rx, n));
        jm_write_begin();
        CHECK(!jm_write_end(m.rx, 65));
        jm_free(m.rx);
        CHECK(jm_stats().used == 0 && jm_stats().nchunks == 0);
        JitMapping next = jm_alloc(63);
        CHECK(next.rx == m.rx);
        jm_write_begin();
        n = write_function(next, 17);
        CHECK(jm_write_end(next.rx, n));
        CHECK(call_function(next) == 17);
        jm_free(next.rx);
        jm_trim();
        CHECK(jm_stats().allocated == 0);
}

static void
check_classes(void)
{
        JitMapping mappings[11];
        usize bytes = 0;
        for (u32 i = 0; i < countof(mappings); ++i) {
                usize size = (usize)1 << (6 + i);
                mappings[i] = jm_alloc(size - 1);
                CHECK(mappings[i].rx != NULL);
                CHECK(((uptr)mappings[i].rx & 63) == 0);
                bytes += size;
        }
        CHECK(jm_stats().used == bytes);
        CHECK(jm_stats().nchunks == countof(mappings));
        for (u32 i = 0; i < countof(mappings); ++i) {
                void *rx = mappings[i].rx;
                jm_free(rx);
                JitMapping next = jm_alloc((usize)1 << (6 + i));
                CHECK(next.rx == rx);
                jm_free(next.rx);
        }
        CHECK(jm_stats().used == 0);
        CHECK(jm_alloc(0).rx == NULL);
        CHECK(jm_alloc(SIZE_MAX).rx == NULL);
        jm_trim();
        CHECK(jm_stats().allocated == 0);
}

static void
check_extents(void)
{
        JitMapping a = jm_alloc(70000);
        JitMapping b = jm_alloc(90000);
        JitMapping c = jm_alloc(131072);
        CHECK(a.rx != NULL && b.rx != NULL && c.rx != NULL);
        jm_free(a.rx);
        jm_free(b.rx);
        JitMapping d = jm_alloc(150000);
        CHECK(d.rx == a.rx);
        jm_free(d.rx);
        jm_free(c.rx);
        jm_trim();
        CHECK(jm_stats().allocated == 0);
        a = jm_alloc(64);
        b = jm_alloc(128);
        jm_free(a.rx);
        jm_free(b.rx);
        c = jm_alloc(128 << 20);
        CHECK(c.rx == a.rx);
        CHECK(jm_stats().allocated == (128 << 20));
        jm_free(c.rx);
        jm_trim();
        CHECK(jm_stats().allocated == 0);
        c = jm_alloc((128 << 20) + 64);
        if (c.rx != NULL) {
                jm_write_begin();
                usize n = write_function(c, 31);
                CHECK(jm_write_end(c.rx, n));
                CHECK(call_function(c) == 31);
                jm_free(c.rx);
        }
        jm_trim();
        CHECK(jm_stats().allocated == 0 && jm_stats().nchunks == 0);
}

static void
check_nested(void)
{
        JitMapping a = jm_alloc(64);
        JitMapping b = jm_alloc(64);
        jm_write_begin();
        jm_write_begin();
        usize na = write_function(a, 11);
        CHECK(jm_write_end(a.rx, na));
        usize nb = write_function(b, 12);
        CHECK(jm_write_end(b.rx, nb));
        CHECK(call_function(a) == 11 && call_function(b) == 12);
        jm_free(a.rx);
        jm_free(b.rx);
        jm_trim();
}

static void *
thread(void *data)
{
        u64 seed = (uptr)data + 1;
        for (u32 i = 0; i < 2000; ++i) {
                seed ^= seed << 13;
                seed ^= seed >> 7;
                seed ^= seed << 17;
                usize size = 64 + seed % 131072;
                JitMapping m = jm_alloc(size);
                if (m.rx == NULL) {
                        return (void *)1;
                }
                jm_write_begin();
                usize n = write_function(m, 42);
                if (!jm_write_end(m.rx, n) || call_function(m) != 42) {
                        jm_free(m.rx);
                        return (void *)1;
                }
                jm_free(m.rx);
        }
        return NULL;
}

static void
check_threads(void)
{
        pthread_t threads[8];
        for (u32 i = 0; i < countof(threads); ++i) {
                CHECK(pthread_create(&threads[i], NULL, thread, (void *)(uptr)i) == 0);
        }
        for (u32 i = 0; i < countof(threads); ++i) {
                void *status;
                CHECK(pthread_join(threads[i], &status) == 0);
                CHECK(status == NULL);
        }
        CHECK(jm_stats().used == 0 && jm_stats().nchunks == 0);
        jm_trim();
        CHECK(jm_stats().allocated == 0);
}

static void
check_fork(void)
{
        JitMapping m = jm_alloc(64);
        jm_write_begin();
        usize n = write_function(m, 42);
        CHECK(jm_write_end(m.rx, n));
        pid_t pid = fork();
        CHECK(pid != -1);
        if (pid == 0) {
                if (call_function(m) != 42) {
                        _exit(1);
                }
                jm_trim();
                if (call_function(m) != 42) {
                        _exit(2);
                }
                jm_free(m.rx);
                JitMapping next = jm_alloc(64);
                if (next.rx == NULL) {
                        _exit(3);
                }
                jm_write_begin();
                n = write_function(next, 17);
                if (!jm_write_end(next.rx, n) || call_function(next) != 17) {
                        _exit(4);
                }
                jm_free(next.rx);
                jm_trim();
                if (jm_stats().used != 0 || jm_stats().allocated != 0) {
                        _exit(5);
                }
                _exit(0);
        }
        if (pid > 0) {
                int status;
                CHECK(waitpid(pid, &status, 0) == pid);
                CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 0);
        }
        CHECK(call_function(m) == 42);
        jm_free(m.rx);
        jm_trim();
}

static void
check_perf(void)
{
        char path[64];
        char line[128];
        unsigned long address;
        usize size;
        char name[64];
        snprintf(path, sizeof path, "/tmp/perf-%ld.map", (long)getpid());
        unlink(path);
        setenv("TY_JIT_PERF_MAP", "0", 1);
        jm_perf((void *)0x123456, 31, "test");
        CHECK(access(path, F_OK) != 0);
        setenv("TY_JIT_PERF_MAP", "1", 1);
        jm_perf((void *)0x123456, 31, "jit.test");
        FILE *f = fopen(path, "r");
        CHECK(f != NULL);
        if (f != NULL) {
                CHECK(fgets(line, sizeof line, f) != NULL);
                CHECK(sscanf(line, "%lx %zx %63s", &address, &size, name) == 3);
                CHECK(address == 0x123456 && size == 31 && strcmp(name, "jit.test") == 0);
                fclose(f);
        }
        unlink(path);
        unsetenv("TY_JIT_PERF_MAP");
}

int
main(void)
{
        check_execute();
        check_classes();
        check_extents();
        check_nested();
        check_threads();
        check_fork();
        check_perf();
        printf("JIT memory: %u checks, %u failures\n", checks, failures);
        return failures != 0;
}
