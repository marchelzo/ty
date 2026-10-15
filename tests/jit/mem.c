#include <pthread.h>
#include <unistd.h>
#include <sys/wait.h>

#include "lir/test.h"

static usize
assemble(JitMapping m, i32 value)
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
answer(JitMapping m)
{
#if defined(__aarch64__) || defined(__x86_64__)
        return ((i32 (*)(void))m.rx)();
#else
        return *(i32 *)m.rx;
#endif
}

static bool
install(JitMapping m, i32 value)
{
        jm_write_begin();
        return jm_write_end(m.rx, assemble(m, value));
}

static bool
runs(JitMapping m, i32 value)
{
        return install(m, value) && (answer(m) == value);
}

static void
trim(void)
{
        jm_trim();
        CHECK(jm_stats().allocated == 0);
}

static void
check_execute(void)
{
        JitMapping m = jm_alloc(64);

        CHECK(m.rx != NULL && m.rw != NULL);
        CHECK(install(m, 42));
        CHECK(answer(m) == 42);
        CHECK(!jm_write_end(m.rx, 64));

        jm_write_begin();
        CHECK(!jm_write_end(m.rx, 65));

        jm_free(m.rx);
        CHECK(jm_stats().used == 0 && jm_stats().nchunks == 0);

        JitMapping next = jm_alloc(63);

        CHECK(next.rx == m.rx);
        CHECK(install(next, 17));
        CHECK(answer(next) == 17);

        jm_free(next.rx);
        trim();
}

static void
check_classes(void)
{
        JitMapping maps[11];
        usize      bytes = 0;

        for (u32 i = 0; i < countof(maps); ++i) {
                usize size = (usize)1 << (6 + i);
                maps[i] = jm_alloc(size - 1);
                CHECK(maps[i].rx != NULL);
                CHECK(((uptr)maps[i].rx & 63) == 0);
                bytes += size;
        }

        CHECK(jm_stats().used == bytes);
        CHECK(jm_stats().nchunks == countof(maps));

        for (u32 i = 0; i < countof(maps); ++i) {
                void *rx = maps[i].rx;
                jm_free(rx);
                maps[i] = jm_alloc((usize)1 << (6 + i));
                CHECK(maps[i].rx == rx);
        }

        CHECK(jm_stats().used == bytes);

        for (u32 i = 0; i < countof(maps); ++i) {
                jm_free(maps[i].rx);
        }

        CHECK(jm_stats().used == 0);
        CHECK(jm_alloc(0).rx == NULL);
        CHECK(jm_alloc(SIZE_MAX).rx == NULL);

        trim();
}

static void
check_extents(void)
{
        enum { REGION = 128 << 20 };

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
        trim();

        a = jm_alloc(64);
        b = jm_alloc(128);
        jm_free(a.rx);
        jm_free(b.rx);

        c = jm_alloc(REGION);
        CHECK(c.rx == a.rx);
        CHECK(jm_stats().allocated == REGION);

        jm_free(c.rx);
        trim();

        c = jm_alloc(REGION + 64);

        if (c.rx != NULL) {
                CHECK(install(c, 31));
                CHECK(answer(c) == 31);
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
        CHECK(jm_write_end(a.rx, assemble(a, 11)));
        CHECK(jm_write_end(b.rx, assemble(b, 12)));
        CHECK(answer(a) == 11 && answer(b) == 12);

        jm_free(a.rx);
        jm_free(b.rx);
        jm_trim();
}

static void *
thread(void *data)
{
        u64 seed = (uptr)data + 1;

        for (u32 i = 0; i < 2000; ++i) {
                JitMapping m = jm_alloc(64 + xorshift(&seed) % 131072);

                if (m.rx == NULL) {
                        return (void *)1;
                }

                bool ok = runs(m, 42);
                jm_free(m.rx);

                if (!ok) {
                        return (void *)1;
                }
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
        trim();
}

static int
child(JitMapping m)
{
        if (answer(m) != 42) {
                return 1;
        }

        jm_trim();

        if (answer(m) != 42) {
                return 2;
        }

        jm_free(m.rx);

        JitMapping next = jm_alloc(64);

        if (next.rx == NULL) {
                return 3;
        }

        if (!runs(next, 17)) {
                return 4;
        }

        jm_free(next.rx);
        jm_trim();

        return (jm_stats().used != 0 || jm_stats().allocated != 0) ? 5 : 0;
}

static void
check_fork(void)
{
        JitMapping m = jm_alloc(64);

        CHECK(install(m, 42));

        pid_t pid = fork();
        CHECK(pid != -1);

        if (pid == 0) {
                _exit(child(m));
        }

        if (pid > 0) {
                int status;
                CHECK(waitpid(pid, &status, 0) == pid);
                CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 0);
        }

        CHECK(answer(m) == 42);

        jm_free(m.rx);
        jm_trim();
}

static void
check_perf(void)
{
        char          path[64];
        char          line[128];
        char          name[64];
        unsigned long address;
        usize         size;

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

        return report("JIT memory");
}
