#include <stdatomic.h>
#include <string.h>

#include <xxhash.h>

#include "ty.h"
#include "panic.h"

typedef struct {
        char const *text;
        u32         len;
        u32         id;
        u64         hash;
} SourceKey;

Source *SourcePages[TY_SOURCE_PAGES];

static atomic_flag Lock = ATOMIC_FLAG_INIT;
static u32         Count;
static SourceKey  *Keys;
static u32         KeyCap;

inline static void
lock(void)
{
        while (atomic_flag_test_and_set_explicit(&Lock, memory_order_acquire)) {
                ;
        }
}

inline static void
unlock(void)
{
        atomic_flag_clear_explicit(&Lock, memory_order_release);
}

inline static u32
slot(char const *text, u32 len, u64 hash, u32 cap)
{
        return (u32)((hash ^ (uptr)text ^ len) & (cap - 1));
}

static void
grow(void)
{
        u32 cap = (KeyCap == 0) ? 1024 : 2 * KeyCap;
        SourceKey *keys = calloc(cap, sizeof *keys);

        if (keys == NULL) {
                panic("out of memory: source registry");
        }

        for (u32 i = 0; i < KeyCap; ++i) {
                SourceKey const *k = &Keys[i];
                if (k->id == 0) {
                        continue;
                }
                u32 h = slot(k->text, k->len, k->hash, cap);
                while (keys[h].id != 0) {
                        h = (h + 1) & (cap - 1);
                }
                keys[h] = *k;
        }

        free(Keys);

        Keys   = keys;
        KeyCap = cap;
}

static u32 const *
index_lines(char const *text, u32 len, u32 *n)
{
        u32 count = 1;
        u32 *lines;

        for (char const *p = text; (p = memchr(p, '\n', text + len - p)) != NULL; ++p) {
                count += 1;
        }

        lines = malloc(count * sizeof *lines);
        if (lines == NULL) {
                panic("out of memory: source line index");
        }

        lines[0] = 0;
        count    = 1;

        for (char const *p = text; (p = memchr(p, '\n', text + len - p)) != NULL; ++p) {
                lines[count++] = (u32)(p - text) + 1;
        }

        *n = count;

        return lines;
}

u32
SourceRegister(char const *text, usize len)
{
        u64 hash = XXH3_64bits(text, len);
        u32 id;
        u32 h;

        lock();

        if (4 * (Count + 1) >= 3 * KeyCap) {
                grow();
        }

        h = slot(text, (u32)len, hash, KeyCap);

        while (Keys[h].id != 0) {
                if (
                        (Keys[h].text == text)
                     && (Keys[h].len  == len)
                     && (Keys[h].hash == hash)
                ) {
                        id = Keys[h].id;
                        unlock();
                        return id;
                }
                h = (h + 1) & (KeyCap - 1);
        }

        id = ++Count;

        if (id >= TY_SOURCE_PAGES * TY_SOURCE_PAGE_SIZE) {
                panic("source registry exhausted");
        }

        if (SourcePages[id >> TY_SOURCE_PAGE_BITS] == NULL) {
                SourcePages[id >> TY_SOURCE_PAGE_BITS] = calloc(TY_SOURCE_PAGE_SIZE, sizeof (Source));
                if (SourcePages[id >> TY_SOURCE_PAGE_BITS] == NULL) {
                        panic("out of memory: source registry");
                }
        }

        Source *src = SourceOf(id);

        src->text  = text;
        src->len   = (u32)len;
        src->hash  = hash;
        src->lines = index_lines(text, (u32)len, &src->nl);

        Keys[h] = (SourceKey) {
                .text = text,
                .len  = (u32)len,
                .id   = id,
                .hash = hash
        };

        unlock();

        return id;
}

u32
SourceLineOf(Source const *src, u32 byte)
{
        u32 lo = 0;
        u32 hi = src->nl;

        while (hi - lo > 1) {
                u32 mid = lo + (hi - lo) / 2;
                if (src->lines[mid] <= byte) {
                        lo = mid;
                } else {
                        hi = mid;
                }
        }

        return lo;
}

/* vim: set sts=8 sw=8 expandtab: */
