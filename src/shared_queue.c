#include <limits.h>

#if defined(__linux__) && !defined(TY_NO_FUTEX)
#define TY_QUEUE_FUTEX 1
#include <linux/futex.h>
#include <sys/syscall.h>
#include <unistd.h>
#endif

#include "queue.h"
#include "qcache.h"
#include "value.h"
#include "vm.h"

#define QUEUE_BLOCK_N 64
#define QUEUE_EPOCH (UINT64_C(1) << 32)

struct queue_block {
        _Atomic(struct queue_block *) next;
        atomic_uint                   used;
        struct queue_block *spare;
        Value items[QUEUE_BLOCK_N];
};

struct queue_lane {
        _Alignas(64) TyMutex read;
        struct queue_block *first;
        usize         head;
        _Atomic usize taken;
        _Alignas(64) TyMutex write;
        struct queue_block *last;
        usize         tail;
        _Atomic usize given;
};

static struct queue_block *
block_new(Ty *ty)
{
        struct queue_block *b = queue_cache_take();
        if (b == NULL) {
                b = uAo(sizeof *b, GC_ANY);
                NOGC(b);
        }
        atomic_init(&b->next, NULL);
        atomic_init(&b->used, 0);
        b->spare = NULL;
        return b;
}

static void
block_free(Ty *ty, struct queue_block *b)
{
        if (!queue_cache_put(b)) {
                OKGC(b);
        }
}

static void
blocks_free(Ty *ty, struct queue_block *b)
{
        while (b != NULL) {
                struct queue_block *next = b->spare;
                block_free(ty, b);
                b = next;
        }
}

static void
queue_lock(SharedQueue *q)
{
        for (usize i = 0; i < q->nlanes; ++i) {
                TyMutexLock(&q->lanes[i].read);
        }
        for (usize i = 0; i < q->nlanes; ++i) {
                TyMutexLock(&q->lanes[i].write);
        }
}

static void
queue_unlock(SharedQueue *q)
{
        for (usize i = q->nlanes; i != 0; --i) {
                TyMutexUnlock(&q->lanes[i - 1].write);
        }
        for (usize i = q->nlanes; i != 0; --i) {
                TyMutexUnlock(&q->lanes[i - 1].read);
        }
}

static usize
queue_size_locked(SharedQueue *q)
{
        usize n = 0;
        for (usize i = 0; i < q->nlanes; ++i) {
                n += atomic_load_explicit(&q->lanes[i].given, memory_order_relaxed)
                   - atomic_load_explicit(&q->lanes[i].taken, memory_order_relaxed);
        }
        return n;
}

#ifdef TY_QUEUE_FUTEX
static u32 *
queue_futex(SharedQueue *q)
{
        u32 *p = (void *)&q->event;
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
        ++p;
#endif
        return p;
}
#endif

static void
queue_notify(SharedQueue *q, usize n)
{
        u64 old = atomic_fetch_add_explicit(&q->event, QUEUE_EPOCH, memory_order_acq_rel);
        if ((u32)old == 0) {
                return;
        }
#ifdef TY_QUEUE_FUTEX
        syscall(SYS_futex, queue_futex(q), FUTEX_WAKE_PRIVATE, (int)min(n, INT_MAX), NULL, NULL, 0);
#else
        TyMutexLock(&q->park);
        if (n == 1) {
                TyCondVarSignal(&q->ready);
        } else {
                TyCondVarBroadcast(&q->ready);
        }
        TyMutexUnlock(&q->park);
#endif
}

static void
queue_park(Ty *ty, SharedQueue *q, u32 epoch, u64 deadline)
{
        UnlockTy();
#ifdef TY_QUEUE_FUTEX
        struct timespec ts;
        struct timespec *timeout = NULL;
        if (deadline != UINT64_MAX) {
                ts.tv_sec = deadline / TY_1e9;
                ts.tv_nsec = deadline % TY_1e9;
                timeout = &ts;
        }
        syscall(
                SYS_futex,
                queue_futex(q),
                FUTEX_WAIT_BITSET_PRIVATE,
                epoch,
                timeout,
                NULL,
                FUTEX_BITSET_MATCH_ANY
        );
#else
        TyMutexLock(&q->park);
        while ((atomic_load_explicit(&q->event, memory_order_acquire) >> 32) == epoch) {
                if (deadline == UINT64_MAX) {
                        TyCondVarWait(&q->ready, &q->park);
                        continue;
                }
                u64 now = TyMonotonicTime();
                if (now >= deadline) {
                        break;
                }
                u64 ms = min((deadline - now + TY_1e6 - 1) / TY_1e6, UINT_MAX);
                TyCondVarTimedWaitRelative(&q->ready, &q->park, ms);
        }
        TyMutexUnlock(&q->park);
#endif
        LockTy();
}

SharedQueue *
shared_queue_new(Ty *ty, usize nlanes, bool work)
{
        usize bytes = nlanes * sizeof (struct queue_lane);
        SharedQueue *q = mAo0(sizeof *q + 63 + bytes, GC_SHARED_QUEUE);
        q->lanes = (void *)(((uptr)(q + 1) + 63) & ~(uptr)63);
        q->nlanes = nlanes;
        q->work = work;
        atomic_init(&q->open, true);
        atomic_init(&q->event, 0);
        TyMutexInit(&q->park);
        TyCondVarInit(&q->ready);
        for (usize i = 0; i < nlanes; ++i) {
                struct queue_lane *s = &q->lanes[i];
                TyMutexInit(&s->read);
                TyMutexInit(&s->write);
                atomic_init(&s->taken, 0);
                atomic_init(&s->given, 0);
                s->first = s->last = block_new(ty);
        }
        return q;
}

void
shared_queue_free(Ty *ty, SharedQueue *q)
{
        for (usize i = 0; i < q->nlanes; ++i) {
                struct queue_lane *s = &q->lanes[i];
                struct queue_block *b = s->first;
                while (b != NULL) {
                        struct queue_block *next = atomic_load_explicit(&b->next, memory_order_relaxed);
                        block_free(ty, b);
                        b = next;
                }
                TyMutexDestroy(&s->read);
                TyMutexDestroy(&s->write);
        }
        TyMutexDestroy(&q->park);
        TyCondVarDestroy(&q->ready);
}

void
shared_queue_mark(Ty *ty, SharedQueue *q)
{
        if (MARKED(q)) {
                return;
        }
        MARK(q);
        for (usize i = 0; i < q->nlanes; ++i) {
                struct queue_lane *s = &q->lanes[i];
                struct queue_block *b = s->first;
                usize start = s->head;
                while (b != NULL) {
                        MARK(b);
                        usize end = atomic_load_explicit(&b->used, memory_order_relaxed);
                        for (usize j = start; j < end; ++j) {
                                xvP(ty->marking, &b->items[j]);
                        }
                        start = 0;
                        b = atomic_load_explicit(&b->next, memory_order_relaxed);
                }
        }
}

usize
shared_queue_count(SharedQueue *q)
{
        queue_lock(q);
        usize n = queue_size_locked(q);
        queue_unlock(q);
        return n;
}

static void
queue_put(Ty *ty, SharedQueue *q, Value const *xs, usize n)
{
        if (n == 0) {
                return;
        }
        usize i = (q->nlanes == 1) ? 0 : queue_cpu_hint(ty->id) % q->nlanes;
        struct queue_lane *s = &q->lanes[i];
        struct queue_block *spare = NULL;
        usize nspare = 0;
        TyMutexLock(&s->write);
        usize need = (s->tail + n - 1) / QUEUE_BLOCK_N;
        while (nspare < need) {
                TyMutexUnlock(&s->write);
                while (nspare < need) {
                        struct queue_block *b = block_new(ty);
                        b->spare = spare;
                        spare = b;
                        ++nspare;
                }
                TyMutexLock(&s->write);
                need = (s->tail + n - 1) / QUEUE_BLOCK_N;
        }
        usize left = n;
        while (left != 0) {
                if (s->tail == QUEUE_BLOCK_N) {
                        struct queue_block *b = spare;
                        spare = b->spare;
                        struct queue_block *old = s->last;
                        s->last = b;
                        s->tail = 0;
                        atomic_store_explicit(&old->next, b, memory_order_release);
                }
                usize k = min(left, QUEUE_BLOCK_N - s->tail);
                memcpy(s->last->items + s->tail, xs, k * sizeof *xs);
                s->tail += k;
                atomic_store_explicit(&s->last->used, s->tail, memory_order_release);
                xs += k;
                left -= k;
        }
        usize given = atomic_load_explicit(&s->given, memory_order_relaxed);
        atomic_store_explicit(&s->given, given + n, memory_order_release);
        TyMutexUnlock(&s->write);
        blocks_free(ty, spare);
        queue_notify(q, n);
}

static usize
lane_take(Ty *ty, struct queue_lane *s, Value *xs, usize n, bool peek)
{
        struct queue_block *retired = NULL;
        usize copied = 0;
        TyMutexLock(&s->read);
        while (copied < n) {
                struct queue_block *b = s->first;
                if (s->head == QUEUE_BLOCK_N) {
                        struct queue_block *next = atomic_load_explicit(&b->next, memory_order_acquire);
                        if (next == NULL) {
                                break;
                        }
                        TyMutexLock(&s->write);
                        s->first = next;
                        s->head = 0;
                        TyMutexUnlock(&s->write);
                        b->spare = retired;
                        retired = b;
                        b = next;
                }
                usize end = atomic_load_explicit(&b->used, memory_order_acquire);
                usize k = min(n - copied, end - s->head);
                if (k == 0) {
                        break;
                }
                memcpy(xs + copied, b->items + s->head, k * sizeof *xs);
                copied += k;
                if (peek) {
                        break;
                }
                s->head += k;
        }
        if (!peek) {
                usize taken = atomic_load_explicit(&s->taken, memory_order_relaxed);
                atomic_store_explicit(&s->taken, taken + copied, memory_order_release);
        }
        TyMutexUnlock(&s->read);
        blocks_free(ty, retired);
        return copied;
}

static usize
queue_take(Ty *ty, SharedQueue *q, Value *xs, usize n, bool peek)
{
        usize start = (q->nlanes == 1) ? 0 : (ty->id + ty->queue_cursor) % q->nlanes;
        usize taken = 0;
        for (usize i = 0; i < q->nlanes && taken < n; ++i) {
                struct queue_lane *s = &q->lanes[(start + i) % q->nlanes];
                if (
                        (q->nlanes > 1)
                     && (atomic_load_explicit(&s->given, memory_order_acquire)
                         == atomic_load_explicit(&s->taken, memory_order_acquire))
                ) {
                        continue;
                }
                taken += lane_take(ty, s, xs + taken, n - taken, peek);
        }
        if (peek && taken != 0) {
                queue_notify(q, 1);
        } else if (taken != 0) {
                ++ty->queue_cursor;
        }
        return taken;
}

static bool
queue_wait(Ty *ty, SharedQueue *q, Value *v, bool peek, u64 deadline)
{
        if (queue_take(ty, q, v, 1, peek)) {
                return true;
        }
        u64 state = atomic_fetch_add_explicit(&q->event, 1, memory_order_acq_rel);
        bool found;
        for (;;) {
                found = queue_take(ty, q, v, 1, peek) != 0;
                if (found) {
                        break;
                }
                if (!atomic_load_explicit(&q->open, memory_order_acquire)) {
                        found = queue_take(ty, q, v, 1, peek) != 0;
                        break;
                }
                if (deadline != UINT64_MAX && TyMonotonicTime() >= deadline) {
                        break;
                }
                queue_park(ty, q, state >> 32, deadline);
                state = atomic_load_explicit(&q->event, memory_order_acquire);
        }
        atomic_fetch_sub_explicit(&q->event, 1, memory_order_seq_cst);
        return found;
}

static Value
shared_queue_put(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.put()", 1);
        queue_put(ty, self->shared_queue, &ARG(0), 1);
        CheckUsed(ty);
        return *self;
}

static Value
shared_queue_put_all(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.put-all()", 1);
        Array *a = ARRAY_ARG(0);
        queue_put(ty, self->shared_queue, a->items, a->count);
        CheckUsed(ty);
        return *self;
}

static Value
shared_queue_take(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.take()", 0);
        Value v;
        if (!queue_wait(ty, self->shared_queue, &v, false, UINT64_MAX)) {
                CanceledError("queue is closed and empty");
        }
        return v;
}

static Value
shared_queue_try_take(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.try-take()", 0, 1);
        Value v;
        bool found;
        if (argc == 0) {
                found = queue_take(ty, self->shared_queue, &v, 1, false) != 0;
        } else {
                u64 ms = MSEC_TIMEOUT_ARG(0);
                u64 now = TyMonotonicTime();
                u64 deadline = UINT64_MAX;
                if (ms < (UINT64_MAX - now) / TY_1e6) {
                        deadline = now + ms * TY_1e6;
                }
                found = queue_wait(ty, self->shared_queue, &v, false, deadline);
        }
        return found ? Some(v) : None;
}

static Value
shared_queue_take_up_to(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.take-up-to()", 1);
        i64 n = INT_ARG(0);
        if (n < 0 || (u64)n > SIZE_MAX / sizeof (Value)) {
                bP("invalid batch size");
        }
        Array *a = mAo0(sizeof *a, GC_ARRAY);
        uvR(*a, n);
        a->count = queue_take(ty, self->shared_queue, a->items, n, false);
        return ARRAY(a);
}

static Value
shared_queue_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.peek()", 0);
        Value v;
        if (!queue_wait(ty, self->shared_queue, &v, true, UINT64_MAX)) {
                CanceledError("queue is closed and empty");
        }
        return v;
}

static Value
shared_queue_try_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.try-peek()", 0);
        Value v;
        return queue_take(ty, self->shared_queue, &v, 1, true) ? Some(v) : None;
}

static Value
shared_queue_len(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.len()", 0);
        return INTEGER(shared_queue_count(self->shared_queue));
}

static Value
shared_queue_empty(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.empty?()", 0);
        return BOOLEAN(shared_queue_count(self->shared_queue) == 0);
}

static Value
shared_queue_clear(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.clear()", 0);
        SharedQueue *q = self->shared_queue;
        struct queue_block *retired = NULL;
        queue_lock(q);
        for (usize i = 0; i < q->nlanes; ++i) {
                struct queue_lane *s = &q->lanes[i];
                struct queue_block *b = s->first;
                while (b != s->last) {
                        struct queue_block *next = atomic_load_explicit(&b->next, memory_order_relaxed);
                        b->spare = retired;
                        retired = b;
                        b = next;
                }
                s->first = b;
                s->head = s->tail = 0;
                atomic_store_explicit(&s->taken, 0, memory_order_relaxed);
                atomic_store_explicit(&s->given, 0, memory_order_relaxed);
                atomic_store_explicit(&b->used, 0, memory_order_relaxed);
        }
        queue_unlock(q);
        blocks_free(ty, retired);
        return *self;
}

static Value
shared_queue_close(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.close()", 0);
        SharedQueue *q = self->shared_queue;
        for (usize i = 0; i < q->nlanes; ++i) {
                TyMutexLock(&q->lanes[i].write);
        }
        atomic_store_explicit(&q->open, false, memory_order_release);
        for (usize i = q->nlanes; i != 0; --i) {
                TyMutexUnlock(&q->lanes[i - 1].write);
        }
        queue_notify(q, INT_MAX);
        return NIL;
}

static Value
shared_queue_open(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.open?()", 0);
        return BOOLEAN(atomic_load_explicit(&self->shared_queue->open, memory_order_acquire));
}

static Value
shared_queue_to_array(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.to-array()", 0);
        SharedQueue *q = self->shared_queue;
        Array *a = mAo0(sizeof *a, GC_ARRAY);
        queue_lock(q);
        usize n = queue_size_locked(q);
        while (a->capacity < n) {
                queue_unlock(q);
                uvR(*a, n);
                queue_lock(q);
                n = queue_size_locked(q);
        }
        for (usize i = 0; i < q->nlanes; ++i) {
                struct queue_lane *s = &q->lanes[i];
                struct queue_block *b = s->first;
                usize start = s->head;
                while (b != NULL) {
                        usize end = atomic_load_explicit(&b->used, memory_order_relaxed);
                        usize k = end - start;
                        if (k != 0) {
                                memcpy(a->items + a->count, b->items + start, k * sizeof (Value));
                                a->count += k;
                        }
                        start = 0;
                        b = atomic_load_explicit(&b->next, memory_order_relaxed);
                }
        }
        queue_unlock(q);
        return ARRAY(a);
}

DEFINE_METHOD_TABLE(
        shared_queue,
        { .name = "clear",    .func = shared_queue_clear      },
        { .name = "close",    .func = shared_queue_close      },
        { .name = "empty?",   .func = shared_queue_empty      },
        { .name = "len",      .func = shared_queue_len        },
        { .name = "open?",    .func = shared_queue_open       },
        { .name = "peek",     .func = shared_queue_peek       },
        { .name = "put",      .func = shared_queue_put        },
        { .name = "putAll",   .func = shared_queue_put_all    },
        { .name = "take",     .func = shared_queue_take       },
        { .name = "takeUpTo", .func = shared_queue_take_up_to },
        { .name = "toArray",  .func = shared_queue_to_array   },
        { .name = "tryPeek",  .func = shared_queue_try_peek   },
        { .name = "tryTake",  .func = shared_queue_try_take   }
);

DEFINE_METHOD_LOOKUP(shared_queue);
DEFINE_METHOD_TABLE_BUILDER(shared_queue);
DEFINE_METHOD_COMPLETER(shared_queue);
