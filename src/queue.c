#include "ty.h"
#include "queue.h"
#include "value.h"
#include "vm.h"
#include "gc.h"
#include "xd.h"
#include "mmmm.h"

/*================================================================
                            Queue
================================================================*/

void
queue_mark(Ty *ty, Queue *q)
{
        if (MARKED(q)) return;

        MARK(q);

        if (q->items == NULL) return;

        MARK(q->items);

        usize n = _queue_count(q->head, q->tail, q->cap);

        for (usize i = 0; i < n; ++i) {
                xvP(ty->marking, &q->items[(q->head + i) % q->cap]);
        }
}

static Value
queue_push(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Queue.push()", 1, INT_MAX);

        Queue *q = self->queue;

        for (int i = 0; i < argc; ++i) {
                _queue_push_back_one(ty, &q->items, &q->head, &q->tail, &q->cap, ARG(i));
        }

        CheckUsed(ty);

        return *self;
}

static Value
queue_push_front(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_RANGE("Queue.push-front()", 1, INT_MAX);

        Queue *q = self->queue;

        for (int i = argc - 1; i >= 0; --i) {
                _queue_push_front_one(ty, &q->items, &q->head, &q->tail, &q->cap, ARG(i));
        }

        CheckUsed(ty);

        return *self;
}

static Value
queue_pop(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.pop()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                bP("empty queue");
        }

        Value v = q->items[q->head];
        q->head = (q->head + 1) % q->cap;

        return v;
}

static Value
queue_pop_back(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.pop-back()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                bP("empty queue");
        }

        q->tail = (q->tail - 1 + q->cap) % q->cap;

        return q->items[q->tail];
}

static Value
queue_try_pop(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.try-pop()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                return None;
        }

        Value v = q->items[q->head];
        q->head = (q->head + 1) % q->cap;

        return Some(v);
}

static Value
queue_try_pop_back(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.try-pop-back()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                return None;
        }

        q->tail = (q->tail - 1 + q->cap) % q->cap;

        return Some(q->items[q->tail]);
}

static Value
queue_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.peek()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                bP("empty queue");
        }

        return q->items[q->head];
}

static Value
queue_peek_back(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.peek-back()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                bP("empty queue");
        }

        return q->items[(q->tail - 1 + q->cap) % q->cap];
}

static Value
queue_try_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.try-peek()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                return None;
        }

        return Some(q->items[q->head]);
}

static Value
queue_try_peek_back(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.try-peek-back()", 0);

        Queue *q = self->queue;

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                return None;
        }

        return Some(q->items[(q->tail - 1 + q->cap) % q->cap]);
}

static Value
queue_len(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.len()", 0);
        return INTEGER(_queue_count(self->queue->head, self->queue->tail, self->queue->cap));
}

static Value
queue_empty(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.empty?()", 0);
        return BOOLEAN(_queue_count(self->queue->head, self->queue->tail, self->queue->cap) == 0);
}

static Value
queue_clear(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.clear()", 0);

        self->queue->head = 0;
        self->queue->tail = 0;

        return *self;
}

static Value
queue_to_array(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.to-array()", 0);

        Queue *q = self->queue;
        usize n = _queue_count(q->head, q->tail, q->cap);

        Array *a = vAn(n);

        for (usize i = 0; i < n; ++i) {
                a->items[i] = q->items[(q->head + i) % q->cap];
        }
        a->count = n;

        return ARRAY(a);
}

DEFINE_METHOD_TABLE(
        queue,
        { .name = "clear",       .func = queue_clear         },
        { .name = "empty?",      .func = queue_empty         },
        { .name = "len",         .func = queue_len           },
        { .name = "peek",        .func = queue_peek          },
        { .name = "peekBack",    .func = queue_peek_back     },
        { .name = "pop",         .func = queue_pop           },
        { .name = "popBack",     .func = queue_pop_back      },
        { .name = "push",        .func = queue_push          },
        { .name = "pushFront",   .func = queue_push_front    },
        { .name = "toArray",     .func = queue_to_array      },
        { .name = "tryPeek",     .func = queue_try_peek      },
        { .name = "tryPeekBack", .func = queue_try_peek_back },
        { .name = "tryPop",      .func = queue_try_pop       },
        { .name = "tryPopBack",  .func = queue_try_pop_back  },
);

DEFINE_METHOD_LOOKUP(queue)
DEFINE_METHOD_TABLE_BUILDER(queue)
DEFINE_METHOD_COMPLETER(queue)


/*================================================================
                        SharedQueue
================================================================*/

void
shared_queue_mark(Ty *ty, SharedQueue *q)
{
        if (MARKED(q)) {
                return;
        }

        MARK(q);

        if (q->items == NULL) {
                return;
        }

        MARK(q->items);

        usize n = _queue_count(q->head, q->tail, q->cap);

        for (usize i = 0; i < n; ++i) {
                xvP(ty->marking, &q->items[(q->head + i) % q->cap]);
        }
}

static Value
shared_queue_put(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.put()", 1);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);
        _queue_push_back_one(ty, &q->items, &q->head, &q->tail, &q->cap, ARG(0));
        TyMutexUnlock(&q->mutex);

        TyCondVarSignal(&q->cond);
        CheckUsed(ty);

        return *self;
}

static Value
shared_queue_take(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.take()", 0);

        SharedQueue *q = self->shared_queue;

        UnlockTy();
        TyMutexLock(&q->mutex);

        while (_queue_count(q->head, q->tail, q->cap) == 0) {
                if (!q->open) {
                        TyMutexUnlock(&q->mutex);
                        LockTy();
                        CanceledError("queue is closed and empty");
                }
                TyCondVarWait(&q->cond, &q->mutex);
        }

        LockTy();

        Value v = q->items[q->head];
        q->head = (q->head + 1) % q->cap;

        TyMutexUnlock(&q->mutex);

        return v;
}

static Value
shared_queue_try_take(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.tryTake()", 0, 1);

        SharedQueue *q = self->shared_queue;

        if (argc == 1) {
                u64 timeout = TIMEOUT_ARG(0);
                UnlockTy();
                TyMutexLock(&q->mutex);
                while (_queue_count(q->head, q->tail, q->cap) == 0) {
                        if (!q->open) break;
                        if (!TyCondVarTimedWaitRelative(&q->cond, &q->mutex, timeout)) {
                                break;
                        }
                }
                LockTy();
        } else {
                TyMutexLock(&q->mutex);
        }

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                TyMutexUnlock(&q->mutex);
                return None;
        }

        Value v = q->items[q->head];
        q->head = (q->head + 1) % q->cap;

        TyMutexUnlock(&q->mutex);

        return Some(v);
}

static Value
shared_queue_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.peek()", 0);

        SharedQueue *q = self->shared_queue;

        UnlockTy();
        TyMutexLock(&q->mutex);

        while (_queue_count(q->head, q->tail, q->cap) == 0) {
                if (!q->open) {
                        TyMutexUnlock(&q->mutex);
                        LockTy();
                        CanceledError("queue is closed and empty");
                }
                TyCondVarWait(&q->cond, &q->mutex);
        }

        LockTy();

        Value v = q->items[q->head];

        TyMutexUnlock(&q->mutex);

        return v;
}

static Value
shared_queue_try_peek(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.try-peek()", 0);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);

        if (_queue_count(q->head, q->tail, q->cap) == 0) {
                TyMutexUnlock(&q->mutex);
                return None;
        }

        Value v = q->items[q->head];

        TyMutexUnlock(&q->mutex);

        return Some(v);
}

static Value
shared_queue_len(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.len()", 0);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);
        usize n = _queue_count(q->head, q->tail, q->cap);
        TyMutexUnlock(&q->mutex);

        return INTEGER(n);
}

static Value
shared_queue_empty(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.empty?()", 0);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);
        bool empty = (_queue_count(q->head, q->tail, q->cap) == 0);
        TyMutexUnlock(&q->mutex);

        return BOOLEAN(empty);
}

static Value
shared_queue_clear(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.clear()", 0);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);
        q->head = 0;
        q->tail = 0;
        TyMutexUnlock(&q->mutex);

        return *self;
}

static Value
shared_queue_close(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.close()", 0);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);
        q->open = false;
        TyMutexUnlock(&q->mutex);

        TyCondVarBroadcast(&q->cond);

        return NIL;
}

static Value
shared_queue_open(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.open?()", 0);

        SharedQueue *q = self->shared_queue;

        TyMutexLock(&q->mutex);
        bool open = q->open;
        TyMutexUnlock(&q->mutex);

        return BOOLEAN(open);
}

static Value
shared_queue_to_array(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("SharedQueue.to-array()", 0);

        SharedQueue *q = self->shared_queue;
        Array *a = mAo0(sizeof (Array), GC_ARRAY);

        TyMutexLock(&q->mutex);
        usize n = _queue_count(q->head, q->tail, q->cap);
        for (usize i = 0; i < n; ++i) {
                uvP(*a, q->items[(q->head + i) % q->cap]);
        }
        TyMutexUnlock(&q->mutex);

        return ARRAY(a);
}

DEFINE_METHOD_TABLE(
        shared_queue,
        { .name = "clear",   .func = shared_queue_clear    },
        { .name = "close",   .func = shared_queue_close    },
        { .name = "empty?",  .func = shared_queue_empty    },
        { .name = "len",     .func = shared_queue_len      },
        { .name = "open?",   .func = shared_queue_open     },
        { .name = "peek",    .func = shared_queue_peek     },
        { .name = "put",     .func = shared_queue_put      },
        { .name = "take",    .func = shared_queue_take     },
        { .name = "toArray", .func = shared_queue_to_array },
        { .name = "tryPeek", .func = shared_queue_try_peek },
        { .name = "tryTake", .func = shared_queue_try_take },
);

DEFINE_METHOD_LOOKUP(shared_queue);
DEFINE_METHOD_TABLE_BUILDER(shared_queue);
DEFINE_METHOD_COMPLETER(shared_queue);
