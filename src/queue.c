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
