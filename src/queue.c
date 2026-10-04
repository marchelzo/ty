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

inline static bool
full(Queue const *q)
{
        return (q->max != 0) && (queue_count((Queue *)q) == q->max);
}

static Value
queue_push(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Queue.push()", 1);

        Queue *q = self->queue;

        for (int i = 0; i < argc; ++i) {
                if (full(q)) {
                        q->head = (q->head + 1) % q->cap;
                }
                _queue_push_back_one(ty, &q->items, &q->head, &q->tail, &q->cap, ARG(i));
        }

        CheckUsed(ty);

        return *self;
}

static Value
queue_push_front(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Queue.push-front()", 1);

        Queue *q = self->queue;

        for (int i = argc - 1; i >= 0; --i) {
                if (full(q)) {
                        q->tail = (q->tail - 1 + q->cap) % q->cap;
                }
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

inline static Value *
at(Queue const *q, usize i)
{
        return &q->items[(q->head + i) % q->cap];
}

Value *
queue_index(Queue const *q, imax i)
{
        imax n = queue_count((Queue *)q);

        if (i < 0) {
                i += n;
        }

        return (i < 0 || i >= n) ? NULL : at(q, i);
}

static Value
queue_contains(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.contains?()", 1);

        Queue *q = self->queue;
        Value  x = ARG(0);

        for (usize i = 0; i < queue_count(q); ++i) {
                if (v_eq(at(q, i), &x)) {
                        return BOOLEAN(true);
                }
        }

        return BOOLEAN(false);
}

static Value
queue_rotate(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.rotate()", 0, 1);

        Queue *q = self->queue;
        imax   n = queue_count(q);
        imax   k = (argc == 1) ? INT_ARG(0) : 1;

        if (n < 2 || (k %= n) == 0) {
                return *self;
        }

        if (k < 0) {
                k += n;
        }

        if (k <= n - k) {
                while (k --> 0) {
                        q->tail = (q->tail - 1 + q->cap) % q->cap;
                        q->head = (q->head - 1 + q->cap) % q->cap;
                        q->items[q->head] = q->items[q->tail];
                }
        } else {
                for (k = n - k; k --> 0;) {
                        q->items[q->tail] = q->items[q->head];
                        q->tail = (q->tail + 1) % q->cap;
                        q->head = (q->head + 1) % q->cap;
                }
        }

        return *self;
}

static Value
queue_max_len(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.max-len()", 0);
        return (self->queue->max == 0) ? NIL : INTEGER(self->queue->max);
}

static Value
queue_empty(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.empty?()", 0);
        return BOOLEAN(queue_count(self->queue) == 0);
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
        { .name = "contains?",   .func = queue_contains      },
        { .name = "empty?",      .func = queue_empty         },
        { .name = "len",         .func = queue_len           },
        { .name = "maxLen",      .func = queue_max_len       },
        { .name = "peek",        .func = queue_peek          },
        { .name = "peekBack",    .func = queue_peek_back     },
        { .name = "pop",         .func = queue_pop           },
        { .name = "popBack",     .func = queue_pop_back      },
        { .name = "push",        .func = queue_push          },
        { .name = "pushFront",   .func = queue_push_front    },
        { .name = "rotate",      .func = queue_rotate        },
        { .name = "toArray",     .func = queue_to_array      },
        { .name = "tryPeek",     .func = queue_try_peek      },
        { .name = "tryPeekBack", .func = queue_try_peek_back },
        { .name = "tryPop",      .func = queue_try_pop       },
        { .name = "tryPopBack",  .func = queue_try_pop_back  },
);

DEFINE_METHOD_LOOKUP(queue)
DEFINE_METHOD_TABLE_BUILDER(queue)
DEFINE_METHOD_COMPLETER(queue)
