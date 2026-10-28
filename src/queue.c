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

        queue_trace(ty, q);
}

void
queue_trace(Ty *ty, Queue *q)
{
        if (q->items == NULL) return;

        GCMarkOwned(ty, q, q->items);

        usize n = _queue_count(q->head, q->tail, q->cap);

        for (usize i = 0; i < n; ++i) {
                GCMarkPush(ty, &q->items[(q->head + i) % q->cap]);
        }
}

inline static bool
full(Queue const *q)
{
        return (q->max != 0) && (queue_count((Queue *)q) == q->max);
}

inline static void
push_one(Ty *ty, Queue *q, Value v)
{
        if (full(q)) {
                q->head = (q->head + 1) % q->cap;
        }
        _queue_push_back_one(ty, &q->items, &q->head, &q->tail, &q->cap, v);
}

inline static Value *
at(Queue const *q, usize i)
{
        return &q->items[(q->head + i) % q->cap];
}

void
queue_extend(Ty *ty, Queue *q, Value xs)
{
        Value x;

        switch (xs.type) {
        case VALUE_ARRAY:
                for (usize i = 0; i < vN(*xs.array); ++i) {
                        push_one(ty, q, v__(*xs.array, i));
                }
                break;

        case VALUE_QUEUE:
        {
                usize n = queue_count(xs.queue);
                if (xs.queue == q && full(q)) {
                        Value snap = QUEUE(QueueClone(ty, q));
                        gP(&snap);
                        queue_extend(ty, q, snap);
                        gX();
                        break;
                }
                for (usize i = 0; i < n; ++i) {
                        push_one(ty, q, *at(xs.queue, i));
                }
                break;
        }

        default:
                gP(&xs);
                vm_iter_begin(ty, xs);
                while (vm_iter_next(ty, &x)) {
                        push_one(ty, q, x);
                }
                gX();
        }

        CheckUsed(ty);
}

static Value
queue_push(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Queue.push()", 1);

        Queue *q = self->queue;

        for (int i = 0; i < argc; ++i) {
                push_one(ty, q, ARG(i));
        }

        CheckUsed(ty);

        return *self;
}

static Value
queue_extend_m(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.extend()", 1);
        queue_extend(ty, self->queue, ARG(0));
        return *self;
}

Queue *
QueueClone(Ty *ty, Queue const *q)
{
        Queue *c = queue_new(ty);
        usize  n = queue_count((Queue *)q);

        c->max = q->max;

        if (n > 0) {
                NOGC(c);
                c->cap   = n + 1;
                c->items = GCOwnedResize(ty, NULL, c->cap * sizeof (Value), 0, GC_BUF_VALUES, false);
                for (usize i = 0; i < n; ++i) {
                        c->items[i] = *at(q, i);
                }
                c->tail = n;
                OKGC(c);
        }

        return c;
}

static Value
queue_clone(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.clone()", 0);
        return QUEUE(QueueClone(ty, self->queue));
}

static Value
queue_shift(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.shift()", 0, 1);

        Queue *q = self->queue;
        usize  n = queue_count(q);

        if (argc == 0) {
                if (n == 0) {
                        bP("empty queue");
                }
                Value v = q->items[q->head];
                q->head = (q->head + 1) % q->cap;
                return v;
        }

        imax k = INT_ARG(0);

        if (k < 0) {
                bP("negative count: %"PRIiMAX, k);
        }

        k = min(k, (imax)n);

        Array *a = vAn(k);

        for (imax i = 0; i < k; ++i) {
                a->items[i] = *at(q, i);
        }
        a->count = k;

        if (k > 0) {
                q->head = (q->head + k) % q->cap;
        }

        return ARRAY(a);
}

static Value
queue_shift_while(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.shift-while()", 1);

        Queue *q = self->queue;
        Value  f = ARG(0);
        Value  out = ARRAY(vA());

        gP(&out);

        while (queue_count(q) > 0) {
                Value x = q->items[q->head];
                vmP(&x);
                Value keep = vmC(&f, 1);
                if (!value_truthy(ty, &keep)) {
                        break;
                }
                q->head = (q->head + 1) % q->cap;
                vAp(out.array, x);
        }

        gX();

        return out;
}

static Value
queue_filter_mut(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.filter!()", 1);

        Queue *q = self->queue;
        Value  f = ARG(0);
        usize  n = queue_count(q);
        usize  k = 0;

        for (usize i = 0; i < n; ++i) {
                Value x = *at(q, i);
                vmP(&x);
                Value keep = vmC(&f, 1);
                if (value_truthy(ty, &keep)) {
                        *at(q, k++) = x;
                }
        }

        if (q->cap > 0) {
                q->tail = (q->head + k) % q->cap;
        }

        return *self;
}

static Value
queue_remove(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.remove()", 1);

        Queue *q = self->queue;
        Value  x = ARG(0);
        usize  n = queue_count(q);

        for (usize i = 0; i < n; ++i) {
                if (value_test_equality(ty, at(q, i), &x)) {
                        for (usize j = i; j + 1 < n; ++j) {
                                *at(q, j) = *at(q, j + 1);
                        }
                        q->tail = (q->tail - 1 + q->cap) % q->cap;
                        return BOOLEAN(true);
                }
        }

        return BOOLEAN(false);
}

static Value
queue_reverse_mut(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Queue.reverse!()", 0);

        Queue *q = self->queue;
        usize  n = queue_count(q);

        for (usize i = 0; i < n / 2; ++i) {
                SWAP(Value, *at(q, i), *at(q, n - 1 - i));
        }

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
        { .name = "clone",       .func = queue_clone         },
        { .name = "extend",      .func = queue_extend_m      },
        { .name = "filter!",     .func = queue_filter_mut    },
        { .name = "remove",      .func = queue_remove        },
        { .name = "shift",       .func = queue_shift         },
        { .name = "shiftWhile",  .func = queue_shift_while   },
        { .name = "reverse!",    .func = queue_reverse_mut   },
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
