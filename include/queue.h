#ifndef QUEUE_H_INCLUDED
#define QUEUE_H_INCLUDED

#include "ty.h"
#include "gc.h"

#define QUEUE_INITIAL_CAP 8

inline static usize
_queue_count(usize head, usize tail, usize cap)
{
        if (cap == 0) return 0;
        return (tail - head + cap) % cap;
}

inline static void
_queue_grow(Ty *ty, Value **items, usize *head, usize *tail, usize *cap)
{
        usize n = _queue_count(*head, *tail, *cap);
        usize new_cap = (*cap == 0) ? QUEUE_INITIAL_CAP : (*cap * 2);

        if (*items != NULL) NOGC(*items);

        Value *new_items = mA(new_cap * sizeof (Value));

        for (usize i = 0; i < n; ++i) {
                new_items[i] = (*items)[(*head + i) % *cap];
        }

        if (*items != NULL) OKGC(*items);

        *items = new_items;
        *head = 0;
        *tail = n;
        *cap = new_cap;
}

inline static void
_queue_push_back_one(Ty *ty, Value **items, usize *head, usize *tail, usize *cap, Value v)
{
        if (*cap == 0 || (*tail + 1) % *cap == *head) {
                _queue_grow(ty, items, head, tail, cap);
        }

        (*items)[*tail] = v;
        *tail = (*tail + 1) % *cap;
}

inline static void
_queue_push_front_one(Ty *ty, Value **items, usize *head, usize *tail, usize *cap, Value v)
{
        if (*cap == 0 || (*head - 1 + *cap) % *cap == *tail) {
                _queue_grow(ty, items, head, tail, cap);
        }

        *head = (*head - 1 + *cap) % *cap;
        (*items)[*head] = v;
}

inline static Queue *
queue_new(Ty *ty)
{
        return mAo0(sizeof (Queue), GC_QUEUE);
}

inline static SharedQueue *
shared_queue_new(Ty *ty)
{
        SharedQueue *q = mAo0(sizeof (SharedQueue), GC_SHARED_QUEUE);
        TyMutexInit(&q->mutex);
        TyCondVarInit(&q->cond);
        q->open = true;
        return q;
}

void queue_mark(Ty *ty, Queue *q);
void shared_queue_mark(Ty *ty, SharedQueue *q);

void build_queue_method_table(void);
void build_shared_queue_method_table(void);

BuiltinMethod *get_queue_method(char const *);
BuiltinMethod *get_queue_method_i(int);

BuiltinMethod *get_shared_queue_method(char const *);
BuiltinMethod *get_shared_queue_method_i(int);

int queue_get_completions(Ty *ty, char const *prefix, char **out, int max);
int shared_queue_get_completions(Ty *ty, char const *prefix, char **out, int max);

inline static usize
queue_count(Queue *q)
{
        return _queue_count(q->head, q->tail, q->cap);
}

inline static usize
shared_queue_count(SharedQueue *q)
{
        TyMutexLock(&q->mutex);
        usize n = _queue_count(q->head, q->tail, q->cap);
        TyMutexUnlock(&q->mutex);
        return n;
}

#endif
