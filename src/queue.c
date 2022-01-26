#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>

#include "gc.h"
#include "queue.h"

static void
grow(MessageQueue *q)
{
        size_t c = (q->c == 0) ? 8 : (2 * q->c);

        resize(q->q, c * sizeof *q->q);

//        n=4 c=6 i=4
//        E F A B C D
//                ^
        
        if (q->n + q->i > q->c) {
                memcpy(q->q + q->c, q->q, (q->i + q->n - q->c) * sizeof *q->q);
        }

        q->c = c;
}

void
queue_init(MessageQueue *q)
{
        q->i = 0;
        q->n = 0;
        q->c = 0;
        q->q = NULL;
        pthread_mutex_init(&q->m, NULL);
}

void
queue_add(MessageQueue *q, void *msg)
{
        pthread_mutex_lock(&q->m);

        if (q->n == q->c) {
                grow(q);
        }

        size_t i = (q->i + q->n) & (q->c - 1);

        q->q[i] = msg;
        q->n += 1;

        pthread_mutex_unlock(&q->m);
}

void *
queue_take(MessageQueue *q)
{
        pthread_mutex_lock(&q->m);

        q->n -= 1;
        q->i = (q->i + q->n) & (q->c - 1);

        void *msg = q->q[q->i];

        pthread_mutex_unlock(&q->m);

        return msg;
}

size_t
queue_count(MessageQueue *q)
{
        pthread_mutex_lock(&q->m);

        size_t n = q->n;

        pthread_mutex_unlock(&q->m);

        return n;
}
