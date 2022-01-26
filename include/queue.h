#ifndef QUEUE_H_INCLUDED
#define QUEUE_H_INCLUDED

#include <stddef.h>
#include <pthread.h>

#include "value.h"

typedef struct {
        enum {
                TYMSG_RESULT,
                TYMSG_CALL
        } type;
        union {
                struct value v;
                struct {
                        struct value *f;
                        struct value *args;
                        int n;
                };
        };
} Message;


typedef struct {
        size_t i;
        size_t n;
        size_t c;
        void **q;
        pthread_mutex_t m;
} MessageQueue;

void
queue_init(MessageQueue *q);

void
queue_add(MessageQueue *q, void *msg);

void *
queue_take(MessageQueue *q);

#endif
