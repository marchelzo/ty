#ifndef PTHREAD_BARRIER_H
#define PTHREAD_BARRIER_H

#include <pthread.h>

#ifdef __APPLE__

#ifdef __cplusplus
extern "C" {
#endif

#if !defined(PTHREAD_BARRIER_SERIAL_THREAD)
# define PTHREAD_BARRIER_SERIAL_THREAD  (1)
#endif

#if !defined(PTHREAD_PROCESS_PRIVATE)
# define PTHREAD_PROCESS_PRIVATE    (42)
#endif
#if !defined(PTHREAD_PROCESS_SHARED)
# define PTHREAD_PROCESS_SHARED     (43)
#endif

typedef struct {
} pthread_barrierattr_t;

typedef struct {
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    unsigned int limit;
    unsigned int count;
    unsigned int phase;
} pthread_barrier_t;

int pthread_barrierattr_init(pthread_barrierattr_t *attr);
int pthread_barrierattr_destroy(pthread_barrierattr_t *attr);

int pthread_barrierattr_getpshared(const pthread_barrierattr_t *restrict attr,
                   int *restrict pshared);
int pthread_barrierattr_setpshared(pthread_barrierattr_t *attr,
                   int pshared);

int pthread_barrier_init(pthread_barrier_t *restrict barrier,
             const pthread_barrierattr_t *restrict attr,
             unsigned int count);
int pthread_barrier_destroy(pthread_barrier_t *barrier);

int pthread_barrier_wait(pthread_barrier_t *barrier);

#ifdef  __cplusplus
}
#endif


#include <errno.h>

#define __unused __attribute__((unused))

int
pthread_barrierattr_init(pthread_barrierattr_t *attr __unused)
{
    return 0;
}

int
pthread_barrierattr_destroy(pthread_barrierattr_t *attr __unused)
{
    return 0;
}

int
pthread_barrierattr_getpshared(const pthread_barrierattr_t *restrict attr __unused,
                   int *restrict pshared)
{
    *pshared = PTHREAD_PROCESS_PRIVATE;
    return 0;
}

int
pthread_barrierattr_setpshared(pthread_barrierattr_t *attr __unused,
                   int pshared)
{
    if (pshared != PTHREAD_PROCESS_PRIVATE) {
        errno = EINVAL;
        return -1;
    }
    return 0;
}

int
pthread_barrier_init(pthread_barrier_t *restrict barrier,
             const pthread_barrierattr_t *restrict attr __unused,
             unsigned count)
{
    if (count == 0) {
        errno = EINVAL;
        return -1;
    }

    if (pthread_mutex_init(&barrier->mutex, 0) < 0) {
        return -1;
    }
    if (pthread_cond_init(&barrier->cond, 0) < 0) {
        int errno_save = errno;
        pthread_mutex_destroy(&barrier->mutex);
        errno = errno_save;
        return -1;
    }

    barrier->limit = count;
    barrier->count = 0;
    barrier->phase = 0;

    return 0;
}

int
pthread_barrier_destroy(pthread_barrier_t *barrier)
{
    pthread_mutex_destroy(&barrier->mutex);
    pthread_cond_destroy(&barrier->cond);
    return 0;
}

int
pthread_barrier_wait(pthread_barrier_t *barrier)
{
    pthread_mutex_lock(&barrier->mutex);
    barrier->count++;
    if (barrier->count >= barrier->limit) {
        barrier->phase++;
        barrier->count = 0;
        pthread_cond_broadcast(&barrier->cond);
        pthread_mutex_unlock(&barrier->mutex);
        return PTHREAD_BARRIER_SERIAL_THREAD;
    } else {
        unsigned phase = barrier->phase;
        do
            pthread_cond_wait(&barrier->cond, &barrier->mutex);
        while (phase == barrier->phase);
        pthread_mutex_unlock(&barrier->mutex);
        return 0;
    }
}

#endif /* __APPLE__ */

#endif /* PTHREAD_BARRIER_H */
