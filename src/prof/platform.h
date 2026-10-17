#ifndef PROF_PLATFORM_H_INCLUDED
#define PROF_PLATFORM_H_INCLUDED

#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>

#include "ty.h"

typedef struct {
        u64 *buf;
        u64 mask;
        _Atomic u64 head;
        _Atomic u64 tail;
} Ring;

typedef struct {
        Ty *ty;
        u64 tid;
        pthread_t self;
        u32 slot;
        void *os;
        u8 volatile *state;
        _Atomic bool live;
        sig_atomic_t volatile busy;
        Ring ring[2];
        char name[32];
} ProfThread;

typedef struct {
        uptr lo;
        uptr hi;
        char const *name;
} ExeSym;

typedef void ProfHandler(int sig, siginfo_t *si, void *uc);

void
prof_os_init(ProfHandler *handler);

ExeSym *
prof_os_exe_symbols(usize *n);

u64
prof_os_tid(void);

char const *const *
prof_os_events(void);

char const *
prof_os_event(char const *name, u64 *period);

void
prof_os_arm(ProfThread *pt, int mode, u64 period);

void
prof_os_disarm(ProfThread *pt);

u64
prof_os_weight(ProfThread *pt, u64 weight);

void
prof_os_sampled(ProfThread *pt);

uptr
prof_os_context_pc(void *uc);

void
prof_os_kick(ProfThread *pt);

void
prof_os_sleep_until(u64 ns);

int
prof_os_attach_signal(void);

#endif

/* vim: set sts=8 sw=8 expandtab: */
