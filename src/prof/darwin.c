#include "prof.h"

#ifdef TY_HAVE_SAMPLER

#include <dispatch/dispatch.h>
#include <errno.h>
#include <libproc.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach/mach.h>
#include <notify.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ucontext.h>
#include <time.h>
#include <unistd.h>

#include "platform.h"

#ifndef PROC_PIDTHREADCOUNTS
#define PROC_PIDTHREADCOUNTS 34
#endif

#define EVENT_POLL_NS 1000000ULL

typedef struct DarwinThread DarwinThread;

struct DarwinThread {
        ProfThread   *pt;
        mach_port_t   port;
        u64           last;
        bool          armed;
        DarwinThread *next;
};

typedef struct {
        u64 instructions;
        u64 cycles;
        u64 user;
        u64 system;
        u64 energy;
} PmcLevel;

typedef struct {
        u16      n;
        u16      _0;
        u32      _1;
        PmcLevel level[8];
} Pmc;

static struct {
        char const *name;
        usize       field;
        u64         period;
} const Events[] = {
        { "cycles",       offsetof(PmcLevel, cycles),       2000000 },
        { "instructions", offsetof(PmcLevel, instructions), 4000000 },
};

static char const *EventNames[countof(Events) + 1];
static int         Event = -1;

static pthread_mutex_t TickLock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  TickCond = PTHREAD_COND_INITIALIZER;
static DarwinThread   *Armed;
static pthread_t       Ticker;
static bool            HaveTicker;
static int             TickMode;
static u64             TickEvery;
static u64             TickPoll;
static ProfRemote     *Remote;
static void          (*AttachFn)(void);

static int
SymCmp(void const *a_, void const *b_)
{
        ExeSym const *a = a_;
        ExeSym const *b = b_;
        return (a->lo > b->lo) - (a->lo < b->lo);
}

static u64
MonoNs(void)
{
        return clock_gettime_nsec_np(CLOCK_MONOTONIC);
}

static bool
ThreadCpuNs(mach_port_t port, u64 *out)
{
        thread_extended_info_data_t info;
        mach_msg_type_number_t n = THREAD_EXTENDED_INFO_COUNT;

        if (thread_info(port, THREAD_EXTENDED_INFO, (thread_info_t)&info, &n) != KERN_SUCCESS) {
                return false;
        }

        *out = info.pth_user_time + info.pth_system_time;

        return true;
}

static bool
ThreadEvents(u64 tid, u64 *out)
{
        Pmc pmc = {0};
        int n   = proc_pidinfo(getpid(), PROC_PIDTHREADCOUNTS, tid, &pmc, sizeof pmc);

        if (Event < 0 || n < (int)offsetof(Pmc, level)) {
                return false;
        }

        *out = 0;

        for (u16 i = 0; i < pmc.n && i < countof(pmc.level); ++i) {
                *out += *(u64 const *)((u8 const *)&pmc.level[i] + Events[Event].field);
        }

        return true;
}

static bool
Count(DarwinThread const *dt, u64 *out)
{
        return (TickMode == PK_CPU) ? ThreadCpuNs(dt->port, out)
             :                        ThreadEvents(dt->pt->tid, out);
}

static bool
ThreadPc(mach_port_t port, uptr *pc)
{
#if defined(__aarch64__)
        arm_thread_state64_t   ss;
        mach_msg_type_number_t n = ARM_THREAD_STATE64_COUNT;

        if (thread_get_state(port, ARM_THREAD_STATE64, (thread_state_t)&ss, &n) != KERN_SUCCESS) {
                return false;
        }

        *pc = arm_thread_state64_get_pc(ss);
#elif defined(__x86_64__)
        x86_thread_state64_t   ss;
        mach_msg_type_number_t n = x86_THREAD_STATE64_COUNT;

        if (thread_get_state(port, x86_THREAD_STATE64, (thread_state_t)&ss, &n) != KERN_SUCCESS) {
                return false;
        }

        *pc = ss.__rip;
#else
        *pc = 0;
#endif

        return true;
}

static void
Probe(ProfThread *pt, mach_port_t port, u64 weight)
{
        uptr pc;

        if (Remote == NULL || thread_suspend(port) != KERN_SUCCESS) {
                return;
        }

        if (ThreadPc(port, &pc)) {
                Remote(pt, pc, weight);
        }

        thread_resume(port);
}

static void
Tick(void)
{
        for (DarwinThread *dt = Armed; dt != NULL; dt = dt->next) {
                u64 now;

                if (!Count(dt, &now) || now < dt->last + TickEvery) {
                        continue;
                }

                u64 n = (now - dt->last) / TickEvery;

                dt->last += n * TickEvery;
                Probe(dt->pt, dt->port, n * TickEvery);
        }
}

static void *
TickLoop(void *_)
{
        u64 next = MonoNs();

        pthread_setname_np("ty-prof-tick");

        pthread_mutex_lock(&TickLock);

        for (;;) {
                while (Armed == NULL) {
                        pthread_cond_wait(&TickCond, &TickLock);
                        next = MonoNs();
                }

                Tick();

                next += TickPoll;

                pthread_mutex_unlock(&TickLock);
                prof_os_sleep_until(next);
                pthread_mutex_lock(&TickLock);
        }
}

void
prof_os_init(ProfHandler *handler, ProfRemote *remote)
{
        Remote = remote;
}

static void
ScanSegment(
        struct segment_command_64 const *seg,
        struct segment_command_64 const **linkedit,
        struct section_64 const **text
)
{
        struct section_64 const *sec = (void const *)(seg + 1);

        if (strcmp(seg->segname, SEG_LINKEDIT) == 0) {
                *linkedit = seg;
        }

        for (u32 i = 0; i < seg->nsects; ++i) {
                if (
                        (strcmp(sec[i].segname, SEG_TEXT) == 0)
                     && (strcmp(sec[i].sectname, SECT_TEXT) == 0)
                ) {
                        *text = &sec[i];
                }
        }
}

ExeSym *
prof_os_exe_symbols(usize *count)
{
        struct mach_header_64 const *mh = (void const *)_dyld_get_image_header(0);
        intptr_t slide = _dyld_get_image_vmaddr_slide(0);
        struct segment_command_64 const *linkedit = NULL;
        struct symtab_command const *symtab = NULL;
        struct section_64 const *text = NULL;
        ExeSym *syms;
        usize n = 0;

        *count = 0;

        if (mh == NULL || mh->magic != MH_MAGIC_64) {
                return NULL;
        }

        struct load_command const *lc = (void const *)(mh + 1);

        for (u32 i = 0; i < mh->ncmds; ++i) {
                switch (lc->cmd) {
                case LC_SYMTAB:
                        symtab = (void const *)lc;
                        break;

                case LC_SEGMENT_64:
                        ScanSegment((void const *)lc, &linkedit, &text);
                        break;
                }
                lc = (void const *)((u8 const *)lc + lc->cmdsize);
        }

        if (symtab == NULL || linkedit == NULL || text == NULL) {
                return NULL;
        }

        u8 const *base = (u8 const *)(linkedit->vmaddr + slide - linkedit->fileoff);
        struct nlist_64 const *nl = (void const *)(base + symtab->symoff);
        char const *str = (char const *)(base + symtab->stroff);
        uptr tlo = text->addr + slide;
        uptr thi = tlo + text->size;

        syms = malloc((symtab->nsyms + 1) * sizeof *syms);

        for (u32 i = 0; i < symtab->nsyms; ++i) {
                uptr addr = nl[i].n_value + slide;
                char const *name = str + nl[i].n_un.n_strx;

                if (
                        (nl[i].n_type & N_STAB)
                     || ((nl[i].n_type & N_TYPE) != N_SECT)
                     || (addr < tlo)
                     || (addr >= thi)
                     || (nl[i].n_un.n_strx == 0)
                ) {
                        continue;
                }

                syms[n++] = (ExeSym) {
                        .lo   = addr,
                        .hi   = 0,
                        .name = (name[0] == '_') ? name + 1 : name
                };
        }

        qsort(syms, n, sizeof *syms, SymCmp);

        usize m = 0;

        for (usize i = 0; i < n; ++i) {
                if (m > 0 && syms[m - 1].lo == syms[i].lo) {
                        continue;
                }
                syms[m++] = syms[i];
        }

        for (usize i = 0; i < m; ++i) {
                syms[i].hi = (i + 1 < m) ? syms[i + 1].lo : thi;
        }

        *count = m;

        return syms;
}

u64
prof_os_tid(void)
{
        u64 tid = 0;
        pthread_threadid_np(NULL, &tid);
        return tid;
}

char const *const *
prof_os_events(void)
{
        for (usize i = 0; i < countof(Events); ++i) {
                EventNames[i] = Events[i].name;
        }

        return EventNames;
}

char const *
prof_os_event(char const *name, u64 *period)
{
        u64 probe;

        for (usize i = 0; i < countof(Events); ++i) {
                if (strcmp(Events[i].name, name) != 0) {
                        continue;
                }

                Event = i;

                if (!ThreadEvents(prof_os_tid(), &probe)) {
                        Event = -1;
                        return NULL;
                }

                *period = Events[i].period;

                return Events[i].name;
        }

        return NULL;
}

static DarwinThread *
OsOf(ProfThread *pt)
{
        if (pt->os == NULL) {
                DarwinThread *dt = calloc(1, sizeof *dt);
                dt->pt = pt;
                pt->os = dt;
        }

        return pt->os;
}

void
prof_os_arm(ProfThread *pt, int mode, u64 period)
{
        DarwinThread *dt;

        if (mode != PK_CPU && mode != PK_EVENT) {
                return;
        }

        pthread_mutex_lock(&TickLock);

        dt = OsOf(pt);

        if (dt->armed) {
                goto Unlock;
        }

        dt->port  = pthread_mach_thread_np(pt->self);
        TickMode  = mode;
        TickEvery = period;
        TickPoll  = (mode == PK_CPU) ? period : EVENT_POLL_NS;

        if (!Count(dt, &dt->last)) {
                goto Unlock;
        }

        dt->armed = true;
        dt->next  = Armed;
        Armed     = dt;

        if (!HaveTicker) {
                HaveTicker = pthread_create(&Ticker, NULL, TickLoop, NULL) == 0;
        }

        pthread_cond_signal(&TickCond);

Unlock:
        pthread_mutex_unlock(&TickLock);
}

void
prof_os_disarm(ProfThread *pt)
{
        DarwinThread *dt = pt->os;

        if (dt == NULL) {
                return;
        }

        pthread_mutex_lock(&TickLock);

        if (dt->armed) {
                for (DarwinThread **p = &Armed; *p != NULL; p = &(*p)->next) {
                        if (*p == dt) {
                                *p = dt->next;
                                break;
                        }
                }
                dt->armed = false;
                dt->next  = NULL;
        }

        pthread_mutex_unlock(&TickLock);
}

u64
prof_os_weight(ProfThread *pt, u64 weight)
{
        return weight;
}

void
prof_os_sampled(ProfThread *pt)
{
}

uptr
prof_os_context_pc(void *uc_)
{
        ucontext_t const *uc = uc_;

        if (uc == NULL || uc->uc_mcontext == NULL) {
                return 0;
        }

#if defined(__x86_64__)
        return uc->uc_mcontext->__ss.__rip;
#elif defined(__aarch64__)
        return arm_thread_state64_get_pc(uc->uc_mcontext->__ss);
#else
        return 0;
#endif
}

void
prof_os_kick(ProfThread *pt, u64 weight)
{
        Probe(pt, pthread_mach_thread_np(pt->self), weight);
}

void
prof_os_sleep_until(u64 ns)
{
        u64 now = MonoNs();

        if (ns <= now) {
                return;
        }

        u64 d = ns - now;
        struct timespec ts = {
                .tv_sec  = d / 1000000000ULL,
                .tv_nsec = d % 1000000000ULL
        };

        while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {
                continue;
        }
}

static void
AttachName(char *buf, usize n, pid_t pid)
{
        snprintf(buf, n, "org.ty.prof-attach.%d", (int)pid);
}

static void
Listen(void *_)
{
        char name[64];
        int  token;

        AttachName(name, sizeof name, getpid());

        notify_register_dispatch(
                name,
                &token,
                dispatch_get_global_queue(QOS_CLASS_UTILITY, 0),
                ^(int _) { AttachFn(); }
        );
}

void
prof_os_attach_listen(void (*fn)(void))
{
        AttachFn = fn;
        dispatch_async_f(dispatch_get_global_queue(QOS_CLASS_UTILITY, 0), NULL, Listen);
}

int
prof_os_attach_poke(pid_t pid)
{
        char name[64];

        if (kill(pid, 0) != 0) {
                return -1;
        }

        AttachName(name, sizeof name, pid);

        if (notify_post(name) != NOTIFY_STATUS_OK) {
                errno = EIO;
                return -1;
        }

        return 0;
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
