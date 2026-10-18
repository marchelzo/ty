#include "prof.h"

#ifdef TY_HAVE_SAMPLER

#include <errno.h>
#include <mach-o/dyld.h>
#include <mach-o/loader.h>
#include <mach-o/nlist.h>
#include <mach/mach.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ucontext.h>
#include <time.h>

#include "platform.h"

typedef struct DarwinThread DarwinThread;

struct DarwinThread {
        ProfThread *pt;
        mach_port_t port;
        u64 last;
        _Atomic u64 ticks;
        bool armed;
        DarwinThread *next;
};

static pthread_mutex_t TickLock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  TickCond = PTHREAD_COND_INITIALIZER;
static DarwinThread   *Armed;
static pthread_t       Ticker;
static bool            HaveTicker;
static u64             TickPeriod;

static char const *EventNames[] = { NULL };

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

static void
Tick(void)
{
        for (DarwinThread *dt = Armed; dt != NULL; dt = dt->next) {
                u64 cpu;

                if (!ThreadCpuNs(dt->port, &cpu) || cpu < dt->last + TickPeriod) {
                        continue;
                }

                u64 n = (cpu - dt->last) / TickPeriod;

                dt->last += n * TickPeriod;
                atomic_fetch_add_explicit(&dt->ticks, n, memory_order_relaxed);
                pthread_kill(dt->pt->self, SIGPROF);
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

                next += TickPeriod;

                pthread_mutex_unlock(&TickLock);
                prof_os_sleep_until(next);
                pthread_mutex_lock(&TickLock);
        }
}

void
prof_os_init(ProfHandler *handler)
{
        struct sigaction sa = {0};

        sa.sa_sigaction = handler;
        sa.sa_flags = SA_SIGINFO | SA_RESTART;
        sigemptyset(&sa.sa_mask);
        sigaction(SIGPROF, &sa, NULL);
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
        return EventNames;
}

char const *
prof_os_event(char const *name, u64 *period)
{
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

        if (mode != PK_CPU) {
                return;
        }

        pthread_mutex_lock(&TickLock);

        dt = OsOf(pt);

        if (dt->armed) {
                goto Unlock;
        }

        dt->port = pthread_mach_thread_np(pt->self);

        if (!ThreadCpuNs(dt->port, &dt->last)) {
                goto Unlock;
        }

        TickPeriod = period;
        dt->armed  = true;
        dt->next   = Armed;
        Armed      = dt;

        atomic_store_explicit(&dt->ticks, 0, memory_order_relaxed);

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
        DarwinThread *dt = pt->os;

        if (dt != NULL) {
                u64 n = atomic_exchange_explicit(&dt->ticks, 0, memory_order_relaxed);
                if (n > 1) {
                        weight *= n;
                }
        }

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
prof_os_kick(ProfThread *pt)
{
        pthread_kill(pt->self, SIGPROF);
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

int
prof_os_attach_signal(void)
{
        return SIGUSR1;
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
