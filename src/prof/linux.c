#include "prof.h"

#ifdef TY_HAVE_SAMPLER

#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <link.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>
#include <linux/perf_event.h>

#include "platform.h"

#ifndef sigev_notify_thread_id
#define sigev_notify_thread_id _sigev_un._tid
#endif

typedef struct {
        timer_t timer;
        bool has_timer;
        int perf_fd;
} LinuxThread;

static struct {
        char const *name;
        u32 type;
        u64 config;
        u64 period;
} const Events[] = {
        { "cycles",           PERF_TYPE_HARDWARE, PERF_COUNT_HW_CPU_CYCLES,          2000000 },
        { "instructions",     PERF_TYPE_HARDWARE, PERF_COUNT_HW_INSTRUCTIONS,        4000000 },
        { "cache-misses",     PERF_TYPE_HARDWARE, PERF_COUNT_HW_CACHE_MISSES,          10007 },
        { "cache-references", PERF_TYPE_HARDWARE, PERF_COUNT_HW_CACHE_REFERENCES,     100003 },
        { "branch-misses",    PERF_TYPE_HARDWARE, PERF_COUNT_HW_BRANCH_MISSES,         10007 },
        { "branches",         PERF_TYPE_HARDWARE, PERF_COUNT_HW_BRANCH_INSTRUCTIONS,  1000003 },
        { "stalled-cycles",   PERF_TYPE_HARDWARE, PERF_COUNT_HW_STALLED_CYCLES_BACKEND, 1000003 },
        { "page-faults",      PERF_TYPE_SOFTWARE, PERF_COUNT_SW_PAGE_FAULTS,               1 },
        { "context-switches", PERF_TYPE_SOFTWARE, PERF_COUNT_SW_CONTEXT_SWITCHES,          1 },
        { "cpu-migrations",   PERF_TYPE_SOFTWARE, PERF_COUNT_SW_CPU_MIGRATIONS,            1 },
        { "task-clock",       PERF_TYPE_SOFTWARE, PERF_COUNT_SW_TASK_CLOCK,          1000000 },
};

static char const *EventNames[countof(Events) + 1];
static int Event = -1;

static int
SymCmp(void const *a_, void const *b_)
{
        ExeSym const *a = a_;
        ExeSym const *b = b_;
        return (a->lo > b->lo) - (a->lo < b->lo);
}

static int
FindBias(struct dl_phdr_info *info, usize size, void *data)
{
        *(uptr *)data = info->dlpi_addr;
        return 1;
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

ExeSym *
prof_os_exe_symbols(usize *count)
{
        int fd = open("/proc/self/exe", O_RDONLY | O_CLOEXEC);
        struct stat st;
        ExeSym *syms = NULL;
        usize n = 0;

        *count = 0;

        if (fd < 0) {
                return NULL;
        }

        if (fstat(fd, &st) != 0 || st.st_size < (off_t)sizeof (Elf64_Ehdr)) {
                close(fd);
                return NULL;
        }

        u8 const *img = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
        close(fd);

        if (img == MAP_FAILED) {
                return NULL;
        }

        uptr bias = 0;
        dl_iterate_phdr(FindBias, &bias);

        Elf64_Ehdr const *eh = (void const *)img;
        Elf64_Shdr const *sh = (void const *)(img + eh->e_shoff);

        if (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0 || eh->e_shoff == 0) {
                return NULL;
        }

        for (int i = 0; i < eh->e_shnum; ++i) {
                if (sh[i].sh_type != SHT_SYMTAB) {
                        continue;
                }

                Elf64_Sym const *sym = (void const *)(img + sh[i].sh_offset);
                char const *str = (char const *)(img + sh[sh[i].sh_link].sh_offset);
                usize m = sh[i].sh_size / sizeof *sym;

                syms = realloc(syms, (n + m) * sizeof *syms);

                for (usize j = 0; j < m; ++j) {
                        if (
                                (ELF64_ST_TYPE(sym[j].st_info) != STT_FUNC)
                             || (sym[j].st_size == 0)
                             || (sym[j].st_value == 0)
                        ) {
                                continue;
                        }
                        syms[n++] = (ExeSym) {
                                .lo   = bias + sym[j].st_value,
                                .hi   = bias + sym[j].st_value + sym[j].st_size,
                                .name = str + sym[j].st_name
                        };
                }
        }

        qsort(syms, n, sizeof *syms, SymCmp);

        *count = n;

        return syms;
}

u64
prof_os_tid(void)
{
        return (u64)syscall(SYS_gettid);
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
        for (usize i = 0; i < countof(Events); ++i) {
                if (strcmp(Events[i].name, name) == 0) {
                        Event = i;
                        *period = Events[i].period;
                        return Events[i].name;
                }
        }

        return NULL;
}

static LinuxThread *
OsOf(ProfThread *pt)
{
        if (pt->os == NULL) {
                LinuxThread *lt = calloc(1, sizeof *lt);
                lt->perf_fd = -1;
                pt->os = lt;
        }

        return pt->os;
}

static int
OpenPerf(ProfThread *pt, u32 type, u64 config, u64 period, bool kernel)
{
        struct perf_event_attr a = {0};
        int fd;

        a.size           = sizeof a;
        a.type           = type;
        a.config         = config;
        a.sample_period  = period;
        a.disabled       = 1;
        a.exclude_kernel = !kernel;
        a.exclude_hv     = 1;
        a.wakeup_events  = 1;

        fd = syscall(SYS_perf_event_open, &a, (pid_t)pt->tid, -1, -1, PERF_FLAG_FD_CLOEXEC);

        if (fd < 0) {
                a.exclude_kernel = 1;
                a.exclude_guest  = 1;
                fd = syscall(SYS_perf_event_open, &a, (pid_t)pt->tid, -1, -1, PERF_FLAG_FD_CLOEXEC);
        }

        return fd;
}

static void
StartPerf(ProfThread *pt, int fd)
{
        struct f_owner_ex owner = { .type = F_OWNER_TID, .pid = (pid_t)pt->tid };

        fcntl(fd, F_SETFL, O_ASYNC);
        fcntl(fd, F_SETSIG, SIGPROF);
        fcntl(fd, F_SETOWN_EX, &owner);

        OsOf(pt)->perf_fd = fd;

        ioctl(fd, PERF_EVENT_IOC_RESET, 0);
        ioctl(fd, PERF_EVENT_IOC_REFRESH, 1);
}

static void
ArmTimer(ProfThread *pt, u64 period)
{
        LinuxThread *lt = OsOf(pt);
        struct sigevent sev = {0};
        clockid_t clock;
        int fd;

        fd = OpenPerf(pt, PERF_TYPE_SOFTWARE, PERF_COUNT_SW_TASK_CLOCK, period, true);

        if (fd >= 0) {
                StartPerf(pt, fd);
                return;
        }

        sev.sigev_notify = SIGEV_THREAD_ID;
        sev.sigev_signo = SIGPROF;
        sev.sigev_notify_thread_id = (pid_t)pt->tid;

        if (pthread_getcpuclockid(pt->self, &clock) != 0) {
                clock = CLOCK_THREAD_CPUTIME_ID;
        }

        if (timer_create(clock, &sev, &lt->timer) == 0) {
                struct itimerspec its = {
                        .it_interval = { period / 1000000000ULL, period % 1000000000ULL },
                        .it_value    = { period / 1000000000ULL, period % 1000000000ULL }
                };
                timer_settime(lt->timer, 0, &its, NULL);
                lt->has_timer = true;
        }
}

static void
ArmEvent(ProfThread *pt, u64 period)
{
        int fd;

        if (Event < 0) {
                return;
        }

        fd = OpenPerf(pt, Events[Event].type, Events[Event].config, period, false);

        if (fd < 0) {
                fprintf(
                        stderr,
                        "ty: perf_event_open(%s): %s (check /proc/sys/kernel/perf_event_paranoid)\n",
                        Events[Event].name,
                        strerror(errno)
                );
                exit(1);
        }

        StartPerf(pt, fd);
}

void
prof_os_arm(ProfThread *pt, int mode, u64 period)
{
        switch (mode) {
        case PK_CPU:   ArmTimer(pt, period); break;
        case PK_EVENT: ArmEvent(pt, period); break;
        }
}

void
prof_os_disarm(ProfThread *pt)
{
        LinuxThread *lt = pt->os;

        if (lt == NULL) {
                return;
        }

        if (lt->has_timer) {
                timer_delete(lt->timer);
                lt->has_timer = false;
        }

        if (lt->perf_fd >= 0) {
                ioctl(lt->perf_fd, PERF_EVENT_IOC_DISABLE, 0);
                close(lt->perf_fd);
                lt->perf_fd = -1;
        }
}

u64
prof_os_weight(ProfThread *pt, u64 weight)
{
        LinuxThread *lt = pt->os;

        if (lt != NULL && lt->has_timer) {
                int over = timer_getoverrun(lt->timer);
                if (over > 0) {
                        weight *= (u64)over + 1;
                }
        }

        return weight;
}

void
prof_os_sampled(ProfThread *pt)
{
        LinuxThread *lt = pt->os;

        if (lt != NULL && lt->perf_fd >= 0) {
                ioctl(lt->perf_fd, PERF_EVENT_IOC_REFRESH, 1);
        }
}

uptr
prof_os_context_pc(void *uc_)
{
        ucontext_t const *uc = uc_;

        if (uc == NULL) {
                return 0;
        }

#if defined(__x86_64__)
        return uc->uc_mcontext.gregs[REG_RIP];
#elif defined(__aarch64__)
        return uc->uc_mcontext.pc;
#else
        return 0;
#endif
}

void
prof_os_kick(ProfThread *pt)
{
        syscall(SYS_tgkill, getpid(), (pid_t)pt->tid, SIGPROF);
}

void
prof_os_sleep_until(u64 ns)
{
        struct timespec ts = {
                .tv_sec  = ns / 1000000000ULL,
                .tv_nsec = ns % 1000000000ULL
        };

        clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &ts, NULL);
}

int
prof_os_attach_signal(void)
{
        return SIGRTMIN + 7;
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
