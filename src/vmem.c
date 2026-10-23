#ifndef _WIN32
#include <sys/mman.h>
#include <unistd.h>
#endif

#ifdef __linux__
#include <sys/prctl.h>
#endif

#include "vmem.h"
#include "xd.h"

#ifndef _WIN32
usize
VPage(void)
{
        static usize pg;

        if (pg == 0) {
                pg = sysconf(_SC_PAGESIZE);
        }

        return pg;
}

void *
VMap(usize n)
{
        void *p = mmap(
                NULL,
                n,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
                -1,
                0
        );

        if (p == MAP_FAILED) {
                return NULL;
        }

#ifdef MADV_NOHUGEPAGE
        madvise(p, n, MADV_NOHUGEPAGE);
#endif

        return p;
}

void
VDrop(void *p, usize n)
{
        madvise(p, n, MADV_DONTNEED);
}

static void *
carve(VPool *p)
{
        char *slot;

        if (p->end == NULL) {
                p->next = VMap(p->span);
                p->end  = (p->next == NULL) ? (char *)-1 : p->next + p->span;
        }

        if (p->next != NULL && (usize)(p->end - p->next) >= p->slot) {
                slot     = p->next;
                p->next += p->slot;
        } else if ((slot = VMap(p->slot)) == NULL) {
                return NULL;
        }

        if (p->guard) {
                mprotect(slot + VPage(), VPage(), PROT_NONE);
        }

        return slot;
}

void *
VPoolTake(VPool *p)
{
        void *slot;

        TyMutexLock(&p->lock);
        slot = (vN(p->free) > 0) ? vXx(p->free) : carve(p);
        TyMutexUnlock(&p->lock);

        return slot;
}

void
VPoolPut(VPool *p, void *slot)
{
        VDrop(slot, p->slot);

        TyMutexLock(&p->lock);
        xvP(p->free, slot);
        TyMutexUnlock(&p->lock);
}

void
VNoHugePages(void)
{
#if defined(TY_RELEASE)
        mi_option_disable(mi_option_allow_large_os_pages);
#endif
#if defined(__linux__) && defined(PR_SET_THP_DISABLE)
        prctl(PR_SET_THP_DISABLE, 1, 0, 0, 0);
#endif
}
#else
usize
VPage(void)
{
        return 4096;
}

void *
VMap(usize n)
{
        return NULL;
}

void
VDrop(void *p, usize n)
{
}

void *
VPoolTake(VPool *p)
{
        return NULL;
}

void
VPoolPut(VPool *p, void *slot)
{
}

void
VNoHugePages(void)
{
}
#endif
