#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <netinet/in.h>
#include <sys/socket.h>

#if defined(__linux__)
#include <linux/io_uring.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#else
#include <sys/event.h>
#endif

#include "http.h"
#include "vm.h"
#include "functions.h"
#include "dict.h"

enum {
        U_RECV = 1,
        U_SEND,
        U_ACCEPT,
        U_WAKE,
        U_WATCH,
        U_IGNORE
};

enum {
        TAG_WAKE   = 0xFFFFFFFF,
        TAG_LISTEN = 0xFFFFFFFE,
        TAG_WATCH  = 1u << 31
};

enum {
        BATCH = 256
};

#define UD(op, gen, slot) (((u64)(op) << 56) | ((u64)((gen) & 0xFFFFFF) << 32) | (u32)(slot))
#define UD_OP(u)          ((int)((u) >> 56))
#define UD_GEN(u)         ((u32)(((u) >> 32) & 0xFFFFFF))
#define UD_SLOT(u)        ((u32)(u))

static _Thread_local struct sockaddr_storage AcceptAddr;
static _Thread_local socklen_t               AcceptLen;

static void
nonblocking(int fd)
{
        fcntl(fd, F_SETFL, fcntl(fd, F_GETFL) | O_NONBLOCK);
#if defined(__APPLE__)
        int one = 1;
        setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
#endif
}

static void
queue(Loop *L, u32 slot, u32 gen, int op, i64 res)
{
        xvP(L->ready, ((Done) { .slot = slot, .gen = gen, .op = op, .res = res }));
}

static Conn *
conn_of(Loop *L, u32 slot, u32 gen)
{
        if (slot >= vN(L->conns)) {
                return NULL;
        }

        Conn *c = v__(L->conns, slot);

        return (c != NULL && (c->gen & 0xFFFFFF) == (gen & 0xFFFFFF) && c->fd >= 0) ? c : NULL;
}

static void
deliver(Loop *L)
{
        for (usize i = 0; i < vN(L->ready); ++i) {
                Done d = v__(L->ready, i);
                switch (d.op) {
                case U_ACCEPT:
                        OnAccept(L, d.res);
                        break;

                case U_WATCH:
                        OnWatch(L, d.slot, d.gen, d.res);
                        break;

                case U_RECV:
                case U_SEND:;
                        Conn *c = conn_of(L, d.slot, d.gen);
                        if (c != NULL) {
                                ((d.op == U_RECV) ? OnRecv : OnSent)(L, c, d.res);
                        }
                        break;
                }
        }

        v0(L->ready);
}

static void
format_peer(Conn *c, struct sockaddr const *sa)
{
        char ip[INET6_ADDRSTRLEN] = "";
        int port = 0;

        switch (sa->sa_family) {
        case AF_INET:
                inet_ntop(AF_INET, &((struct sockaddr_in const *)sa)->sin_addr, ip, sizeof ip);
                port = ntohs(((struct sockaddr_in const *)sa)->sin_port);
                c->npeer = ty_snprintf(c->peer, sizeof c->peer, "%s:%d", ip, port);
                break;

        case AF_INET6:
                inet_ntop(AF_INET6, &((struct sockaddr_in6 const *)sa)->sin6_addr, ip, sizeof ip);
                port = ntohs(((struct sockaddr_in6 const *)sa)->sin6_port);
                c->npeer = ty_snprintf(c->peer, sizeof c->peer, "[%s]:%d", ip, port);
                break;

        default:
                c->npeer = 0;
        }
}

void
IoPeer(Conn *c)
{
        format_peer(c, (struct sockaddr const *)&AcceptAddr);
}

static i64
do_recv(Conn *c, char *p, usize n)
{
        for (;;) {
                isize k = recv(c->fd, p, n, 0);
                if (k >= 0) {
                        return k;
                }
                if (errno == EINTR) {
                        continue;
                }
                return -errno;
        }
}

static i64
do_send(Conn *c, char const *p, usize n)
{
        for (;;) {
                isize k = send(c->fd, p, n, HTTP_SEND_FLAGS);
                if (k >= 0) {
                        return k;
                }
                if (errno == EINTR) {
                        continue;
                }
                return -errno;
        }
}

static i64
do_accept(int lfd)
{
        AcceptLen = sizeof AcceptAddr;

        for (;;) {
#if defined(__APPLE__)
                int fd = accept(lfd, (struct sockaddr *)&AcceptAddr, &AcceptLen);
                if (fd >= 0) {
                        nonblocking(fd);
                        fcntl(fd, F_SETFD, FD_CLOEXEC);
                        return fd;
                }
#else
                int fd = accept4(lfd, (struct sockaddr *)&AcceptAddr, &AcceptLen, SOCK_NONBLOCK | SOCK_CLOEXEC);
                if (fd >= 0) {
                        return fd;
                }
#endif
                if (errno == EINTR) {
                        continue;
                }
                return -errno;
        }
}

static void
try_recv(Loop *L, Conn *c)
{
        i64 r = do_recv(c, c->rp, c->rn);

        if (r == -EAGAIN || r == -EWOULDBLOCK) {
                c->rready = false;
                return;
        }

        c->rp = NULL;
        queue(L, c->slot, c->gen, U_RECV, r);
}

static void
try_send(Loop *L, Conn *c)
{
        i64 r = do_send(c, c->sp, c->sn);

        if (r == -EAGAIN || r == -EWOULDBLOCK) {
                c->wready = false;
                return;
        }

        c->sp = NULL;
        queue(L, c->slot, c->gen, U_SEND, r);
}

static void
try_accept(Loop *L)
{
        for (int i = 0; i < 64 && L->accepting; ++i) {
                i64 fd = do_accept(L->g->lfd);
                if (fd == -EAGAIN || fd == -EWOULDBLOCK) {
                        return;
                }
                OnAccept(L, fd);
                deliver(L);
        }
}

#if defined(__linux__)
struct ring {
        int                  fd;
        u32                  entries;
        u32                 *sq_head;
        u32                 *sq_tail;
        u32                 *sq_mask;
        u32                 *sq_array;
        struct io_uring_sqe *sqes;
        u32                 *cq_head;
        u32                 *cq_tail;
        u32                 *cq_mask;
        struct io_uring_cqe *cqes;
        void                *sq_ptr;
        void                *cq_ptr;
        usize                sq_sz;
        usize                cq_sz;
        usize                sqe_sz;
        u32                  tail;
        u32                  queued;
};

static int
uring_setup(u32 entries, struct io_uring_params *p)
{
        return syscall(__NR_io_uring_setup, entries, p);
}

static int
uring_enter(int fd, u32 submit, u32 wait, u32 flags, void *arg, usize sz)
{
        return syscall(__NR_io_uring_enter, fd, submit, wait, flags, arg, sz);
}

static void
ring_free(Ring *r)
{
        if (r->sqes != NULL && r->sqes != MAP_FAILED) {
                munmap(r->sqes, r->sqe_sz);
        }
        if (r->cq_ptr != NULL && r->cq_ptr != r->sq_ptr && r->cq_ptr != MAP_FAILED) {
                munmap(r->cq_ptr, r->cq_sz);
        }
        if (r->sq_ptr != NULL && r->sq_ptr != MAP_FAILED) {
                munmap(r->sq_ptr, r->sq_sz);
        }
        if (r->fd >= 0) {
                close(r->fd);
        }
        xmF(r);
}

static Ring *
ring_new(u32 entries)
{
        struct io_uring_params p = {0};
        u32 const want = IORING_SETUP_CQSIZE | IORING_SETUP_SUBMIT_ALL | IORING_SETUP_COOP_TASKRUN | IORING_SETUP_SINGLE_ISSUER;

        p.flags      = want;
        p.cq_entries = entries * 4;

        int fd = uring_setup(entries, &p);

        if (fd < 0 && errno == EINVAL) {
                p = (struct io_uring_params) { .flags = IORING_SETUP_CQSIZE, .cq_entries = entries * 4 };
                fd = uring_setup(entries, &p);
        }

        if (fd < 0) {
                return NULL;
        }

        Ring *r = xmA(sizeof *r);
        *r = (Ring) { .fd = fd, .entries = p.sq_entries };

        if (
                !(p.features & IORING_FEAT_SINGLE_MMAP)
             || !(p.features & IORING_FEAT_EXT_ARG)
             || !(p.features & IORING_FEAT_NODROP)
        ) {
                ring_free(r);
                errno = ENOSYS;
                return NULL;
        }

        r->sq_sz  = p.sq_off.array + p.sq_entries * sizeof (u32);
        r->cq_sz  = p.cq_off.cqes + p.cq_entries * sizeof (struct io_uring_cqe);
        r->sq_sz  = max(r->sq_sz, r->cq_sz);
        r->sqe_sz = p.sq_entries * sizeof (struct io_uring_sqe);

        r->sq_ptr = mmap(NULL, r->sq_sz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fd, IORING_OFF_SQ_RING);
        r->cq_ptr = r->sq_ptr;
        r->sqes   = mmap(NULL, r->sqe_sz, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, fd, IORING_OFF_SQES);

        if (r->sq_ptr == MAP_FAILED || r->sqes == MAP_FAILED) {
                ring_free(r);
                return NULL;
        }

        char *sq = r->sq_ptr;
        char *cq = r->cq_ptr;

        r->sq_head  = (u32 *)(sq + p.sq_off.head);
        r->sq_tail  = (u32 *)(sq + p.sq_off.tail);
        r->sq_mask  = (u32 *)(sq + p.sq_off.ring_mask);
        r->sq_array = (u32 *)(sq + p.sq_off.array);
        r->cq_head  = (u32 *)(cq + p.cq_off.head);
        r->cq_tail  = (u32 *)(cq + p.cq_off.tail);
        r->cq_mask  = (u32 *)(cq + p.cq_off.ring_mask);
        r->cqes     = (struct io_uring_cqe *)(cq + p.cq_off.cqes);
        r->tail     = *r->sq_tail;

        return r;
}

static int
ring_submit(Ring *r, u32 wait, i64 ms)
{
        struct __kernel_timespec ts;
        struct io_uring_getevents_arg arg = { .sigmask_sz = _NSIG / 8 };
        u32 flags = IORING_ENTER_EXT_ARG;

        if (wait > 0) {
                flags |= IORING_ENTER_GETEVENTS;
                if (ms >= 0) {
                        ts.tv_sec  = ms / 1000;
                        ts.tv_nsec = (ms % 1000) * 1000000;
                        arg.ts     = (u64)(uptr)&ts;
                }
        }

        atomic_store_explicit((_Atomic u32 *)r->sq_tail, r->tail, memory_order_release);

        u32 n = r->queued;
        int rc;

        do {
                rc = uring_enter(r->fd, n, wait, flags, &arg, sizeof arg);
        } while (rc < 0 && errno == EINTR && wait == 0);

        if (rc >= 0) {
                r->queued -= min((u32)rc, r->queued);
        } else if (errno == ETIME || errno == EINTR || errno == EBUSY) {
                rc = 0;
        }

        return rc;
}

static struct io_uring_sqe *
ring_sqe(Ring *r)
{
        u32 head = atomic_load_explicit((_Atomic u32 *)r->sq_head, memory_order_acquire);

        if (r->tail - head >= r->entries) {
                ring_submit(r, 0, 0);
                head = atomic_load_explicit((_Atomic u32 *)r->sq_head, memory_order_acquire);
                if (r->tail - head >= r->entries) {
                        return NULL;
                }
        }

        u32 i = r->tail & *r->sq_mask;
        struct io_uring_sqe *sqe = &r->sqes[i];

        memset(sqe, 0, sizeof *sqe);
        r->sq_array[i] = i;
        r->tail += 1;
        r->queued += 1;

        return sqe;
}

static void
uring_prep(Loop *L, int op, int fd, void const *p, u32 n, u64 off, u64 ud, u32 flags)
{
        struct io_uring_sqe *sqe = ring_sqe(L->ring);

        if (sqe == NULL) {
                return;
        }

        sqe->opcode    = op;
        sqe->fd        = fd;
        sqe->addr      = (u64)(uptr)p;
        sqe->len       = n;
        sqe->off       = off;
        sqe->user_data = ud;
        sqe->msg_flags = flags;
}

static void
uring_arm_wake(Loop *L)
{
        if (!L->armed_wake) {
                L->armed_wake = true;
                uring_prep(L, IORING_OP_READ, L->efd, &L->ebuf, sizeof L->ebuf, 0, UD(U_WAKE, 0, 0), 0);
        }
}

static int
uring_wait(Loop *L, i64 ms)
{
        Ty *ty  = L->ty;
        Ring *r = L->ring;

        uring_arm_wake(L);

        if (vN(L->ready) > 0) {
                ms = 0;
        }

        UnlockTy();
        int rc = ring_submit(r, 1, ms);
        LockTy();
        LoopTick(L);

        if (rc < 0 && errno != ETIME) {
                return -errno;
        }

        u32 head = *r->cq_head;
        u32 tail = atomic_load_explicit((_Atomic u32 *)r->cq_tail, memory_order_acquire);
        int n = 0;

        while (head != tail) {
                struct io_uring_cqe *cqe = &r->cqes[head & *r->cq_mask];
                u64 ud  = cqe->user_data;
                i64 res = cqe->res;

                head += 1;
                n    += 1;

                switch (UD_OP(ud)) {
                case U_RECV:
                case U_SEND:
                case U_WATCH:
                        queue(L, UD_SLOT(ud), UD_GEN(ud), UD_OP(ud), res);
                        break;

                case U_ACCEPT:
                        if (res >= 0) {
                                AcceptLen = sizeof AcceptAddr;
                                getpeername(res, (struct sockaddr *)&AcceptAddr, &AcceptLen);
                        }
                        queue(L, 0, 0, U_ACCEPT, res);
                        break;

                case U_WAKE:
                        L->armed_wake = false;
                        queue(L, 0, 0, U_WAKE, res);
                        break;
                }

                if (head - *r->cq_head >= 64 || head == tail) {
                        atomic_store_explicit((_Atomic u32 *)r->cq_head, head, memory_order_release);
                        tail = atomic_load_explicit((_Atomic u32 *)r->cq_tail, memory_order_acquire);
                }
        }

        for (usize i = 0; i < vN(L->ready); ++i) {
                if (v__(L->ready, i).op == U_WAKE) {
                        v__(L->ready, i).op = U_IGNORE;
                        OnWake(L);
                }
        }

        deliver(L);

        return n;
}
#endif

#if defined(__linux__)
static void
ep_ctl(Loop *L, int op, int fd, u32 events, u64 data)
{
        struct epoll_event ev = { .events = events, .data.u64 = data };
        epoll_ctl(L->pfd, op, fd, &ev);
}

static int
epoll_wait_(Loop *L, i64 ms)
{
        Ty *ty = L->ty;
        struct epoll_event evs[BATCH];

        deliver(L);

        if (vN(L->ready) > 0 || vN(*L->evs) > 0 || L->dirty != NULL) {
                ms = 0;
        }

        UnlockTy();
        int n = epoll_wait(L->pfd, evs, BATCH, (int)min(ms, INT32_MAX));
        LockTy();
        LoopTick(L);

        if (n < 0) {
                return (errno == EINTR) ? 0 : -errno;
        }

        for (int i = 0; i < n; ++i) {
                u64 data = evs[i].data.u64;
                u32 e    = evs[i].events;
                u32 slot = (u32)data;

                if (slot == TAG_WAKE) {
                        u64 x;
                        while (read(L->efd, &x, sizeof x) > 0) {
                                continue;
                        }
                        OnWake(L);
                        continue;
                }

                if (slot == TAG_LISTEN) {
                        try_accept(L);
                        continue;
                }

                if (slot & TAG_WATCH) {
                        u32 w = slot & ~TAG_WATCH;
                        int rev = ((e & EPOLLIN) ? POLLIN : 0)
                                | ((e & EPOLLOUT) ? POLLOUT : 0)
                                | ((e & EPOLLERR) ? POLLERR : 0)
                                | ((e & EPOLLHUP) ? POLLHUP : 0);
                        if (w < vN(L->wt) && v_(L->wt, w)->live) {
                                epoll_ctl(L->pfd, EPOLL_CTL_DEL, v_(L->wt, w)->fd, NULL);
                        }
                        queue(L, w, (u32)(data >> 32), U_WATCH, rev);
                        continue;
                }

                Conn *c = conn_of(L, slot, (u32)(data >> 32));
                if (c == NULL) {
                        continue;
                }

                if (e & (EPOLLIN | EPOLLERR | EPOLLHUP | EPOLLRDHUP)) {
                        c->rready = true;
                        if (c->rp != NULL) {
                                try_recv(L, c);
                        }
                }

                if (e & (EPOLLOUT | EPOLLERR | EPOLLHUP)) {
                        c->wready = true;
                        if (c->sp != NULL) {
                                try_send(L, c);
                        }
                }
        }

        deliver(L);

        return n;
}
#endif

#if !defined(__linux__)
static void
kq_change(Loop *L, int fd, int filter, int flags, u64 data)
{
        struct kevent ev;
        EV_SET(&ev, fd, filter, flags, 0, 0, (void *)(uptr)data);
        kevent(L->pfd, &ev, 1, NULL, 0, NULL);
}

static int
kq_wait(Loop *L, i64 ms)
{
        Ty *ty = L->ty;
        struct kevent evs[BATCH];
        struct timespec ts;

        deliver(L);

        if (vN(L->ready) > 0 || vN(*L->evs) > 0 || L->dirty != NULL) {
                ms = 0;
        }

        ts.tv_sec  = ms / 1000;
        ts.tv_nsec = (ms % 1000) * 1000000;

        UnlockTy();
        int n = kevent(L->pfd, NULL, 0, evs, BATCH, (ms < 0) ? NULL : &ts);
        LockTy();
        LoopTick(L);

        if (n < 0) {
                return (errno == EINTR) ? 0 : -errno;
        }

        for (int i = 0; i < n; ++i) {
                u64 data = (u64)(uptr)evs[i].udata;
                u32 slot = (u32)data;

                if (evs[i].filter == EVFILT_USER) {
                        OnWake(L);
                        continue;
                }

                if (slot == TAG_LISTEN) {
                        try_accept(L);
                        continue;
                }

                if (slot & TAG_WATCH) {
                        int rev = (evs[i].filter == EVFILT_READ) ? POLLIN : POLLOUT;
                        if (evs[i].flags & EV_EOF) {
                                rev |= POLLHUP;
                        }
                        queue(L, slot & ~TAG_WATCH, (u32)(data >> 32), U_WATCH, rev);
                        continue;
                }

                Conn *c = conn_of(L, slot, (u32)(data >> 32));
                if (c == NULL) {
                        continue;
                }

                if (evs[i].filter == EVFILT_READ) {
                        c->rready = true;
                        if (c->rp != NULL) {
                                try_recv(L, c);
                        }
                } else if (evs[i].filter == EVFILT_WRITE) {
                        c->wready = true;
                        if (c->sp != NULL) {
                                try_send(L, c);
                        }
                }
        }

        deliver(L);

        return n;
}
#endif

int
IoInit(Loop *L)
{
#if defined(__linux__)
        L->efd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
        if (L->efd < 0) {
                return -errno;
        }

        char const *force = getenv("TY_HTTP_EPOLL");

        if (force == NULL || *force == '\0' || *force == '0') {
                L->ring = ring_new(1024);
                if (L->ring != NULL) {
                        L->io = IO_URING;
                        return 0;
                }
        }

        L->pfd = epoll_create1(EPOLL_CLOEXEC);
        if (L->pfd < 0) {
                return -errno;
        }

        L->io = IO_EPOLL;
        ep_ctl(L, EPOLL_CTL_ADD, L->efd, EPOLLIN | EPOLLET, TAG_WAKE);
#else
        L->pfd = kqueue();
        if (L->pfd < 0) {
                return -errno;
        }

        L->io = IO_KQUEUE;

        struct kevent ev;
        EV_SET(&ev, 1, EVFILT_USER, EV_ADD | EV_CLEAR, 0, 0, (void *)(uptr)TAG_WAKE);
        kevent(L->pfd, &ev, 1, NULL, 0, NULL);
#endif

        return 0;
}

void
IoFree(Loop *L)
{
#if defined(__linux__)
        if (L->ring != NULL) {
                ring_free(L->ring);
                L->ring = NULL;
        }
        if (L->efd >= 0) {
                close(L->efd);
                L->efd = -1;
        }
#endif
        if (L->pfd >= 0) {
                close(L->pfd);
                L->pfd = -1;
        }
}

char const *
IoName(Loop const *L)
{
        switch (L->io) {
        case IO_URING:  return "io_uring";
        case IO_EPOLL:  return "epoll";
        case IO_KQUEUE: return "kqueue";
        }

        return "none";
}

void
IoWake(Loop *L)
{
        if (atomic_exchange(&L->woken, 1) != 0) {
                return;
        }

#if defined(__linux__)
        u64 one = 1;
        (void)!write(L->efd, &one, sizeof one);
#else
        struct kevent ev;
        EV_SET(&ev, 1, EVFILT_USER, 0, NOTE_TRIGGER, 0, (void *)(uptr)TAG_WAKE);
        kevent(L->pfd, &ev, 1, NULL, 0, NULL);
#endif
}

void
IoOpen(Loop *L, Conn *c)
{
        c->rready = true;
        c->wready = true;
        c->rp     = NULL;
        c->sp     = NULL;

        switch (L->io) {
#if defined(__linux__)
        case IO_EPOLL:
                ep_ctl(L, EPOLL_CTL_ADD, c->fd, EPOLLIN | EPOLLOUT | EPOLLRDHUP | EPOLLET, ((u64)c->gen << 32) | c->slot);
                break;
#else
        case IO_KQUEUE:;
                struct kevent evs[2];
                u64 data = ((u64)c->gen << 32) | c->slot;
                EV_SET(&evs[0], c->fd, EVFILT_READ,  EV_ADD | EV_CLEAR, 0, 0, (void *)(uptr)data);
                EV_SET(&evs[1], c->fd, EVFILT_WRITE, EV_ADD | EV_CLEAR, 0, 0, (void *)(uptr)data);
                kevent(L->pfd, evs, 2, NULL, 0, NULL);
                break;
#endif
        }
}

void
IoRecv(Loop *L, Conn *c, char *p, usize n)
{
#if defined(__linux__)
        if (L->io == IO_URING) {
                uring_prep(L, IORING_OP_RECV, c->fd, p, n, 0, UD(U_RECV, c->gen, c->slot), 0);
                return;
        }
#endif
        c->rp = p;
        c->rn = n;

        if (c->rready) {
                try_recv(L, c);
        }
}

void
IoSend(Loop *L, Conn *c, char const *p, usize n)
{
#if defined(__linux__)
        if (L->io == IO_URING) {
                uring_prep(L, IORING_OP_SEND, c->fd, p, n, 0, UD(U_SEND, c->gen, c->slot), HTTP_SEND_FLAGS);
                return;
        }
#endif
        c->sp = p;
        c->sn = n;

        if (c->wready) {
                try_send(L, c);
        }
}

void
IoKill(Loop *L, Conn *c)
{
        c->rp = NULL;
        c->sp = NULL;

#if defined(__linux__)
        if (L->io == IO_URING && (c->reading || c->sending)) {
                shutdown(c->fd, SHUT_RDWR);
        }
#else
        struct kevent evs[2];
        EV_SET(&evs[0], c->fd, EVFILT_READ,  EV_DELETE | EV_RECEIPT, 0, 0, NULL);
        EV_SET(&evs[1], c->fd, EVFILT_WRITE, EV_DELETE | EV_RECEIPT, 0, 0, NULL);
        kevent(L->pfd, evs, 2, evs, 2, NULL);
#endif
}

void
IoAccept(Loop *L)
{
        if (L->accepting || L->g->lfd < 0) {
                return;
        }

        L->accepting = true;

        switch (L->io) {
#if defined(__linux__)
        case IO_URING:;
                struct io_uring_sqe *sqe = ring_sqe(L->ring);
                if (sqe != NULL) {
                        sqe->opcode       = IORING_OP_ACCEPT;
                        sqe->fd           = L->g->lfd;
                        sqe->accept_flags = SOCK_NONBLOCK | SOCK_CLOEXEC;
                        sqe->user_data    = UD(U_ACCEPT, 0, 0);
                }
                break;

        case IO_EPOLL:
                if (!L->backoff) {
                        nonblocking(L->g->lfd);
                        ep_ctl(L, EPOLL_CTL_ADD, L->g->lfd, EPOLLIN | EPOLLEXCLUSIVE, TAG_LISTEN);
                }
                L->backoff = false;
                try_accept(L);
                break;
#else
        case IO_KQUEUE:
                if (!L->backoff) {
                        nonblocking(L->g->lfd);
                        kq_change(L, L->g->lfd, EVFILT_READ, EV_ADD, TAG_LISTEN);
                }
                L->backoff = false;
                try_accept(L);
                break;
#endif
        }
}

void
IoPause(Loop *L)
{
        L->accepting = false;
        L->backoff   = (L->io != IO_URING);
}

void
IoCancelAccept(Loop *L)
{
        switch (L->io) {
#if defined(__linux__)
        case IO_URING:
                if (L->accepting) {
                        struct io_uring_sqe *sqe = ring_sqe(L->ring);
                        if (sqe != NULL) {
                                sqe->opcode    = IORING_OP_ASYNC_CANCEL;
                                sqe->addr      = UD(U_ACCEPT, 0, 0);
                                sqe->user_data = UD(U_IGNORE, 0, 0);
                        }
                }
                break;

        case IO_EPOLL:
                if (L->accepting || L->backoff) {
                        epoll_ctl(L->pfd, EPOLL_CTL_DEL, L->g->lfd, NULL);
                }
                L->accepting = false;
                break;
#else
        case IO_KQUEUE:
                if (L->accepting || L->backoff) {
                        kq_change(L, L->g->lfd, EVFILT_READ, EV_DELETE, 0);
                }
                L->accepting = false;
                break;
#endif
        }

        L->backoff = false;
}

int
IoWatch(Loop *L, u32 slot, int fd, int events)
{
        u32 gen = v_(L->wt, slot)->gen;

        switch (L->io) {
#if defined(__linux__)
        case IO_URING:;
                struct io_uring_sqe *sqe = ring_sqe(L->ring);
                if (sqe == NULL) {
                        return -EBUSY;
                }
                sqe->opcode       = IORING_OP_POLL_ADD;
                sqe->fd           = fd;
                sqe->poll32_events = events;
                sqe->user_data    = UD(U_WATCH, gen, slot);
                return 0;

        case IO_EPOLL:;
                u32 e = ((events & POLLIN) ? EPOLLIN : 0) | ((events & POLLOUT) ? EPOLLOUT : 0) | EPOLLONESHOT;
                struct epoll_event ev = { .events = e, .data.u64 = ((u64)gen << 32) | slot | TAG_WATCH };
                return (epoll_ctl(L->pfd, EPOLL_CTL_ADD, fd, &ev) == 0) ? 0 : -errno;
#else
        case IO_KQUEUE:;
                u64 data = ((u64)gen << 32) | slot | TAG_WATCH;
                if (events & POLLIN) {
                        kq_change(L, fd, EVFILT_READ, EV_ADD | EV_ONESHOT, data);
                }
                if (events & POLLOUT) {
                        kq_change(L, fd, EVFILT_WRITE, EV_ADD | EV_ONESHOT, data);
                }
                return 0;
#endif
        }

        return -ENOSYS;
}

void
IoUnwatch(Loop *L, u32 slot, int fd)
{
        switch (L->io) {
#if defined(__linux__)
        case IO_URING:;
                struct io_uring_sqe *sqe = ring_sqe(L->ring);
                if (sqe != NULL) {
                        sqe->opcode    = IORING_OP_POLL_REMOVE;
                        sqe->addr      = UD(U_WATCH, v_(L->wt, slot)->gen, slot);
                        sqe->user_data = UD(U_IGNORE, 0, 0);
                }
                break;

        case IO_EPOLL:
                epoll_ctl(L->pfd, EPOLL_CTL_DEL, fd, NULL);
                break;
#else
        case IO_KQUEUE:
                kq_change(L, fd, EVFILT_READ,  EV_DELETE, 0);
                kq_change(L, fd, EVFILT_WRITE, EV_DELETE, 0);
                break;
#endif
        }
}

int
IoWait(Loop *L, i64 ms)
{
        switch (L->io) {
#if defined(__linux__)
        case IO_URING: return uring_wait(L, ms);
        case IO_EPOLL: return epoll_wait_(L, ms);
#else
        case IO_KQUEUE: return kq_wait(L, ms);
#endif
        }

        return -ENOSYS;
}

/* vim: set sts=8 sw=8 expandtab: */
