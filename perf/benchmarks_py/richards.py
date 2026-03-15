I_IDLE = 1
I_WORK = 2
I_HANDLERA = 3
I_HANDLERB = 4
I_DEVA = 5
I_DEVB = 6

K_DEV = 1000
K_WORK = 1001
BUFSIZE = 4

class Packet:
    __slots__ = ('link', 'ident', 'kind', 'datum', 'data')
    def __init__(self, link, ident, kind):
        self.link = link
        self.ident = ident
        self.kind = kind
        self.datum = 0
        self.data = [0, 0, 0, 0]

def append_to(pkt, lst):
    pkt.link = None
    if lst is None:
        return pkt
    p = lst
    while p.link is not None:
        p = p.link
    p.link = pkt
    return lst

class TaskState:
    __slots__ = ('pp', 'tw', 'th')
    def __init__(self, pp, tw, th):
        self.pp = pp; self.tw = tw; self.th = th

class Task:
    __slots__ = ('link', 'ident', 'priority', 'input', 'pp', 'tw', 'th', 'kind', 'rec')
    def __init__(self, link, ident, priority, inp, state, kind, rec):
        self.link = link; self.ident = ident; self.priority = priority
        self.input = inp
        self.pp = state.pp; self.tw = state.tw; self.th = state.th
        self.kind = kind; self.rec = rec

    def is_waiting_with_packet(self):
        return self.pp and self.tw and not self.th

    def is_holding_or_waiting(self):
        return self.th or (not self.pp and self.tw)

    def add_packet(self, p, old):
        if self.input is None:
            self.input = p; self.pp = True
            if self.priority > old.priority:
                return self
        else:
            append_to(p, self.input)
        return old

    def wait(self):
        self.tw = True; return self

    def set_running(self):
        self.pp = False; self.tw = False; self.th = False

    def mark_pending(self):
        self.pp = True; self.tw = False; self.th = False

class TaskWorkArea:
    def __init__(self):
        self.task_list = None
        self.task_tab = [None] * 10
        self.hold_count = 0
        self.qpkt_count = 0

    def new_task(self, ident, priority, inp, state, kind, rec):
        t = Task(self.task_list, ident, priority, inp, state, kind, rec)
        self.task_list = t
        self.task_tab[ident] = t
        return t

    def find(self, ident):
        t = self.task_tab[ident]
        if t is None:
            raise RuntimeError("Bad task id")
        return t

KIND_DEVICE = 0
KIND_IDLE = 1
KIND_HANDLER = 2
KIND_WORKER = 3

def qpkt(t, pkt, work):
    target = work.find(pkt.ident)
    work.qpkt_count += 1
    pkt.link = None
    pkt.ident = t.ident
    return target.add_packet(pkt, t)

def hold(t, work):
    work.hold_count += 1
    t.th = True
    return t.link

def release(t, ident, work):
    target = work.find(ident)
    target.th = False
    if target.priority > t.priority:
        return target
    return t

def device_fn(t, pkt, work):
    if pkt is not None:
        t.rec['pending'] = pkt
        return hold(t, work)
    p = t.rec.get('pending')
    if p is not None:
        t.rec['pending'] = None
        return qpkt(t, p, work)
    return t.wait()

def handler_fn(t, pkt, work):
    h = t.rec
    if pkt is not None:
        if pkt.kind == K_WORK:
            h['wi'] = append_to(pkt, h['wi'])
        else:
            h['di'] = append_to(pkt, h['di'])

    if h['wi'] is None:
        return t.wait()

    wp = h['wi']
    if wp.datum >= BUFSIZE:
        h['wi'] = wp.link
        return qpkt(t, wp, work)
    if h['di'] is None:
        return t.wait()

    dev = h['di']
    h['di'] = dev.link
    dev.datum = wp.data[wp.datum]
    wp.datum += 1
    return qpkt(t, dev, work)

def idle_fn(t, pkt, work):
    rec = t.rec
    rec['count'] -= 1
    if rec['count'] == 0:
        return hold(t, work)
    if (rec['control'] & 1) == 0:
        rec['control'] //= 2
        return release(t, I_DEVA, work)
    else:
        rec['control'] = (rec['control'] // 2) ^ 0xd008
        return release(t, I_DEVB, work)

def worker_fn(t, pkt, work):
    w = t.rec
    if pkt is None:
        return t.wait()
    w['dest'] = I_HANDLERB if w['dest'] == I_HANDLERA else I_HANDLERA
    pkt.ident = w['dest']
    pkt.datum = 0
    for i in range(BUFSIZE):
        w['count'] += 1
        if w['count'] > 26:
            w['count'] = 1
        pkt.data[i] = 64 + w['count']
    return qpkt(t, pkt, work)

FN_TABLE = [device_fn, idle_fn, handler_fn, worker_fn]

def run_task(t, work):
    msg = None
    if t.is_waiting_with_packet():
        msg = t.input
        t.input = msg.link
        if t.input is None:
            t.set_running()
        else:
            t.mark_pending()
    return FN_TABLE[t.kind](t, msg, work)

def schedule(work):
    t = work.task_list
    while t is not None:
        if t.is_holding_or_waiting():
            t = t.link
        else:
            t = run_task(t, work)

def richards_once():
    work = TaskWorkArea()
    running = TaskState(False, False, False)
    waiting = TaskState(False, True, False)
    ww_pkt = TaskState(True, True, False)

    work.new_task(I_IDLE, 1, None, running, KIND_IDLE, {'control': 1, 'count': 10000})

    wkq = Packet(Packet(None, 0, K_WORK), 0, K_WORK)
    work.new_task(I_WORK, 1000, wkq, ww_pkt, KIND_WORKER, {'dest': I_HANDLERA, 'count': 0})

    wkq = Packet(Packet(Packet(None, I_DEVA, K_DEV), I_DEVA, K_DEV), I_DEVA, K_DEV)
    work.new_task(I_HANDLERA, 2000, wkq, ww_pkt, KIND_HANDLER, {'wi': None, 'di': None})

    wkq = Packet(Packet(Packet(None, I_DEVB, K_DEV), I_DEVB, K_DEV), I_DEVB, K_DEV)
    work.new_task(I_HANDLERB, 3000, wkq, ww_pkt, KIND_HANDLER, {'wi': None, 'di': None})

    work.new_task(I_DEVA, 4000, None, waiting, KIND_DEVICE, {'pending': None})
    work.new_task(I_DEVB, 5000, None, waiting, KIND_DEVICE, {'pending': None})

    schedule(work)

    assert work.hold_count == 9297
    assert work.qpkt_count == 23246

def richards_bench(n):
    for _ in range(n):
        richards_once()
