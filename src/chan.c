#include "ty.h"
#include "vm.h"
#include "chan.h"
#include "dict.h"
#include "class.h"

typedef struct {
        iptr id;
        usize entry;
} SeenEntry;

typedef vec(SeenEntry) SeenVec;

static inline usize
qmask(Channel const *chan)
{
        return chan->cap - 1;
}

static inline usize
qcount(Channel const *chan)
{
        return (chan->tail - chan->head + chan->cap) & qmask(chan);
}

static bool
basic(Value const *v)
{
        switch (V_TYPE(*v) & ~VALUE_TAGGED) {
        case VALUE_BOOLEAN:
        case VALUE_INTEGER:
        case VALUE_REAL:
        case VALUE_NIL:
        case VALUE_TAG:
                return true;

        case VALUE_STRING:
                return V_RO(*v);

        case VALUE_FUNCTION:
                return (V_ENV(*v) == NULL && V_XINFO(*v) == NULL);

        default:
                return false;
        }
}

static iptr
ident(Value const *v)
{
        switch (V_TYPE(*v) & ~VALUE_TAGGED) {
        case VALUE_ARRAY:   return (iptr)V_ARRAY(*v);
        case VALUE_DICT:    return (iptr)V_DICT(*v);
        case VALUE_OBJECT:  return (iptr)V_OBJECT(*v);
        case VALUE_BLOB:    return (iptr)V_BLOB(*v);
        case VALUE_QUEUE:   return (iptr)V_QUEUE(*v);
        case VALUE_TUPLE:   return (iptr)V_ITEMS(*v);
        case VALUE_STRING:  return (iptr)V_STR0(*v);
        default:            return -1;
        }
}

static i64
seen(SeenVec const *sv, iptr id)
{
        for (usize i = 0; i < vN(*sv); ++i) {
                if (v_(*sv, i)->id == id) {
                        return v_(*sv, i)->entry;
                }
        }

        return -1;
}

static void
emit(Ty *ty, ValueVector *out, Value v)
{
        svP(*out, v);
}

static void
prepare(Ty *ty, ValueVector *out, SeenVec *sv, Value const *v)
{
        if (basic(v)) {
                emit(ty, out, *v);
                return;
        }

        iptr id = ident(v);
        i64 ref = (id != -1) ? seen(sv, id) : -1;

        if (ref != -1) {
                emit(ty, out, REF((void *)(iptr)ref));
                return;
        }

        usize slot = vN(*out);

        if (id != -1) {
                svP(*sv, ((SeenEntry){ .id = id, .entry = slot }));
        }

        u8 type = V_TYPE(*v) & ~VALUE_TAGGED;

        switch (type) {
        case VALUE_STRING: {
                u8 *copy = xmA(V_BYTES(*v));
                memcpy(copy, V_STR(*v), V_BYTES(*v));
                Value e = VALUE_BOX_(
                        .type  = V_TYPE(*v),
                        .tags  = V_TAGS(*v),
                        .str   = copy,
                        .bytes = V_BYTES(*v),
                        .str0  = copy,
                        .ro    = true,
                );
                emit(ty, out, e);
                break;
        }

        case VALUE_BLOB: {
                usize n = vN(*V_BLOB(*v));
                u8 *copy = xmA(n);
                memcpy(copy, vv(*V_BLOB(*v)), n);
                Value e = VALUE_BOX_(
                        .type  = V_TYPE(*v),
                        .tags  = V_TAGS(*v),
                        .str   = copy,
                        .bytes = n,
                );
                emit(ty, out, e);
                break;
        }

        case VALUE_ARRAY: {
                Value header = VALUE_BOX_(.type=V_TYPE(*v), .tags=V_TAGS(*v), .src=V_ARRAY(*v)->count);
                emit(ty, out, header);
                for (usize i = 0; i < V_ARRAY(*v)->count; ++i) {
                        prepare(ty, out, sv, &V_ARRAY(*v)->items[i]);
                }
                break;
        }

        case VALUE_TUPLE: {
                i32 *ids = NULL;
                if (V_IDS(*v) != NULL) {
                        ids = xmA(V_COUNT(*v) * sizeof (i32));
                        memcpy(ids, V_IDS(*v), V_COUNT(*v) * sizeof (i32));
                }
                Value header = VALUE_BOX_(
                        .type  = V_TYPE(*v),
                        .tags  = V_TAGS(*v),
                        .count = V_COUNT(*v),
                        .ids   = ids,
                );
                emit(ty, out, header);
                for (i32 i = 0; i < V_COUNT(*v); ++i) {
                        prepare(ty, out, sv, &V_ITEMS(*v)[i]);
                }
                break;
        }

        case VALUE_DICT: {
                Value header = VALUE_BOX_(.type=V_TYPE(*v), .tags=V_TAGS(*v), .src=V_DICT(*v)->count);
                emit(ty, out, header);
                for (DictItem *it = DictFirst(V_DICT(*v)); it != NULL; it = it->next) {
                        prepare(ty, out, sv, &it->k);
                        prepare(ty, out, sv, &it->v);
                }
                prepare(ty, out, sv, &V_DICT(*v)->dflt);
                break;
        }

        case VALUE_OBJECT: {
                Value header = VALUE_BOX_(
                        .type   = V_TYPE(*v),
                        .tags   = V_TAGS(*v),
                        .class  = V_CLASS(*v),
                        .object = (TyObject *)(uptr)V_OBJECT(*v)->nslot,
                );
                emit(ty, out, header);
                for (u32 i = 0; i < V_OBJECT(*v)->nslot; ++i) {
                        prepare(ty, out, sv, &V_OBJECT(*v)->slots[i]);
                }
                break;
        }

        case VALUE_QUEUE: {
                usize n = 0;
                Queue *q = V_QUEUE(*v);
                if (q->cap > 0) {
                        n = (q->tail >= q->head)
                          ? (q->tail - q->head)
                          : (q->cap - q->head + q->tail);
                }
                Value header = VALUE_BOX_(.type=V_TYPE(*v), .tags=V_TAGS(*v), .src=n);
                emit(ty, out, header);
                for (usize i = 0; i < n; ++i) {
                        usize idx = (q->head + i) % q->cap;
                        prepare(ty, out, sv, &q->items[idx]);
                }
                break;
        }

        default:
                emit(ty, out, NIL);
                break;
        }
}

static Value
reconstruct(Ty *ty, Value *msg, usize *cursor)
{
        Value e = msg[(*cursor)++];
        u8 type = V_TYPE(e) & ~VALUE_TAGGED;

        if (type == VALUE_REF) {
                return msg[(uptr)V_PTR(e)];
        }

        if (basic(&e)) {
                return e;
        }

        switch (type) {
        case VALUE_STRING: {
                u8 *s = value_string_clone(ty, V_STR(e), V_BYTES(e));
                xmF((void *)V_STR(e));
                Value r = VALUE_BOX_(
                        .type  = V_TYPE(e),
                        .tags  = V_TAGS(e),
                        .str   = s,
                        .bytes = V_BYTES(e),
                        .str0  = s,
                        .ro    = false,
                );
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_BLOB: {
                Blob *b = value_blob_new(ty);
                if (V_BYTES(e) > 0) {
                        uvR(*b, V_BYTES(e));
                        memcpy(vv(*b), V_STR(e), V_BYTES(e));
                        vN(*b) = V_BYTES(e);
                }
                xmF((void *)V_STR(e));
                Value r = BLOB(b);
                r = value_with_tags(ty, r, V_TAGS(e));
                msg[*cursor - 1] = r;
                return r;
        }

        case VALUE_ARRAY: {
                usize n = V_SRC(e);
                Array *a = value_array_new_sized(ty, n);
                Value r = ARRAY(a);
                r = value_with_tags(ty, r, V_TAGS(e));
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        value_array_push(ty, a, reconstruct(ty, msg, cursor));
                }
                return r;
        }

        case VALUE_TUPLE: {
                i32 n = V_COUNT(e);
                Value r = value_tuple_alloc(ty, n, V_IDS(e) != NULL);
                Value *items = V_ITEMS(r);
                if (V_IDS(e) != NULL) {
                        memcpy(V_IDS(r), V_IDS(e), n * sizeof (i32));
                        xmF(V_IDS(e));
                }
                r = value_with_tags(ty, r, V_TAGS(e));
                msg[*cursor - 1] = r;
                for (i32 i = 0; i < n; ++i) {
                        items[i] = reconstruct(ty, msg, cursor);
                }
                return r;
        }

        case VALUE_DICT: {
                usize n = V_SRC(e);
                Dict *d = dict_new(ty);
                Value r = DICT(d);
                r = value_with_tags(ty, r, V_TAGS(e));
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        Value k = reconstruct(ty, msg, cursor);
                        Value v = reconstruct(ty, msg, cursor);
                        dict_put_value(ty, d, k, v);
                }
                d->dflt = reconstruct(ty, msg, cursor);
                return r;
        }

        case VALUE_OBJECT: {
                u32 nslot = (uptr)V_OBJECT(e);
                usize size = sizeof (TyObject) + nslot * sizeof (Value);
                TyObject *obj = uAo0(size, GC_OBJECT);
                obj->class = class_get(ty, V_CLASS(e));
                obj->nslot = nslot;
                Value r = OBJECT(obj, V_CLASS(e));
                r = value_with_tags(ty, r, V_TAGS(e));
                msg[*cursor - 1] = r;
                for (u32 i = 0; i < nslot; ++i) {
                        obj->slots[i] = reconstruct(ty, msg, cursor);
                }
                return r;
        }

        case VALUE_QUEUE: {
                usize n = V_SRC(e);
                Queue *q = mAo0(sizeof (Queue), GC_QUEUE);
                if (n > 0) {
                        q->items = uA(n * sizeof (Value));
                        q->cap = n;
                }
                Value r = QUEUE(q);
                r = value_with_tags(ty, r, V_TAGS(e));
                msg[*cursor - 1] = r;
                for (usize i = 0; i < n; ++i) {
                        q->items[i] = reconstruct(ty, msg, cursor);
                }
                q->tail = n;
                return r;
        }

        default:
                return NIL;
        }
}

static void
enqueue(Channel *chan, Value *msg)
{
        usize n = chan->cap ? qcount(chan) : 0;

        if (n + 1 >= chan->cap) {
                usize   cap = chan->cap ? chan->cap * 2 : 8;
                Value **buf = mrealloc(NULL, cap * sizeof (Value *));

                for (usize i = 0; i < n; ++i) {
                        buf[i] = chan->items[(chan->head + i) & qmask(chan)];
                }

                xmF(chan->items);
                chan->items = buf;
                chan->head  = 0;
                chan->tail  = n;
                chan->cap   = cap;
        }

        chan->items[chan->tail] = msg;
        chan->tail = (chan->tail + 1) & qmask(chan);
}

void
chan_send(Ty *ty, Channel *chan, Value v)
{
        ValueVector out = {0};
        SeenVec sv = {0};
        Value *msg;
        usize n;

        WITH_SCRATCH {
                prepare(ty, &out, &sv, &v);
                n = vN(out);
                msg = xmA(n * sizeof (Value));
                memcpy(msg, vv(out), n * sizeof (Value));
        }

        UnlockTy();
        TyMutexLock(&chan->m);
        atomic_fetch_add_explicit(&chan->waiters, 1, memory_order_acq_rel);
        enqueue(chan, msg);
        atomic_fetch_sub_explicit(&chan->waiters, 1, memory_order_acq_rel);
        TyMutexUnlock(&chan->m);
        TyCondVarSignal(&chan->c);
        LockTy();
}

static bool
dequeue(Ty *ty, Channel *chan, Value *v)
{
        if (chan->head == chan->tail) {
                atomic_fetch_sub_explicit(&chan->waiters, 1, memory_order_acq_rel);
                TyMutexUnlock(&chan->m);
                LockTy();
                return false;
        }

        Value *msg = chan->items[chan->head];
        chan->head = (chan->head + 1) & qmask(chan);

        atomic_fetch_sub_explicit(&chan->waiters, 1, memory_order_acq_rel);
        TyMutexUnlock(&chan->m);
        LockTy();

        CheckUsed(ty);
        GC_STOP();

        usize cursor = 0;
        *v = reconstruct(ty, msg, &cursor);

        GC_RESUME();

        xmF(msg);

        return true;
}

bool
chan_recv(Ty *ty, Channel *chan, Value *v)
{
        UnlockTy();
        TyMutexLock(&chan->m);
        atomic_fetch_add_explicit(&chan->waiters, 1, memory_order_acq_rel);

        while (chan->head == chan->tail && chan->open) {
                TyCondVarWait(&chan->c, &chan->m);
        }

        return dequeue(ty, chan, v);
}

bool
chan_try_recv(Ty *ty, Channel *chan, Value *v, i64 timeout)
{
        UnlockTy();
        TyMutexLock(&chan->m);
        atomic_fetch_add_explicit(&chan->waiters, 1, memory_order_acq_rel);

        if (chan->open && chan->head == chan->tail) {
                TyCondVarTimedWaitRelative(&chan->c, &chan->m, timeout);
        }

        return dequeue(ty, chan, v);
}

static void
discard(Value *msg, usize *cursor)
{
        Value e = msg[(*cursor)++];
        u8 type = V_TYPE(e) & ~VALUE_TAGGED;

        if (type == VALUE_REF || basic(&e)) {
                return;
        }

        switch (type) {
        case VALUE_STRING:
        case VALUE_BLOB:
                xmF((void *)V_STR(e));
                break;

        case VALUE_TUPLE:
                xmF(V_IDS(e));
                for (i32 i = 0; i < V_COUNT(e); ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_ARRAY:
        case VALUE_QUEUE:
                for (usize i = 0; i < V_SRC(e); ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_DICT:
                for (usize i = 0; i < 2 * V_SRC(e) + 1; ++i) {
                        discard(msg, cursor);
                }
                break;

        case VALUE_OBJECT:
                for (u32 i = 0; i < (uptr)V_OBJECT(e); ++i) {
                        discard(msg, cursor);
                }
                break;
        }
}

void
chan_destroy(Ty *ty, Channel *chan)
{
        TyMutexLock(&chan->m);
        chan->open = false;
        usize n = chan->cap ? qcount(chan) : 0;
        usize h = chan->head;
        chan->head = chan->tail = 0;
        TyMutexUnlock(&chan->m);

        TyCondVarBroadcast(&chan->c);

        while (atomic_load_explicit(&chan->waiters, memory_order_acquire) != 0) {
                ;
        }

        for (usize i = 0; i < n; ++i) {
                Value *msg = chan->items[(h + i) & qmask(chan)];
                usize cursor = 0;
                discard(msg, &cursor);
                xmF(msg);
        }

        TyMutexDestroy(&chan->m);
        TyCondVarDestroy(&chan->c);
        xmF(chan->items);
}

/* vim: set sw=8 sts=8 expandtab: */
