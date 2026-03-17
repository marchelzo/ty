# Threads

Ty exposes native OS threads via the `Thread` class. Its constructor takes a function (and optionally its arguments) and spawns a new thread immediately. `join()` blocks until the thread finishes and returns its result.

## Safety

In contrast to most high-level, dynamic languages, Ty makes no attempt to guarantee safety. The interpreter internals are thread-safe, but objects can easily be corrupted by unsychronized conrurrent access. Rather than using a GIL or per-object locks, Ty tries to provide a variety of synchronization primitives that can be used to coordinate access to shared data, and leaves it to the programmer to use them correctly.

## Basic usage

```ty
import os
import time (now)

fn slow-square(x) {
    os.sleep(0.1)
    x * x
}

let t0 = now()
let thread = Thread(slow-square, 7)
let result = thread.join()
let t1 = now()

print("Computed {result} in {t1 - t0:.3} seconds")
```

## Atomic

`Atomic` wraps an integer for lock-free atomic operations. It supports `+=`, `-=`, `load()`, `store()`, and `try-swap()` (CAS).

```ty
let counter = Atomic(0)

let threads = [Thread(fn () {
    for ..1000 {
        counter += 1
    }
}) for ..4]

for t in threads { t.join() }
print(counter)
```

## Mutex

`Mutex` provides mutual exclusion. Use `lock()`/`unlock()` or a `with` block to delimit a critical section.

```ty
let mtx = Mutex()
let total = 0

let threads = [Thread(fn () {
    for ..1000 {
        with mtx {
            total += 1
        }
    }
}) for ..4]

for threads { it.join() }
print(total)
```

## Sync

`Sync(value)` wraps any value with a mutex. All method calls on the wrapper are automatically locked:

```ty
let xs = Sync([])

let threads = [Thread(fn (i) {
    for j in ..5 {
        xs.push(i * 5 + j)
    }
}, i) for i in ..4]

for threads { it.join() }
print(xs.sort())
```

## SharedQueue

A thread-safe blocking queue. `take()` blocks until an item is available. `close()` signals that no more items will be added; workers blocking on `take()` will unblock.

```ty
let q = SharedQueue()

let producers = [Thread(fn (i) {
    for j in ..3 {
        q.put(i * 3 + j)
    }
}, it) for ..2]

let results = Sync([])
let consumer = Thread(fn () {
    for ..6 {
        results.push(q.take())
    }
})

for producers { it.join() }
consumer.join()
print(results.sort())
```

`try-take(timeout)` returns `Some(value)` or `None`:

```ty
let q = SharedQueue()

q.put(42)
print(q.try-take())
print(q.try-take(0.01))
```

## ThreadPool and Future

`ThreadPool(n, f)` creates `n` worker threads, each running `f` on submitted arguments. `submit()` returns a `Future`.

```ty
import tp (ThreadPool, Future)

let pool = ThreadPool(4, fn (x: Int) -> Int {
    x * x
})

let futures = [pool.submit(i) for i in ..8]

// Iterate results in completion order
for Future.iter(futures) {
    print(it)
}
```

`Future` also has `wait()` (block for result), `cancel()`, and static combinators `Future.all()` and `Future.any()`.

## CondVar

Condition variables work with a `Mutex` for classic wait/signal patterns:

```ty
let mtx = Mutex()
let cv = CondVar()
let ready = false

let t = Thread(fn () {
    with mtx { ready = true }
    cv.signal()
})

mtx.lock()
while !ready { cv.wait(mtx) }
print("ready: {ready}")
mtx.unlock()
t.join()
```

`cv.broadcast()` wakes all waiters. `cv.wait(mtx, timeout)` accepts an optional timeout in seconds.


## Thread-local storage

Top-level variable bindings can use `__tls` as a pseudo-namespace to declare thread-local storage:

```ty
let __tls::items = []

fn work() {
    for ..8 {
        items.push(rand(100))
    }
    print("Thread {Thread.id()}: {items}")
}

let threads = [Thread(work) for ..8]
for threads { it.join() }
```
