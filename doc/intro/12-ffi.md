# C FFI

The `ffi` module allows Ty programs to interop with native libraries, and provides a macro, `C!`, which tries to make doing so as painless as possible. It can be used to declare foreign functions, map C structs to Ty classes, and wrap Ty closures as C function pointers.

## Loading libraries

`c.open(name)` searches standard library paths on the current platform and returns a handle, or `nil` if the library isn't found.

```ty
import ffi as c (C!)

if not let $m = c.open('m') {
    throw 'failed to load libm'
}

C! m fn {
    double cbrt(double);
    double log2(double);
    double fma(double, double, double);
}

print("cbrt(27) = {cbrt(27.0)}")
print("log2(1024) = {log2(1024.0)}")
print("fma(2, 3, 4) = {fma(2.0, 3.0, 4.0)}")
```

The library handle is passed as a prefix to `C! fn`. Without a prefix, symbols are resolved from the default search path (libc, etc.):

```ty
import ffi as c (C!)

C! fn {
    int abs(int);
    long labs(long);
    char *getenv(char *name);
}

print(abs(-42))
print(labs(-100))
print(c.str(getenv('HOME')))
```

## Structs

`C! struct` generates a Ty class whose memory layout matches the C struct. Each field gets a getter and a setter. The constructor accepts keyword arguments for each field.

```ty
import ffi as c (C!)

C! struct Vec3 {
    float x;
    float y;
    float z;
}

let v = Vec3(x: 1.0, y: 2.0, z: 3.0)
print("({v.x}, {v.y}, {v.z})")
print("size: {#Vec3} bytes")
```

### Unions

Anonymous unions overlay their members in the same memory:

```ty
import ffi as c (C!)

C! struct Packet {
    int kind;
    union {
        int code;
        float value;
    };
}

let p = Packet(kind: 1, code: 42)
print("code = {p.code}")

p.value = 3.14
print("value = {p.value}")
// code and value overlap, so setting one changes the other
print("code is now {p.code}")
```

### Nested structs

Anonymous nested structs and unions are flattened — their fields become top-level members of the generated class:

```ty
import ffi as c (C!)

C! struct Event {
    int kind;
    struct {
        int x;
        int y;
    };
    union {
        int key;
        int button;
    };
}

let e = Event(kind: 1, x: 100, y: 200, key: 13)
print("pos = ({e.x}, {e.y}), key = {e.key}")
```

## Closures (C callbacks)

`C! closure` wraps a Ty function as a C-callable function pointer. This lets you pass Ty code to C APIs that expect callbacks.

```ty
import ffi as c (C!)
import ptr

C! fn {
    void qsort(void *base, size_t nmemb, size_t size, void *cmp);
}

C! closure cmp(pa: c.ptr, pb: c.ptr) -> c.int {
    c.load(c.int, pa) <=> c.load(c.int, pb)
}

let nums = c.new(c.int, 9)
for ..9 {
    nums[it] = rand(300)
}

print("Initially: {[nums[it] for ..9]}")
qsort(nums, 9, c.size(c.int), cmp)
print("After qsort: {[nums[it] for ..9]}")
```

## Memory operations

The `c` (ffi) module provides low-level memory primitives:

| Function | Description |
|----------|-------------|
| `c.new(type, ?count)` | Allocate `count` elements (default 1) |
| `c.alloc(size)` | Raw `malloc(size)` |
| `c.box(type, ?val)` | Allocate and initialize a single value |
| `c.free(ptr)` | Free allocated memory |
| `c.load(type, ptr)` | Read a value from a pointer |
| `c.store(type, ptr, val)` | Write a value to a pointer |
| `c.size(type)` | `sizeof(type)` |
| `c.str(ptr, ?len)` | Read a C string as a Ty `String` |
| `ptr.typed(ptr, type)` | Cast a pointer to a different element type |

Pointers may carry pointee type information, in which case the type argument to `c.load` and `c.store` can be omitted,
and pointer arithmetic will automatically scale by the element size. For example:

```ty
import ffi as c

// Returns a typed pointer to 4 i32 values
let buf = c.new(c.i32, 4)

for i in ..4 {
    buf[i] = (i + 1) * 10000
}

for i in ..4 {
    print(buf[i])
}

let octets = [buf.as(c.u8)[i] for i in ..(4 * c.size(c.i32))]
let groups = octets.groups-of(4).map(&unwords)
print('Hex:')
for groups {
    print("  {it}")
}

c.free(buf)
```

## Type aliases

For readability, it's common to alias C types to descriptive names. These aliases work in `C! struct` and `C! fn` declarations:

```ty
import ffi as c (C!)

const pid_t  = c.i32

C! fn {
    pid_t getpid();
}

print("pid: {getpid()}")
```
