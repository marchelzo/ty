# I/O and more

Ty doesn't try to abstract away operating system APIs to the same extent as some other languages. Instead, it provides a thin layer of abstraction over the underlying system calls, allowing you to interact with the operating system directly when needed. Most of POSIX is exposed by the `os` module, with some exceptions (clock-related functions are in `time`). The libc `stdio` API is exposed by the `stdio` module. 

In addition to the low-level syscall wrappers, Ty does include some higher-level APIs for common tasks:

 - The `path` module is heavily inspired by Python's `pathlib` and provides an object-oriented interface for working with file paths.
 - The `io` module provides a basic interface for working with streams.
 - The `net` module provides two very basic helper functions, `dial` and `listen`, which wrap `socket()`/`getaddrinfo()`/`bind()`/`listen()`/`connect()`, etc. for convenience.
 - The `sh` module provides a wrapper around `os.spawn` for spawning subprocesses with an optional timeout and capturing their output.


## Some examples

### Reading files

```ty
import path (Path)
import os
import io

fn read-file(path: Path | String) {
    // slurp() builtin
    let contents = slurp("{path}")

    // or, using the io module
    let contents = with f = io.open("{path}", 'r') {
        f.slurp()
    }

    // the io module, line-by-line
    with f = io.open("{path}", 'r') {
        for line in f {
            // do something with line
        }
    }

    // or, using os.read
    let fd = os.open("{path}", os.O_RDONLY)
    defer os.close(fd)
    let contents = Blob()
    while os.read(fd, contents, 4096) > 0 {
        // keep reading until EOF
    }
    let contents = contents.str()

    // or, using the path module
    let contents = Path(path).read-text()
}
```


### Writing files

```ty
import path (Path)
import os
import io

fn write-file(path: Path | String, contents: String) {
    // sink() (from prelude)
    contents >> sink("{path}")

    // or, using the io module
    with f = io.open("{path}", 'w') {
        f.write(contents)
    }

    // or, using os.write
    let fd = os.open("{path}", os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o644)
    defer os.close(fd)
    os.write(fd, contents)

    // or, using the path module
    Path(path).write(contents)
}
```

### Spawning subprocesses

```ty
import sh (sh)
import os

let _, result = sh('date')
dbg(result)

dbg(sh('sleep 5', timeoutMs=500))


let proc = os.spawn(['date'], stdout=os.SPAWN_PIPE, stderr=os.SPAWN_NULL)
dbg(os.read(proc.stdout, 512).str())
dbg(os.wait(proc.pid))
```


### Simple TCP echo server

```ty
import net
import os

fn echo-server() {
    let sock = net.listen('tcp', '0.0.0.0:12345')
    defer os.close(sock)

    let conns = []

    for (;;) {
        if not let Ok(events) = os.poll([sock, *conns]) {
            os.sleep(1.0)
            continue
        }

        for match events {
            (::sock, os.POLLIN) => {
                if let (conn, addr) = os.accept(sock) {
                    conns.push(conn)
                }
            },

            (conn, os.POLLIN) => {
                if let $data = os.read(conn, 8192) {
                    os.write(conn, data)
                } else {
                    os.close(conn)
                    conns.filter!(\_ != conn)
                }
            }
        }
    }
}
```

### 
