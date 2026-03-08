# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**Ty** is an interpreted, gradually-typed programming language implementation written in C (C23
standard). It includes a bytecode VM, optional JIT compiler (DynASM-based), garbage collector,
coroutine system, and a standard library written in Ty itself.

## Build System

### CMake (primary, cross-platform)

Dependencies are managed via vcpkg.
The vcpkg root is expected at `_vcpkg/` (set in `CMakePresets.json`).
The `./scripts/setup-vcpkg.sh` script can be used to perform the initial clone of vcpkg into
the `_vcpkg` subdirectory.

```bash
# Configure
cmake --preset <preset-name>

# Build
cmake --build --preset <preset-name>
```

**Available presets** (see [CMakePresets.json](CMakePresets.json)):
- `msvc2026` / `msvc2026-debug` — Windows, Visual Studio 2026, MSVC
- `clang-windows` / `clang-windows-debug` — Windows, Clang (Ninja)
- `gcc` / `gcc-ninja` — Linux, GCC
- `clang-osx` — macOS, Apple Clang

Build output goes to `_build/<preset-name>/`. Binaries produced: `ty`, `tyls`, optionally `typrof`.

### Makefile (Unix/Linux/macOS only)

```bash
make                  # Default optimized build (-Og -g3)
make RELEASE=1        # Optimized release (-O3, LTO, mcpu=native)
make DEBUG=1          # Debug with ASAN
make TDEBUG=1         # Debug with ThreadSanitizer
make tyls             # Build language server
make install          # Install to /usr/local/bin and ~/.ty/
make clean
```

**Makefile flags** (combine freely):
- `NO_JIT=1` — Disable JIT
- `LOG=1` — Enable internal logging (disabled by default via `-DTY_NO_LOG`)
- `NO_NSYNC=1` — Disable nsync synchronization
- `JEMALLOC=1` — Use jemalloc instead of mimalloc
- `LTO=1` — Force link-time optimization
- `PROFILE_TYPES=1` — Enable type system profiling

**Pre-build requirements** (Makefile):
- `gperf` generates [include/keywords.h](include/keywords.h) from
  [src/keywords.gperf](src/keywords.gperf)
- `luajit` + DynASM generates `src/jit_x64.h` or `src/jit_arm64.h` from `.dasc` files
- `LuaJIT` project must be cloned from `https://github.com/LuaJIT/LuaJIT` into the
  project root at `<project-root>/LuaJIT` so that the build can find `LuaJIT/dynasm/dynasm.lua`

## Running Tests

Tests require a built `ty` executable in the project root (or on PATH):

```bash
make test             # Runs: ./ty test.ty

# Run a single test file
./ty --test tests/array.ty

# Run the full test suite
./ty test.ty
```

The test runner [test.ty](test.ty) is written in Ty itself. It runs test files from
[tests/](tests/) in parallel with a 5-second timeout per test.

## Architecture

### Compilation Pipeline

```
Source text
  → Lexer (lex.c / token.c)
  → Parser + AST (parse.c)
  → Type checker + Compiler → Bytecode (compiler.c, types.c)
  → VM execution (vm.c)
       └─ optional JIT (jit.c + jit_x64.dasc / jit_arm64.dasc)
```

### Core Source Modules ([src/](src/))

| File           | Role                                                          |
|----------------|---------------------------------------------------------------|
| `compiler.c`   | Type checking, compilation, constant folding (~20K LOC)       |
| `types.c`      | Type system: inference, constraints, refinements (~12K LOC)   |
| `vm.c`         | Bytecode interpreter, exception handling, coroutines (~11K LOC) |
| `functions.c`  | Built-in functions and standard library glue (~10K LOC)       |
| `parse.c`      | Parser, AST construction (~7.5K LOC)                          |
| `jit.c`        | JIT driver; arch-specific code in `.dasc` files (~7K LOC)     |
| `gc.c`         | Naive STW mark-and-sweep GC                                   |
| `ffi.c`        | Foreign function interface via libffi                         |
| `value.c`      | Core `Value` type (32-byte tagged union)                      |
| `scope.c`      | Symbol tables and lexical scoping                             |
| `class.c`      | Class system with inheritance and traits                      |

### Value Representation

All Ty values are a packed 32-byte `Value` struct (defined in [include/ty.h](include/ty.h)) with a
type byte, 16-bit tag, and a union payload. This is the central type used throughout the VM and
compiler.

### Executables

- **ty** — main interpreter (entry: `ty.c`)
- **tyls** — language server (entry: `tyls.c`; compiled with `-DTY_LS`)
- **typrof** — profiler (entry: `ty.c`; compiled with `-DTY_PROFILER`)

### Vendored Libraries

| Library    | Location                              | Purpose                                  |
|------------|---------------------------------------|------------------------------------------|
| libco      | [libco/](libco/)                      | Coroutines (lightweight cooperative threads) |
| dtoa       | [dtoa/](dtoa/)                        | Swift's double-to-string conversion      |
| libmd      | [libmd/](libmd/)                      | MD5/SHA hash functions                   |
| unibilium  | [unibilium/](unibilium/)              | Terminal capability database             |
| nsync      | [nsync/](nsync/)                      | Google synchronization primitives (optional) |
| DynASM     | [LuaJIT/dynasm/](LuaJIT/dynasm/)      | JIT code generation DSL                  |

### vcpkg Dependencies

`libffi`, `sqlite3`, `utf8proc`, `pcre2`, `xxHash`, `mimalloc`

### Standard Library

~50 Ty modules in [lib/](lib/) — installed to `~/.ty/`.
Key modules: `prelude.ty`, `io.ty`, `os.ty`, `ffi.ty`, `http.ty`, `json.ty`, `regex.ty`,
`sqlite.ty`, `term.ty`.

## Platform Notes

- **Linux/macOS**
  - Primary development platforms
  - CMake and Makefile are both supported

- **Windows**
  - Currently unsupported, does not compile on Windows.
  - Uses CMake + MSVC or clang-cl
  - Required file: `ioctl_constants.h` is created as an empty stub
  - Required file: `keywords.h` must be created on a platform with access to gperf and copied
    into `include/keywords.h`
