# Distributing Aletheia

---
**Version**: 1.1.1 (canonical sources: `haskell-shim/aletheia.cabal` `version:` field and `python/pyproject.toml` `version =` field — update those when bumping)
**Last Updated**: 2026-04-15
**Platform**: Linux x86-64 only
---

> **Python users**: The library is loaded automatically via ctypes. This guide is for C, C++, and Go consumers integrating `libaletheia-ffi.so` directly.

How to package, distribute, and integrate `libaletheia-ffi.so` into C, C++, and Go projects.

**Prerequisites**: Build Aletheia first following [BUILDING.md](BUILDING.md). The `dist` target requires `patchelf` (see below).

## Building the Distribution

```bash
# patchelf is required for RPATH patching
# Debian/Ubuntu: sudo apt install patchelf
# Fedora: sudo dnf install patchelf
# Or download from https://github.com/NixOS/patchelf/releases

cabal run shake -- dist
```

This produces:

```
dist/
├── aletheia/
│   ├── lib/
│   │   ├── libaletheia-ffi.so          # Main library (Agda core)
│   │   ├── libHS*.so                   # GHC runtime libraries
│   │   └── libffi.so.*                 # libffi (bundled from GHC)
│   └── include/
│       └── aletheia.h                  # C API header
└── aletheia.tar.gz                     # Compressed tarball
```

All `.so` files are stripped (`--strip-unneeded`) and set to `RPATH=$ORIGIN` for self-contained dependency resolution. No `LD_LIBRARY_PATH` needed.

**Why `--strip-unneeded`?** Using `--strip-all` would remove the C export symbols (`aletheia_init`, `aletheia_process`, etc.) needed by `dlsym`. `--strip-unneeded` preserves these while removing debug symbols.

### System dependencies (not bundled)

See [DEPENDENCIES.md](../../DEPENDENCIES.md) for the complete list with licenses. In brief, only `libgmp` needs explicit installation — the rest are universally present:

| Library | Package (Debian/Ubuntu) | Package (Fedora) |
|---------|------------------------|-------------------|
| `libc`, `libm`, `libpthread` | `libc6` (always present) | `glibc` (always present) |
| `libgmp` | `libgmp10` | `gmp-libs` |

If you see `error while loading shared libraries: libgmp.so.10: cannot open shared object file`, install the package above.

## RPATH

Every `.so` in the dist has `RPATH=$ORIGIN`, so dependencies resolve within the same directory. Verify with:

```bash
patchelf --print-rpath dist/aletheia/lib/libaletheia-ffi.so
# Output: $ORIGIN

ldd dist/aletheia/lib/libaletheia-ffi.so | grep "not found"
# No output = all dependencies resolved
```

If `patchelf` was not installed during `cabal run shake -- dist`, RPATH won't be set and you must use `LD_LIBRARY_PATH` instead:
```bash
LD_LIBRARY_PATH=/path/to/aletheia/lib ./my_app
```

## Integration Guide

### Feature availability per binding

All bindings share the same Agda core and JSON protocol, but surface coverage differs. The authoritative feature matrix lives in the [Interface Guide § Binding parity](../reference/INTERFACES.md#binding-parity); the highlights are:

| Feature | C | Python | C++ | Go |
|---|---|---|---|---|
| Raw JSON FFI (`aletheia_process`) | ✅ | ✅ | ✅ | ✅ |
| Binary `aletheia_send_frame` hot path | ✅ | ✅ | ✅ | ✅ |
| Check API fluent interface | — | ✅ | ✅ | ✅ |
| YAML loader | — | ✅ | ✅ | ✅ |
| Excel loader | — | ✅ | ✅ | ✅ (separate `go/excel/` module) |
| DBC JSON input | ✅ | ✅ | ✅ | ✅ |
| DBC text (`.dbc`) parsing | — | ✅ | ✅ | ✅ |

C consumers get the raw JSON/binary FFI surface — higher-level conveniences (Check API, loaders, DBC text parsing) live in the language bindings.

### Deploying the Library

Unpack the tarball anywhere — no fixed installation path:

```bash
tar xzf aletheia.tar.gz -C /opt/
# Result: /opt/aletheia/lib/ and /opt/aletheia/include/
```

Or vendor it inside your project:

```
my-project/
├── third-party/
│   └── aletheia/
│       ├── lib/
│       │   ├── libaletheia-ffi.so
│       │   └── libHS*.so
│       └── include/
│           └── aletheia.h
└── src/
    └── main.c
```

### C

#### Compile and link

```bash
gcc -I/path/to/aletheia/include \
    -L/path/to/aletheia/lib \
    -Wl,-rpath,/path/to/aletheia/lib \
    -laletheia-ffi \
    -o my_app main.c
```

The `-Wl,-rpath` flag embeds the library path in the binary, eliminating `LD_LIBRARY_PATH` at runtime.

#### Relative RPATH (relocatable binary)

If you ship your binary alongside the library:

```
my-deploy/
├── bin/
│   └── my_app
└── lib/
    ├── libaletheia-ffi.so
    └── libHS*.so
```

Use `$ORIGIN` to make the `my-deploy/` directory relocatable:

```bash
gcc -Ialetheia/include \
    -Laletheia/lib \
    -Wl,-rpath,'$ORIGIN/../lib' \
    -laletheia-ffi \
    -o bin/my_app main.c
```

#### Minimal C example

See `aletheia.h` for complete function documentation. For the JSON command/response format, see the [JSON Protocol](../architecture/PROTOCOL.md).

```c
#include "aletheia.h"
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    hs_init(NULL, NULL);  /* GHC RTS init — once per process, before any aletheia_* call */

    void *session = aletheia_init();
    char *response = aletheia_process(session,
        "{\"type\":\"command\",\"command\":\"parseDBC\",\"dbc\":{\"messages\":[]}}");
    printf("%s\n", response);

    aletheia_free_str(response);
    aletheia_close(session);
    /* Do NOT call hs_exit() — GHC RTS does not support reinitialization */
    return 0;
}
```

`aletheia_process()` handles JSON commands (parseDBC, setProperties, startStream, etc.). To send CAN data frames during streaming, use `aletheia_send_frame()` — a separate binary entry point that passes frame components as C values. See `aletheia.h` for the full signature and [PROTOCOL.md](../architecture/PROTOCOL.md) for details.

### C++ (with the aletheia-cpp binding)

The C++ binding (`cpp/` in the Aletheia repository) uses `dlopen` at runtime — pass the `.so` path to `make_ffi_backend()`. Requires CMake 3.25+ and a C++23 compiler (g++ 14+ or clang 21+).

#### CMake integration

```cmake
# Option 1: FetchContent (source embedded in your project tree)
FetchContent_Declare(aletheia-cpp
    SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/third-party/aletheia-cpp)
FetchContent_MakeAvailable(aletheia-cpp)
target_link_libraries(my_app PRIVATE aletheia-cpp)

# Option 2: find_package (after cmake --install from the aletheia-cpp build)
find_package(aletheia-cpp REQUIRED)
target_link_libraries(my_app PRIVATE aletheia::aletheia-cpp)
```

#### Usage

```cpp
// Functional equivalent of Go's NewFFIBackend + NewClient and Python's
// AletheiaClient(ffi_path=...). All three load the same libaletheia-ffi.so
// via dlopen and hand off to the same verified Agda core.
#include <aletheia/client.hpp>
#include <aletheia/backend.hpp>

int main() {
    auto backend = aletheia::make_ffi_backend("/opt/aletheia/lib/libaletheia-ffi.so");
    auto client = aletheia::AletheiaClient{std::move(backend)};
    // ... use client (see JSON Protocol docs for commands) ...
}
```

The GHC runtime `.so` files are found automatically via `RPATH=$ORIGIN` on `libaletheia-ffi.so`.

### Go

The Go binding (`go/` in the Aletheia repository) uses `dlopen` at runtime via cgo. Requires Go 1.24+ and `CGO_ENABLED=1`.

#### Install

```bash
go get github.com/aletheia-automotive/aletheia-go/aletheia
```

#### Usage

```go
// Functional equivalent of C++'s make_ffi_backend + AletheiaClient and
// Python's AletheiaClient(ffi_path=...). All three load the same
// libaletheia-ffi.so via dlopen and hand off to the same verified Agda core.
package main

import "github.com/aletheia-automotive/aletheia-go/aletheia"

func main() {
    backend, err := aletheia.NewFFIBackend("/opt/aletheia/lib/libaletheia-ffi.so")
    if err != nil {
        panic(err)
    }
    client, err := aletheia.NewClient(backend)
    if err != nil {
        panic(err)
    }
    defer client.Close()
    // ... use client (see JSON Protocol docs for commands) ...
}
```

#### Build

```bash
CGO_ENABLED=1 go build ./...
```

`CGO_ENABLED=1` is required because the Go binding uses cgo to call `dlopen`/`dlsym` from `<dlfcn.h>`.

### Docker

Two Dockerfiles are provided in the repository root:

| File | Purpose | Base image |
|------|---------|------------|
| `Dockerfile` | Build from source (CI/CD) | `haskell:9.6.7` → `python:3.13-slim` |
| `Dockerfile.runtime` | Runtime from pre-built dist | `python:3.13-slim` |

```bash
# Build runtime image from pre-built dist (fast)
cabal run shake -- dist
docker build -t aletheia:runtime -f Dockerfile.runtime .

# Or use the Shake target (runs dist + docker build)
cabal run shake -- docker

# Use as a base image for your project
docker run --rm aletheia:runtime python3 -c \
  "from aletheia import AletheiaClient; print('OK')"
```

For C/C++/Go consumers who don't need Python, use the dist tarball with a minimal base image:

```dockerfile
FROM debian:bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends libgmp10 && rm -rf /var/lib/apt/lists/*
COPY dist/aletheia /opt/aletheia
ENV ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so
```

See [BUILDING.md § Docker](BUILDING.md#docker) for the full from-source build option.

## Library Loading: dlopen vs Link-Time

| Approach | Used by | How it finds the .so |
|----------|---------|---------------------|
| **Link-time** (`-laletheia-ffi`) | C | `-L` at compile time + `RPATH` at runtime |
| **dlopen** (runtime) | C++, Go, Python | Full path passed to `dlopen()` |

C++ and Go use `dlopen` because they wrap the FFI through a `Backend` interface that abstracts the loading mechanism, enabling mock backends for testing without a real `.so`.

For all `dlopen` consumers, the only input is the **path to `libaletheia-ffi.so`**. The bundled GHC `.so` files are found via `RPATH=$ORIGIN`.

## Thread Safety

See `aletheia.h` for the authoritative specification. In summary:

- **hs_init**: Once per process, before any `aletheia_*` call. Never call `hs_exit()`.
- **aletheia_init/close**: Can be called from any thread.
- **aletheia_process**: One thread per session handle. Different sessions may run concurrently.
- **aletheia_send_frame**: Same constraint — one thread per session handle.

## Troubleshooting

**`dlopen failed: libaletheia-ffi.so: cannot open shared object file`**
Verify the path exists: `ls -la /path/to/lib/libaletheia-ffi.so`

**`error while loading shared libraries: libgmp.so.10`**
Install libgmp: `sudo apt install libgmp10` (Debian/Ubuntu) or `sudo dnf install gmp-libs` (Fedora).

**`dlsym failed for aletheia_init: undefined symbol`**
The `.so` was stripped too aggressively. Rebuild with `cabal run shake -- dist` (uses `--strip-unneeded`, not `--strip-all`).

**Segmentation fault on first `aletheia_*` call**
`hs_init()` was not called. It must be called exactly once before any other Aletheia function.

**GHC `.so` files not found (ldd shows "not found")**
`patchelf` was not installed during `cabal run shake -- dist`. Either reinstall patchelf and re-run dist, or set `LD_LIBRARY_PATH` to the `lib/` directory.

## Why Multiple .so Files?

GHC's pre-compiled static archives (`.a`) lack `-fPIC`, preventing them from linking into shared libraries on x86-64 Linux. The GHC runtime libraries are therefore shipped as separate `.so` files with `RPATH=$ORIGIN`. A single-file `.so` would require rebuilding GHC with `-fPIC`, which is fragile and unmaintainable.

Only dynamic linking is supported. Static linking against `libaletheia-ffi` is not possible due to this GHC constraint.
