# Distributing Aletheia

---
**Version**: 4.0.0 (canonical sources: `haskell-shim/aletheia.cabal` `version:` field and `python/pyproject.toml` `version =` field — update those when bumping)
**Last Updated**: 2026-07-19
**Platform**: Linux x86-64 only
---

> **New to Aletheia?** The fastest path is a **release bundle**: one tarball with the verified library and all four language wrappers (Python, C++, Go, Rust), usable after a single `source env.sh`. See [Using a release bundle](#using-a-release-bundle). The per-language sections further down are the in-depth integration reference (explicit `.so`-path constructors, RPATH, Docker).

How to package, distribute, and integrate Aletheia — the self-contained release bundle, and `libaletheia-ffi.so` directly into C, C++, Go, and Rust projects.

## Using a release bundle

A GitHub release ships one self-contained tarball — `aletheia.tar.gz` — that carries the verified library **and** all four language wrappers. Download it, verify it ([RELEASE.md § Verifying release artifacts](RELEASE.md#verifying-release-artifacts-consumer-side)), unpack it anywhere, and you are ready to use Aletheia from Python, C++, Go, or Rust in minutes — no Agda or GHC toolchain required.

Every release is validated this way before it is published: the release workflow builds one consumer program per compiled binding (C++, Go, Rust) from the exact recipes `install.sh` / `install.fish` print and drives a real verification scenario through the bundle's kernel, alongside a Python smoke test of the same `env.sh` → `ALETHEIA_LIB` chain. A weekly scheduled workflow replays the same validation against both a fresh `shake dist` from the default branch and the latest published release. See [RELEASE.md § Release-path bundle validation](RELEASE.md#release-path-bundle-validation).

```
aletheia/
├── lib/libaletheia-ffi.so      # verified Agda kernel + GHC runtime (RPATH=$ORIGIN)
├── lib/libHS*.so               # GHC runtime dependencies
├── include/aletheia.h          # C ABI header (C / C++-via-C consumers)
├── bindings/
│   ├── python/                 # pure-ctypes package (pip install)
│   ├── cpp/                    # CMake wrapper (add_subdirectory)
│   ├── go/                     # Go module (cgo + dlopen)
│   └── rust/                   # Rust crate (dlopen)
├── env.sh   env.fish           # source to export ALETHEIA_LIB (absolute path)
├── install.sh   install.fish   # print the shell + per-language wiring steps
├── MANIFEST.txt                # toolchain pin + per-artifact SHA-256 hashes
├── README.txt                  # consumer entry point
├── aletheia-sbom.cdx.json      # CycloneDX 1.5 SBOM
└── LICENSE.md                  # BSD-2-Clause license text
```

Why source and not just a header + `.so`? For C there is nothing more to ship — `include/aletheia.h` + `lib/libaletheia-ffi.so` is the whole interface. But Python, Go, and Rust have no header/compiled-lib split: their libraries *are* source (a pure-ctypes package, a Go module, a Rust crate). The `bindings/` trees carry each wrapper in its only distributable form — library files only, no tests or benchmarks.

### 1. Make the library discoverable

Every binding locates `libaletheia-ffi.so` at runtime through the `ALETHEIA_LIB` environment variable. `env.sh` / `env.fish` set it to an **absolute** path derived from the script's own location, so the value is correct no matter where you unpacked:

```bash
# bash / zsh — for this shell, or add the line to ~/.bashrc / ~/.zshrc:
source /path/to/aletheia/env.sh
```
```fish
# fish — for this shell, or add the line to ~/.config/fish/config.fish:
source /path/to/aletheia/env.fish
```

Running `./install.sh` (or `./install.fish`) prints exactly these lines for your unpack location plus the per-language recipes below. It does **not** edit your shell startup files — you stay in control.

### 2. Wire it into your language

Each recipe assumes `ALETHEIA_LIB` is set (step 1); `<A>` is the unpack path.

**Python** (requires **Python 3.14+**; no third-party runtime dependencies). Into a virtual environment you have created and activated, `pip install <A>/bindings/python`. With no venv — including on an externally-managed / [PEP 668](https://peps.python.org/pep-0668/) Python, where a plain `pip install` into the system environment is refused — install into an isolated directory and put it on `PYTHONPATH`:

```bash
pip install --target "$HOME/.local/lib/aletheia" "<A>/bindings/python"
export PYTHONPATH="$HOME/.local/lib/aletheia"   # fish: set -gx PYTHONPATH "$HOME/.local/lib/aletheia"
python -c 'import aletheia; from aletheia import FFIBackend; FFIBackend()'
```

**C++** (CMake; fetches nlohmann/json + yaml-cpp + OpenXLSX at configure time, so a network connection is required for the first configure):

```cmake
add_subdirectory("<A>/bindings/cpp" aletheia-cpp)
target_link_libraries(your_app PRIVATE aletheia::aletheia-cpp)
```

**Go** — the bundled module is standalone: it ships **no** `go.work` (a stray `go.work` would hijack your own module resolution). Add it with a `replace`:

```bash
go mod edit -replace "github.com/aletheia-automotive/aletheia-go=<A>/bindings/go"
go get github.com/aletheia-automotive/aletheia-go/aletheia
```

**Rust**:

```toml
[dependencies]
aletheia = { path = "<A>/bindings/rust" }
```

The per-language **reference** sections below cover each API surface, the explicit `.so`-path constructors, RPATH, and Docker in depth.

## Installing from a native package (.deb / .rpm)

Each release also ships the bundle as native Linux packages — `aletheia_<version>_amd64.deb` and `aletheia-<version>-1.x86_64.rpm`, where `<version>` is the four-component cabal form (e.g. `4.0.0.0` for release v4.0.0). Both install the **exact payload of `aletheia.tar.gz`** to `/opt/aletheia` — deliberately not `/usr/lib`: the bundle carries its own GHC runtime `.so` closure (`RPATH=$ORIGIN`), which must never land where it could shadow distro-managed libraries. x86-64 Linux only, as stated in the package metadata.

The only declared dependency beyond glibc is the GMP runtime: `libgmp10` (deb) / the `libgmp.so.10()(64bit)` soname (rpm — a soname rather than a package name, because the owning package differs across rpm distros: Fedora/RHEL ship it as `gmp`, openSUSE as `gmp-libs`).

Download a package with its sidecars from the GitHub Release, verify, install:

```bash
BASE=https://github.com/Jaetan/aletheia/releases/download/vX.Y.Z
PKG=aletheia_<version>_amd64.deb          # rpm: aletheia-<version>-1.x86_64.rpm
curl -fsSLO "$BASE/$PKG";     curl -fsSLO "$BASE/$PKG.sha256"
curl -fsSLO "$BASE/$PKG.sig"; curl -fsSLO "$BASE/$PKG.crt"

sha256sum -c "$PKG.sha256"
cosign verify-blob \
  --certificate "$PKG.crt" --signature "$PKG.sig" \
  --certificate-identity-regexp \
    '^https://github\.com/Jaetan/aletheia/\.github/workflows/release\.yml@refs/tags/v' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  "$PKG"

sudo dpkg -i "$PKG"                              # Debian/Ubuntu
# sudo rpm -i aletheia-<version>-1.x86_64.rpm    # RPM distros
```

Environment wiring stays **strictly opt-in**: the packages run no maintainer scripts and install no `profile.d` drop-ins. Activate per shell exactly as with the tarball —

```bash
source /opt/aletheia/env.sh    # bash/zsh (fish: source /opt/aletheia/env.fish)
```

— then follow [step 2 of the bundle instructions](#2-wire-it-into-your-language) with `<A>` = `/opt/aletheia`.

Uninstall:

```bash
sudo dpkg -r aletheia          # Debian/Ubuntu
# sudo rpm -e aletheia         # RPM distros
```

Before publish, CI install-smokes every release's `.deb` for real — `dpkg -i`, `source /opt/aletheia/env.sh` from a foreign cwd, a kernel load through the packaged Python binding, clean `dpkg -r` — and structurally checks the `.rpm` payload listing; both formats pack the same contents map (`packaging/nfpm.yaml`), so their payloads are identical by construction. See [RELEASE.md § Native packages](RELEASE.md#native-packages-deb--rpm) for the artifact and verification details, including the honest reproducibility scope.

## Building the Distribution

**Prerequisites**: Build Aletheia first following [BUILDING.md](BUILDING.md). The `dist` target requires `patchelf` (see below).

```bash
# patchelf is required for RPATH patching
# Debian/Ubuntu: sudo apt install patchelf
# Fedora: sudo dnf install patchelf
# Or download from https://github.com/NixOS/patchelf/releases

cabal run shake -- dist
```

This produces `dist/aletheia/` — the full bundle (verified library, all four `bindings/`, `env.sh`/`env.fish`, `install.sh`/`install.fish`, `MANIFEST.txt`, SBOM; see [Using a release bundle](#using-a-release-bundle) for the layout) — and the reproducible `dist/aletheia.tar.gz` (with `.sha256`, plus `.sig` and `.crt` when the build is signed). The `bindings/` trees are staged straight from `HEAD` via `git archive` (tracked files only — no build junk, no `go.work`, no tests).

All `.so` files are stripped (`--strip-unneeded`) and set to `RPATH=$ORIGIN` for self-contained dependency resolution. No `LD_LIBRARY_PATH` needed.

**Why `--strip-unneeded`?** Using `--strip-all` would remove the C export symbols (`aletheia_init`, `aletheia_process`, etc.) needed by `dlsym`. `--strip-unneeded` preserves these while removing debug symbols.

### System dependencies (not bundled)

See [DEPENDENCIES.md](../../DEPENDENCIES.md) for the complete list with licenses. In brief, only `libgmp` needs explicit installation — the rest are universally present:

| Library | Package (Debian/Ubuntu) | Package (Fedora) |
|---------|------------------------|-------------------|
| `libc`, `libm`, `libpthread` | `libc6` (always present) | `glibc` (always present) |
| `libgmp` | `libgmp10` | `gmp` |

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

| Feature | C | Python | C++ | Go | Rust |
|---|---|---|---|---|---|
| Raw JSON FFI (`aletheia_process`) | ✅ | ✅ | ✅ | ✅ | ✅ |
| Binary `aletheia_send_frame` hot path | ✅ | ✅ | ✅ | ✅ | ✅ |
| Check API fluent interface | — | ✅ | ✅ | ✅ | ✅ |
| YAML loader | — | ✅ | ✅ | ✅ | ✅ |
| Excel loader | — | ✅ | ✅ | ✅ (separate `go/excel/` module) | ✅ (separate `rust/excel/` crate) |
| DBC JSON input | ✅ | ✅ | ✅ | ✅ | ✅ |
| DBC text (`.dbc`) parsing | — | ✅ | ✅ | ✅ | ✅ |

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

The C++ binding (`cpp/` in the Aletheia repository) uses `dlopen` at runtime — pass the `.so` path to `make_ffi_backend()`. Requires CMake 3.25+ and Clang 22 (the supported toolchain; older may work, unsupported) with a libstdc++/libc++ that supports C++23 (`<expected>`); g++ is not supported.

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

### Rust

The Rust binding (`rust/` in the Aletheia repository) `dlopen`s `libaletheia-ffi.so`
at runtime through the [`libloading`](https://crates.io/crates/libloading) crate. It
resolves the library from the `ALETHEIA_LIB` environment variable (default:
`libaletheia-ffi.so` on the loader path), rather than taking the path as a
constructor argument. See the [Rust API reference](../reference/RUST_API.md) for the
full surface.

#### Cargo dependency

The crate is not published to crates.io; depend on it by git or path:

```toml
[dependencies]
aletheia = { git = "https://github.com/Jaetan/aletheia", package = "aletheia" }
# or, for a local checkout:
# aletheia = { path = "/path/to/aletheia/rust" }
```

#### Usage

```rust
// Functional equivalent of C++'s make_ffi_backend + AletheiaClient and
// Python's AletheiaClient(ffi_path=...). Point ALETHEIA_LIB at the built
// libaletheia-ffi.so, then construct a Client — it loads the same verified
// Agda core via dlopen.
//
//   ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so cargo run
use aletheia::Client;

fn main() {
    let client = Client::new().expect("init client — is ALETHEIA_LIB set?");
    // ... use client (see the Rust API reference for the typed surface) ...
    let _ = client;
}
```

#### Build

```bash
cargo build --release
```

### Docker

#### Pull the published image (GHCR)

Each release pushes a runtime image to GitHub Container Registry, tagged with the release version (`X.Y.Z`, from the `vX.Y.Z` tag) and `latest`, and keyless-signs the image **digest** (tags are movable; the digest is content-addressed):

```bash
docker pull ghcr.io/jaetan/aletheia:X.Y.Z

# Verify the signature against the release workflow identity:
cosign verify \
  --certificate-identity-regexp \
    '^https://github\.com/Jaetan/aletheia/\.github/workflows/release\.yml@refs/tags/v' \
  --certificate-oidc-issuer https://token.actions.githubusercontent.com \
  ghcr.io/jaetan/aletheia:X.Y.Z
```

The image carries the full release bundle at `/opt/aletheia` (verified kernel + GHC runtime closure, C header, all four binding sources, env scripts, MANIFEST, SBOM), has the **bundled** Python binding pre-installed — byte-identical to `/opt/aletheia/bindings/python`, never a separate copy — and presets `ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so`. Python needs no further wiring:

```bash
docker run --rm ghcr.io/jaetan/aletheia:X.Y.Z python3 -c \
  "from aletheia import AletheiaClient; print('OK')"
```

Every image build is gated by throwaway verify stages: the bundled Rust crate and C++ binding (clang-22, the enforced toolchain) must build — and a Go consumer must build **and run** a real LTL scenario — against the image's own `/opt/aletheia`, or the build fails. The stages ship nothing; the image stays slim.

#### C++ / Go / Rust consumer images (`COPY --from`)

The image doubles as a distribution vehicle for compiled-language consumers — `COPY --from` it instead of downloading and unpacking the tarball inside your Dockerfile:

```dockerfile
FROM golang:1.25-trixie AS build
COPY --from=ghcr.io/jaetan/aletheia:X.Y.Z /opt/aletheia /opt/aletheia
WORKDIR /app
COPY . .
RUN go mod edit -replace "github.com/aletheia-automotive/aletheia-go=/opt/aletheia/bindings/go" && \
    go get github.com/aletheia-automotive/aletheia-go/aletheia && \
    CGO_ENABLED=1 go build -o app .

FROM debian:trixie-slim
RUN apt-get update && apt-get install -y --no-install-recommends libgmp10 && rm -rf /var/lib/apt/lists/*
COPY --from=build /opt/aletheia/lib /opt/aletheia/lib
COPY --from=build /app/app /usr/local/bin/app
ENV ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so
CMD ["app"]
```

The same shape serves C++ (`add_subdirectory(/opt/aletheia/bindings/cpp aletheia-cpp)`) and Rust (`aletheia = { path = "/opt/aletheia/bindings/rust" }`): build against the copied bindings, then carry only `/opt/aletheia/lib` plus your binary into the final stage and set `ALETHEIA_LIB`.

#### Building the image locally

Two Dockerfiles are provided in the repository root:

| File | Purpose | Base image |
|------|---------|------------|
| `Dockerfile` | Build from source (CI/CD) | `haskell:9.6.7` → `python:3.14-slim` |
| `Dockerfile.runtime` | Runtime from pre-built dist | `python:3.14-slim` (+ digest-pinned throwaway verify stages) |

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

For C/C++/Go/Rust consumers who don't need Python and build from a local checkout, the dist tree with a minimal base image is still the smallest option:

```dockerfile
FROM debian:trixie-slim
RUN apt-get update && apt-get install -y --no-install-recommends libgmp10 && rm -rf /var/lib/apt/lists/*
COPY dist/aletheia /opt/aletheia
ENV ALETHEIA_LIB=/opt/aletheia/lib/libaletheia-ffi.so
```

## Library Loading: dlopen vs Link-Time

| Approach | Used by | How it finds the .so |
|----------|---------|---------------------|
| **Link-time** (`-laletheia-ffi`) | C | `-L` at compile time + `RPATH` at runtime |
| **dlopen** (runtime) | C++, Go, Rust, Python | An explicit `.so` path, **or** the `ALETHEIA_LIB` env var — all four bindings support both; the release bundle's `env.sh` sets `ALETHEIA_LIB` |

C++, Go, and Rust use `dlopen` because they wrap the FFI through a `Backend` interface that abstracts the loading mechanism, enabling mock backends for testing without a real `.so`.

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
Install libgmp: `sudo apt install libgmp10` (Debian/Ubuntu) or `sudo dnf install gmp` (Fedora).

**`dlsym failed for aletheia_init: undefined symbol`**
The `.so` was stripped too aggressively. Rebuild with `cabal run shake -- dist` (uses `--strip-unneeded`, not `--strip-all`).

**Segmentation fault on first `aletheia_*` call**
`hs_init()` was not called. It must be called exactly once before any other Aletheia function.

**GHC `.so` files not found (ldd shows "not found")**
`patchelf` was not installed during `cabal run shake -- dist`. Either reinstall patchelf and re-run dist, or set `LD_LIBRARY_PATH` to the `lib/` directory.

## Why Multiple .so Files?

GHC's pre-compiled static archives (`.a`) lack `-fPIC`, preventing them from linking into shared libraries on x86-64 Linux. The GHC runtime libraries are therefore shipped as separate `.so` files with `RPATH=$ORIGIN`. A single-file `.so` would require rebuilding GHC with `-fPIC`, which is fragile and unmaintainable.

Only dynamic linking is supported. Static linking against `libaletheia-ffi` is not possible due to this GHC constraint.
