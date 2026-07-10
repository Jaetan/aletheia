# Dependencies and Licenses

**Last Updated**: 2026-07-07

This document lists all third-party software Aletheia depends on, their licenses,
and the resulting obligations when distributing Aletheia.

**Optional opt-in tooling not listed below**: `actionlint` (MIT), `act` (MIT) for
the GHA meta-checks described in [docs/development/CI_LOCAL.md](docs/development/CI_LOCAL.md);
`mutmut` (BSD-3), `gremlins` (Apache-2.0), `Mull` (MIT) for the mutation-testing
lane described in [docs/operations/MUTATION.md](docs/operations/MUTATION.md). These
are dev-only and are NOT linked into `libaletheia-ffi.so`, so they create no
distribution obligation.

Aletheia itself is licensed under **BSD-2-Clause** (see [LICENSE.md](LICENSE.md)).

---

## Build-Time Only

These tools are used to compile Aletheia but are **not** present in the distributed artifact.

| Dependency | Version | License | Role |
|---|---|---|---|
| Agda | 2.8.0 | MIT | Compiler (Agda → Haskell via MAlonzo) |
| Agda standard library | 2.3 | MIT | Type-checked at compile time |
| GHC | 9.6.7 | BSD-3-Clause | Compiler (Haskell → machine code) |
| Shake | ≥ 0.19 | BSD-3-Clause | Build orchestration |
| setuptools | ≥ 82.0.1 | MIT | Python build backend |
| wheel | — | MIT | Python wheel packaging |

**Obligations**: None for downstream users. These tools are not redistributed
with Aletheia.

---

## Runtime — Haskell Layer (`libaletheia-ffi.so`)

The compiled shared library links against these Haskell and system libraries.

### Haskell packages (bundled as .so files with RPATH=$ORIGIN)

| Package | Version | License |
|---|---|---|
| GHC RTS | 1.0.2 | BSD-3-Clause |
| base | 4.18.3.0 | BSD-3-Clause |
| ghc-prim | 0.10.0 | BSD-3-Clause |
| ghc-bignum | 1.3 | BSD-3-Clause |
| text | 2.0.2 | BSD-2-Clause |
| binary | 0.8.9.1 | BSD-3-Clause |
| containers | 0.6.7 | BSD-3-Clause |
| bytestring | 0.11.5.4 | BSD-3-Clause |
| array | 0.5.8.0 | BSD-3-Clause |
| deepseq | 1.4.8.1 | BSD-3-Clause |
| pretty | 1.1.3.6 | BSD-3-Clause |
| template-haskell | 2.20.0.0 | BSD-3-Clause |
| ghc-boot-th | 9.6.7 | BSD-3-Clause |

### System libraries (dynamically linked)

| Library | License | Notes |
|---|---|---|
| **libgmp** | **LGPL-3.0+** | Arbitrary-precision arithmetic (used by ghc-bignum) |
| libffi | MIT | Foreign function interface |
| glibc (libc, libm, libpthread, librt, libdl) | LGPL-2.1+ | C standard library |

---

## Runtime — C++ Layer

The C++ binding (`cpp/`) wraps `libaletheia-ffi.so` via `dlopen`. It has no runtime dependencies beyond the system C++ standard library.

### Build-time dependencies (fetched automatically via CMake FetchContent)

| Package | Version | License | Purpose |
|---|---|---|---|
| nlohmann/json | 3.11.3 | MIT | JSON serialization/deserialization |
| yaml-cpp | 0.8.0 | MIT | YAML check-rule loader (statically linked into the C++ binding) |
| OpenXLSX | master (commit `5723411`, 2025-07-14) | BSD-3-Clause | Excel template loader (statically linked into the C++ binding) |
| Catch2 | 3.7.1 | BSL-1.0 | Unit testing (test-only, not shipped) |

Requires CMake 3.25+ and **Clang 22** with a C++23 libstdc++/libc++ (`<expected>`, `<format>`); see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy) for the full compiler policy.

---

## Runtime — Go Layer

The Go binding (`go/`) wraps `libaletheia-ffi.so` via cgo + `dlopen`.

### Third-party Go dependencies

| Package | Version | License | Pulled in by |
|---|---|---|---|
| gopkg.in/yaml.v3 | v3.0.1 | MIT | `go/aletheia` (YAML check-rule loader) |
| github.com/xuri/excelize/v2 | v2.10.1 | BSD-3-Clause | `go/excel` (optional module — Excel template loader) |

The optional `go/excel` module is a separate Go module so the heavy `excelize`
dependency (and its transitive `golang.org/x/{crypto,net,text}`, `richardlehane/{mscfb,msoleps}`,
`tiendc/go-deepcopy`, `xuri/{efp,nfp}` chain) is not imposed on consumers of the
core `go/aletheia` module.

### System dependencies

| Dependency | Purpose |
|---|---|
| cgo (`CGO_ENABLED=1`) | C interop for `dlopen`/`dlsym` calls |
| libdl (`-ldl`) | Dynamic loader (part of glibc, always present) |

Requires Go 1.24+.

---

## Runtime — Rust Layer

The Rust binding (`rust/`) wraps `libaletheia-ffi.so` via the `libloading` crate
(runtime `dlopen`/`dlsym`). Its crate dependencies (from `rust/Cargo.toml`):

| Crate | Version pin | License | Role |
|---|---|---|---|
| libloading | 0.8 | ISC | Runtime `dlopen` of `libaletheia-ffi.so` |
| serde_json | 1 | MIT OR Apache-2.0 | JSON protocol serialization/deserialization |
| yaml-rust2 | 0.10 | MIT OR Apache-2.0 | YAML check-rule loader (optional `yaml` feature, on by default) |
| futures-channel | 0.3 | MIT OR Apache-2.0 | Async client reply channel (optional `async` feature) |
| futures-util | 0.3 | MIT OR Apache-2.0 | Stream combinators for the lazy async batch send (optional `async` feature) |

`serde` (MIT OR Apache-2.0) is pulled in transitively by `serde_json`.
Dev-only (test/bench, not shipped): `futures` 0.3 and `yaml-rust2` 0.10.

Requires the Rust 2021 edition toolchain.

---

## Runtime — Python Layer

### Optional dependencies (from `pyproject.toml` extras)

| Package | Version | License |
|---|---|---|
| openpyxl | ≥ 3.1.5 | MIT |
| **python-can** | **≥ 4.6.1** | **LGPL-3.0-only** |
| pyyaml | ≥ 6.0.3 | MIT |

(cantools was dropped 2026-05-03 in `2daa2fb` — DBC parsing now goes through the verified Agda kernel via the FFI; no Python dep required.)

### Transitive dependencies

| Package | License | Pulled in by |
|---|---|---|
| et_xmlfile | MIT | openpyxl |
| packaging | Apache-2.0 / BSD | python-can |
| typing_extensions | PSF-2.0 | python-can |
| wrapt | BSD | python-can |

---

## License Obligations Summary

### Permissive licenses (MIT, BSD-2-Clause, BSD-3-Clause, Apache-2.0, ISC, PSF-2.0)

All permissive-licensed dependencies require only:
- **Attribution**: include the original copyright notice and license text when
  redistributing (typically in a NOTICES or LICENSE file alongside the distribution).

No restrictions on use, modification, or proprietary distribution.

### LGPL-3.0 (libgmp, python-can)

Two runtime dependencies use LGPL-3.0 (libgmp uses LGPL-3.0-or-later; python-can uses LGPL-3.0-only). The key obligations are:

1. **Dynamic linking**: Users must be able to replace the LGPL component with a
   modified version. This is satisfied automatically — libgmp is dynamically linked
   (via `ldd`), and python-can is a Python package imported at runtime.

2. **Source availability**: Recipients of a binary distribution must be able to
   obtain the source code of the LGPL components (libgmp, python-can). Pointing
   to the upstream repositories satisfies this:
   - libgmp: https://gmplib.org/
   - python-can: https://github.com/hardbyte/python-can

3. **License notice**: Include the LGPL-3.0 license text (or a reference to it)
   alongside the distribution.

4. **No effect on Aletheia's own code**: LGPL does not require Aletheia's
   BSD-2-Clause source code to be disclosed. The LGPL "weak copyleft" applies
   only to the LGPL library itself, not to code that uses it through its public API.

### glibc (LGPL-2.1+)

Standard system library present on all Linux installations. Dynamic linking
(confirmed via `ldd`) satisfies the LGPL requirements. No special action needed
beyond what any Linux application already provides.
