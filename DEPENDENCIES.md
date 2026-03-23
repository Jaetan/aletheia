# Dependencies and Licenses

**Last Updated**: 2026-03-23

This document lists all third-party software Aletheia depends on, their licenses,
and the resulting obligations when distributing Aletheia.

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
| setuptools | ≥ 61.0 | MIT | Python build backend |
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
| Catch2 | 3.7.1 | BSL-1.0 | Unit testing (test-only, not shipped) |

Requires CMake 3.25+ and a C++23 compiler (g++ 14+ or clang 21+).

---

## Runtime — Go Layer

The Go binding (`go/`) wraps `libaletheia-ffi.so` via cgo + `dlopen`. It has no third-party Go dependencies.

### System dependencies

| Dependency | Purpose |
|---|---|
| cgo (`CGO_ENABLED=1`) | C interop for `dlopen`/`dlsym` calls |
| libdl (`-ldl`) | Dynamic loader (part of glibc, always present) |

Requires Go 1.23+.

---

## Runtime — Python Layer

### Direct dependencies (from `pyproject.toml`)

| Package | Version | License |
|---|---|---|
| cantools | ≥ 39.0 | MIT |
| openpyxl | ≥ 3.1 | MIT |
| **python-can** | **≥ 4.0** | **LGPL-3.0-only** |
| pyyaml | ≥ 6.0 | MIT |

### Transitive dependencies

| Package | License | Pulled in by |
|---|---|---|
| argparse-addons | MIT | cantools |
| bitstruct | MIT | cantools |
| crccheck | MIT | cantools |
| diskcache | Apache-2.0 | cantools |
| textparser | MIT | cantools |
| et_xmlfile | MIT | openpyxl |
| packaging | Apache-2.0 / BSD | python-can |
| typing_extensions | PSF-2.0 | python-can |
| wrapt | BSD | python-can |

---

## License Obligations Summary

### Permissive licenses (MIT, BSD-2-Clause, BSD-3-Clause, Apache-2.0, PSF-2.0)

All permissive-licensed dependencies require only:
- **Attribution**: include the original copyright notice and license text when
  redistributing (typically in a NOTICES or LICENSE file alongside the distribution).

No restrictions on use, modification, or proprietary distribution.

### LGPL-3.0 (libgmp, python-can)

Two runtime dependencies use LGPL-3.0. The key obligations are:

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
