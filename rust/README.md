<!--
SPDX-FileCopyrightText: 2025 Nicolas Pelletier
SPDX-License-Identifier: BSD-2-Clause
-->

# Aletheia — Rust binding

Rust binding for Aletheia, the formally verified CAN frame analysis core.

Like the **Go** and **C++** bindings, this crate loads the GHC-compiled Agda core
`libaletheia-ffi.so` at runtime via `dlopen` (the [`libloading`] crate) rather
than statically linking the GHC RTS + MAlonzo into a non-Haskell binary. All the
verified logic lives in the shared library; this crate is a thin, memory-safe
wrapper over its stable C ABI. (The **Haskell** binding, by contrast, is *native*
— it calls the Agda-compiled core in-process with no `.so` and no FFI.)

## Status

This is the **tracer-bullet slice**. It proves the FFI lifecycle end-to-end —
load → GHC RTS init (once) → one `aletheia_process` JSON round-trip → free →
close — and the two ownership rules that cgo hides from the Go binding:

- **GHC-allocated return strings** are copied out and released with
  `aletheia_free_str` (never `CString::from_raw`, which would hand RTS memory to
  Rust's allocator). A RAII guard makes this impossible to skip per call site.
- **The RTS is initialised once** for the process via `std::sync::Once` and never
  torn down (`hs_exit` does not support re-initialisation).

The typed client surface (validated CAN ID / DLC newtypes, sealed predicate /
formula enums, the binary frame endpoints) lands in subsequent slices, tracked
by the `rust` column of [`docs/FEATURE_MATRIX.yaml`](../docs/FEATURE_MATRIX.yaml).

## Build & test

The crate locates the shared library through the `ALETHEIA_LIB` environment
variable (the same discovery the C++ and Python harnesses use). Build the core
first (`cabal run shake -- build` from the repo root produces
`build/libaletheia-ffi.so`), then:

```sh
cd rust
ALETHEIA_LIB=../build/libaletheia-ffi.so cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check
```

`tools/run_ci.py` runs exactly these as a required lane.

[`libloading`]: https://crates.io/crates/libloading
