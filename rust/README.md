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

## Surface

A **typed client** over one stream in the verified core:

- **Validated value types** — `CanId` (an enum of 11-bit `Standard` / 29-bit
  `Extended`), `Dlc`, `Rational`, `Timestamp`, `TimeBound` — each rejects
  out-of-range input at construction (`Result`), mirroring the Go and C++
  bindings' newtype discipline.
- **LTL** — `Predicate` and `Formula` are native, exhaustively-matchable Rust
  enums (no sealed-interface ceremony) that serialize to the exact wire shape the
  Agda core accepts.
- **`Client`** — load a DBC (`parse_dbc_text`), bind properties
  (`set_properties`), then stream frames through the **binary FFI**
  (`start_stream` / `send_frame` / `send_error` / `send_remote` / `end_stream`)
  and extract signals (`extract_signals`) — the same fast path the other bindings
  use in production. `process` remains as a raw JSON escape hatch.

The two ownership rules that cgo hides from the Go binding are enforced here:

- **GHC-allocated return strings** are copied out and released with
  `aletheia_free_str` (never `CString::from_raw`, which would hand RTS memory to
  Rust's allocator). A RAII guard makes this impossible to skip per call site.
- **The RTS is initialised once** for the process (latched in a `OnceLock`) and
  never torn down (`hs_exit` does not support re-initialisation).

`Client` holds a raw `StreamState` pointer, so it is intentionally
`!Send + !Sync`. The typed DBC document model, the Check DSL, client-side
violation enrichment, and CLI affordances are tracked as `planned` in the `rust`
column of [`docs/FEATURE_MATRIX.yaml`](../docs/FEATURE_MATRIX.yaml); a Rust
parity gate (`tests/feature_matrix.rs`) keeps that column honest.

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
