# Aletheia Project Status

**Last Updated**: 2026-07-13.

Aletheia is a formally verified CAN-frame analysis system: a core written in Agda
with machine-checked correctness proofs, compiled to Haskell and exposed through
Python, C++, Go, and Rust APIs. This document tracks the project at the level of
its delivery **phases** — the high-level goals set out for the project. Detail
that changes continuously lives in dedicated surfaces, not here:

- Live cross-binding feature parity — [`docs/FEATURE_MATRIX.yaml`](docs/FEATURE_MATRIX.yaml)
- Open backlog — [`docs/development/DEFERRED_ITEMS.md`](docs/development/DEFERRED_ITEMS.md)
- Performance — [`docs/development/BENCHMARKS.md`](docs/development/BENCHMARKS.md)

## Phases

Phases 1 through 5.1 are ✅ complete; all provable correctness properties are
proven. Phase 6 is planned (a few of its binding items already delivered).

| Phase | Title | Status | Key deliverables |
|---|---|---|---|
| 1   | Core Infrastructure            | ✅ | Agda → MAlonzo → Haskell → Python pipeline; baseline CAN frame analysis. |
| 2A  | LTL Core + Real-World Support  | ✅ | LTL syntax + semantics + coalgebra; signal predicates; DBC integration. |
| 2B  | Streaming Architecture         | ✅ | Incremental LTL stepping; warm-cache reachability; protocol layer. |
| 3   | Verification + Performance     | ✅ | Soundness/adequacy proofs; binary FFI; Bool fast-path. |
| 4   | Production Hardening           | ✅ | Cross-binding parity; mock backends; error taxonomy; structured logging. |
| 5   | Optional Extensions            | ✅ | CAN-FD; C++, Go, and Rust bindings; cross-language benchmarks; verified DBC text parser. |
| 5.1 | Proof Gaps & Spec Observations | ✅ | Closes Phase 4/5 review carryover; the proof obligations are discharged. |
| 6   | Extensions & New Protocols     | Planned | See below. |

## Phase 6 — Extensions & New Protocols (planned)

**Adoption prerequisites — do first.** These gate the rest of Phase 6: the tool
cannot honestly advertise capabilities it does not yet have.

1. **Prebuilt / installable distribution.** Today the only way to obtain Aletheia
   is a full from-source `Agda → Haskell → libaletheia-ffi.so` build — the leading
   adoption blocker. Ship a prebuilt artifact: a manylinux Python wheel bundling
   the shared library (and PyPI publication), and/or an OS package / container.
2. **`aletheia template <file>.xlsx` CLI subcommand.** A true no-code way to obtain
   the Excel template (today it needs a Python one-liner), so the non-programmer
   on-ramp is real.
3. **Go CAN-log reader.** Bring the `aletheia check … <log>` streaming command to
   Go for full CLI parity (it is Python-only today).

**Candidate tracks.** A native Haskell binding (the core is already Haskell, so it
needs no FFI); a python-can replacement (verified CAN-log readers for
ASC / BLF / MF4); a GHC `--bignum=native` rebuild to drop the libgmp LGPL
dependency; and SOME/IP support for automotive Ethernet.

**DBC text round-trip observability (deferred item E.2, re-examined 2026-07-12).**
The proven `parseText ∘ formatText ≡ id` guarantee holds only for a nine-condition
well-formedness class that no user surface can evaluate. Closure routes are
scheduled **(b) ≫ (a) ≫ (c)** with adversarially-reviewed proof strategies in
[`docs/development/E2_PROOF_STRATEGY.md`](docs/development/E2_PROOF_STRATEGY.md);
route (b) (a runtime "round-trips, or tells you it can't" checker) is pinned as a
prerequisite of any future text-export product surface.

Living detail and rationale for the above live in
[`docs/development/DEFERRED_ITEMS.md`](docs/development/DEFERRED_ITEMS.md) and the
project memory notes.
