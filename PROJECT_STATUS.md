# Aletheia Project Status

**Last Updated**: 2026-07-16.

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

1. **Prebuilt / installable distribution** — the leading adoption blocker,
   **shipped in v4.0.0 (2026-07-17)**. Previously the only way to obtain Aletheia
   was a full from-source `Agda → Haskell → libaletheia-ffi.so` build; now a
   **GitHub Release carries a self-contained, cosign-signed `.tar.gz` bundle** the
   user downloads and is productive with in minutes — not a pip wheel (native
   `.deb` / `.rpm` packages follow as a later step below). A real-downloader walk
   confirmed the full path end-to-end: download → verify (`sha256` + `cosign`) →
   `install.sh` → `pip install --target` → `source env.sh` → run a real LTL
   verification, on a clean interpreter. Delivered:
   - **✅ Release automation (done).** A tag-triggered workflow builds the
     reproducible tarball, **keyless-signs** it (Sigstore via the GitHub Actions
     OIDC identity — no signing key in CI), self-verifies the signature (publish
     is gated on that check), and publishes a draft Release.
   - **✅ Multi-binding payload (done).** The bundle now carries all four language
     bindings (Python / C++ / Go / Rust — each binding's library files over the one
     prebuilt `.so`), plus `env.sh` / `env.fish` (which export an absolute
     `ALETHEIA_LIB`) and `install.sh` / `install.fish` (which print the per-shell
     and per-language wiring steps without editing any startup file). All four
     bindings resolve the library from `ALETHEIA_LIB`, so one download makes every
     binding usable after a single `source env.sh`. A `dist` self-check and a
     release-workflow smoke test guard the bundle's contents.
   - **Remaining — do next (distribution hardening):**
     - **Native packages + Docker.** Native OS packages (`.deb` / `.rpm`) attached
       to the Release, and a multi-binding Docker image (extend `Dockerfile.runtime`
       / `shake docker` past today's Python-only consumer).
     - **Always-on bundle-staging gate.** A fast gate that `bash -n` / `fish -n`s
       the packaging scripts and asserts every `git archive` pathspec resolves to a
       tracked file, so bundle staging cannot silently rot between releases — today
       the `dist` self-check only fires when `dist` actually runs.
     - **SBOM covers the bundled binding sources**, not just the `.so` + GHC deps.
     - **Real-workflow validation in C++ / Go / Rust** from the bundle. Python is
       proven end-to-end (the real-downloader walk ran a real LTL verification); the
       other three are verified to load the `.so` but not yet exercised on a full
       workflow from the published artifact.
2. **`aletheia template <file>.xlsx` CLI subcommand.** A true no-code way to obtain
   the Excel template (today it needs a Python one-liner), so the non-programmer
   on-ramp is real.
3. **Go CAN-log reader.** Bring the `aletheia check … <log>` streaming command to
   Go for full CLI parity (it is Python-only today).

**Candidate tracks.** A native Haskell binding (the core is already Haskell, so it
needs no FFI); a python-can replacement (verified CAN-log readers for
ASC / BLF / MF4); a GHC `--bignum=native` rebuild to drop the libgmp LGPL
dependency; and SOME/IP support for automotive Ethernet.

**DBC text round-trip guarantee.**
`format_dbc_text` is always-strict: it returns `.dbc` text that provably
re-parses to the input DBC, or a typed `handler_text_roundtrip_failed` refusal —
machine-checked (`formatDBCTextResult-sound`), across all four bindings. Every
caller sees a result that is either provably faithful or explicitly refused,
never silently lossy. Two heavier capabilities remain deferred, off the critical
path: emitting the currently-lossy constructs (e.g. multi-value multiplexing)
without loss, and a stronger validator.

Living detail and rationale for the above live in
[`docs/development/DEFERRED_ITEMS.md`](docs/development/DEFERRED_ITEMS.md) and the
project memory notes.
