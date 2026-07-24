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
   - **✅ Distribution hardening (complete, 2026-07-19).** Every follow-up
     shipped, each with an empirically proven failure mode:
     - **Always-on bundle-staging gate** (`check-dist-staging`, also in the
       pre-commit fast tier): every `git archive` pathspec must resolve —
       including `:(exclude)` inner globs, which `git archive` itself passes
       over silently — and the packaging scripts must be tracked and
       syntax-clean (`bash -n` / `fish -n`, fish installed in CI).
     - **SBOM bills the bundled binding sources**: manifest parsers over the
       staged tree (still zero external SBOM tooling), one merged CycloneDX
       document, and a coverage gate that fails the dist on any
       manifest-declared dependency missing from the bill.
     - **Real-workflow validation from the bundle**: a validator executes the
       installers' own printed recipes and drives one consumer per compiled
       binding (C++ / Go / Rust) through a real LTL scenario; it gates
       publish, and the repo's first scheduled workflow re-validates weekly —
       both a fresh dist from HEAD and a replay of the latest published
       Release as a real downloader.
     - **Native packages + published image**: `.deb` / `.rpm` built from one
       nfpm manifest (payload = the bundle at `/opt/aletheia`, byte-identity
       proven; opt-in env; the rpm depends on the libgmp soname so it
       resolves across rpm distros), attached to the Release keyless-signed
       with the self-verify loop covering every artifact; the runtime
       container image is published to GHCR with its digest keyless-signed,
       and its build fails unless every compiled binding builds against the
       image's own payload.
     - **First tag-triggered release shipped as v5.0.0 (2026-07-24)** — the
       full-path acceptance test for all of the above. The tarball, `.deb`,
       `.rpm`, and GHCR image were published and consumer-verified against the
       `@refs/tags/v5.0.0` identity. It surfaced and fixed the release-path
       defects before go-live: the `.deb`/`.rpm` Python binding must be consumed
       via `PYTHONPATH` (not `pip install` from the read-only `/opt` source, which
       setuptools cannot build in place), and a pre-existing GHCR package needs
       the repo granted **Write** under *Manage Actions access* (the docs had
       covered only the visibility flip). The dispatch dry-run
       (`gh workflow run release.yml`) — the whole pipeline minus its publish
       steps — caught the Python one; the real tag caught the GHCR one.
2. **`aletheia template <file>.xlsx` CLI subcommand.** A true no-code way to obtain
   the Excel template (today it needs a Python one-liner), so the non-programmer
   on-ramp is real.
3. **Go CAN-log reader.** Bring the `aletheia check … <log>` streaming command to
   Go for full CLI parity (it is Python-only today).

**Candidate tracks.** A native Haskell binding (the core is already Haskell, so it
needs no FFI); a python-can replacement (verified CAN-log readers for
ASC / BLF / MF4); a GHC `--bignum=native` rebuild to drop the libgmp LGPL
dependency; and SOME/IP support for automotive Ethernet — architecture drafted in
[SOMEIP_DESIGN.md](docs/development/SOMEIP_DESIGN.md) (verified monitor over
captured traffic; one shared library; parameterized LTL kernel; not scheduled).

**DBC text round-trip guarantee.**
`format_dbc_text` is always-strict: it returns `.dbc` text that provably
re-parses to the input DBC, or a typed `handler_text_roundtrip_failed` refusal —
machine-checked (`formatDBCTextResult-sound`), across all four bindings. Every
caller sees a result that is either provably faithful or explicitly refused,
never silently lossy. Every diagnostic behind that guarantee now carries a
proven tightness classification (recorded in the checker's module header), and
the structural validator names the round-trip-fatal mux shapes with
warning-class issues at validate/load — reusing the round-trip checker's own
deciders, so the surfaces cannot disagree. The heavier capability that remains
deferred, off the critical path: emitting the currently-lossy constructs
(e.g. multi-value multiplexing) without loss.

Living detail and rationale for the above live in
[`docs/development/DEFERRED_ITEMS.md`](docs/development/DEFERRED_ITEMS.md) and the
project memory notes.
