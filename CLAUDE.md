# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). Core logic in Agda with correctness proofs, compiled to Haskell, exposed through Python, C++, and Go APIs. Phase status: [PROJECT_STATUS.md](PROJECT_STATUS.md). Mission: [docs/PITCH.md](docs/PITCH.md).

## Development Environment

**Must be preserved across session compression.**

- Agda binary: `/home/nicolas/.cabal/bin/agda`
- Shell: `/usr/bin/fish` (config at `/home/nicolas/.config/fish/config.fish`)
- User binaries: `/home/nicolas/.local/bin`; libraries: `/home/nicolas/.local/lib`
- **Single Python venv**: exactly one, at `python/.venv` (Python 3.14). Run every Python gate via `python/.venv/bin/...` (never system `python3`). Never create a second venv (e.g. a repo-root `.venv`). Enforced by `tools/check_venv_convention.py` (a `run_ci.py` gate); the rule's canonical statement is in [AGENTS.md § Universal Rules](AGENTS.md#universal-rules-all-languages).
- **Optional GHA toolchain** (for `tools/run_ci.py` GHA meta-checks + local `act` pairing — see [docs/development/CI_LOCAL.md](docs/development/CI_LOCAL.md)):
  - `actionlint` — workflow YAML lint. Install:
    ```bash
    ACTIONLINT_VERSION=1.7.7
    curl -fsSLO "https://github.com/rhysd/actionlint/releases/download/v${ACTIONLINT_VERSION}/actionlint_${ACTIONLINT_VERSION}_linux_amd64.tar.gz"
    sudo tar xzf "actionlint_${ACTIONLINT_VERSION}_linux_amd64.tar.gz" -C /usr/local/bin actionlint
    ```
  - `act` — local GHA replay. Install: `curl -fsSL https://raw.githubusercontent.com/nektos/act/master/install.sh | sudo bash`. Requires Docker.
- **Optional mutation-testing toolchain** (for `tools/run_ci.py --mutation` / `ALETHEIA_MUTATION_CHECK=1` — see [docs/operations/MUTATION.md](docs/operations/MUTATION.md)):
  - **Python**: `mutmut` 3.x via `python/.venv/bin/pip install -e 'python/.[mutation]'` (`[mutation]` extras pin `mutmut>=3.5,<4`).
  - **Go**: `gremlins` via `go install github.com/go-gremlins/gremlins/cmd/gremlins@latest` (lands in `~/go/bin/`; gremlins substitutes for AGENTS.md cat 14(g) `go-mutesting` because the named tool is unmaintained since 2021 and panics on Go 1.26's `go/types` internals).
  - **C++**: `Mull` 0.34.0 (LLVM-22) — no prebuilt deb ships for LLVM 22, so build from source against system LLVM-22 (Bazel; `clang-22` + `llvm-22-dev`) into `~/.local/bin/` as `mull-{runner,reporter,ir-frontend}-22`. Full grounded recipe (incl. the `MODULE.bazel` ubuntu:24.04→"22" patch) in [docs/operations/MUTATION.md § C++](docs/operations/MUTATION.md); CI caches it (`.github/workflows/pr-heavy-lanes.yml`). The `ALETHEIA_MUTATION` build folds the real-`.so` integration tests into `unit_tests` so FfiBackend is on the mutation surface.
  Each tool's absence is auto-detected by `tools/mutation_run.py` (per-binding skip-with-precise-error); the orchestrator's static gate `tools/check_mutation_setup.py` runs always-on regardless of tool install state.

**Type-check command** (always cap heap):
```bash
/home/nicolas/.cabal/bin/agda +RTS -N32 -M16G -RTS src/Aletheia/YourModule.agda
```
- `-N32`: parallel GHC; critical for Protocol/StreamState.agda and Main.agda (17s vs >120s timeout).
- `-M16G`: heap cap; prevents runaway elaboration on the 62 GiB host. Doubles as a tripwire — bump only when a specific module legitimately needs it.
- First build compiles stdlib (~20s, cached thereafter).

## Global Project Rules

### AGENTS.md as Coding Standards

[AGENTS.md](AGENTS.md) defines per-language categories, guidelines, and verification commands. **Follow these as coding standards when writing code, not only as review checklists.** Consult the relevant language section before writing/modifying code.

### User Shorthands

When the user's message is just `UPD` (case-insensitive, no other content), interpret it as **"Update session state, memory/feedback, plan/project status, CLAUDE.md/AGENTS.md."** Sweep:
- `.session-state.md` (gitignored — local resume notes)
- `MEMORY.md` + relevant files under `memory/` (open-work pointers; new feedback memories if a generalizable lesson surfaced)
- `PROJECT_STATUS.md` and `docs/development/PARITY_PLAN.md` (the two roadmap surfaces — keep in sync)
- `CLAUDE.md` (Current Session Progress, module-flag breakdown, anything that drifted)
- `AGENTS.md` (only if a new rule / cross-ref was earned this session)

**Size budget** — after the sweep, check BOTH authoritative doc surfaces and reduce any that is over its limit:
- **CLAUDE.md**: `wc -c CLAUDE.md`, limit **40.0 kB**. If over, compress in the same UPD commit — push per-cluster narrative detail into the appropriate `memory/project_*.md` file (e.g. `project_review_round20.md`) and replace with a one-line index pointer, mirroring how prior rounds compressed (e.g. R6-B8.2's `970f704` compression of Current Session Progress). The compression IS doc-state sync; do not split into a separate commit.
- **MEMORY.md**: `wc -l ~/.claude/projects/-home-nicolas-dev-agda-aletheia/memory/MEMORY.md` (the agent store, NOT the repo root), limit **200 lines**. If over, compress in-place — move detail from any over-long or multi-line index entry into its `memory/*.md` topic file and collapse the pointer to a single ≤200-char line; merge or drop stale/duplicate/superseded pointers. MEMORY.md lives in the agent memory store under `~/.claude/` (**outside this repo**), so its reduction is an in-place memory edit, NOT part of the UPD git commit.

**UPD is a doc-state sync only.** The resulting commit must contain ONLY doc-sweep edits. Pre-existing uncommitted work (refactors, structural cleanups, prior tasks) goes in its own commit at task completion, never bundled into UPD. See `memory/feedback_upd_scope.md`. Apply the 2-question pre-commit gate (`feedback_pre_commit_scope_check.md`) before committing the doc sweep.

**UPD frequency rule (token-efficiency).** Run UPD **once per round close**, or once per coherent cluster-series close — not after every single cluster. R22 ran 19 UPDs across 65 commits (29% of all commits were doc syncs); each UPD re-loads CLAUDE.md (~40 KB), so 19 UPDs amount to ~760 KB of CLAUDE re-reads alone. The right cadence: small-cluster work (e.g. each `b25` batch) updates `.session-state.md` (gitignored — no token cost to other sessions) during the work, then a single UPD at the end syncs CLAUDE.md / MEMORY.md / PROJECT_STATUS.md. Exception: when a cluster surfaces a new durable rule (a new `memory/feedback_*.md` worth indexing) AND subsequent work depends on that rule being indexed, that single rule can warrant its own UPD. When in doubt, defer the UPD to the next natural rest-point.

When the user's message is just `READ` (case-insensitive, no other content), interpret it as **"Read the session state, memory/feedback, plan/project status, CLAUDE.md/AGENTS.md."** Sweep (read-only — no edits):
- `.session-state.md` (gitignored — local resume notes)
- `MEMORY.md` + relevant files under `memory/` (open-work pointers, feedback memories)
- `PROJECT_STATUS.md` and `docs/development/PARITY_PLAN.md` (the two roadmap surfaces)
- `CLAUDE.md` (already loaded into context)
- `AGENTS.md` (per-language coding standards)

READ is the read-only counterpart of UPD: rehydrate context at session start, do not write.

### Agda Module Requirements (MANDATORY)

Every Agda module MUST start with:
```agda
{-# OPTIONS --safe --without-K #-}
```

- `--safe`: no postulates, no unsafe primitives, no non-terminating recursion.
- `--without-K`: HoTT compatibility (no Streicher's K).
- Library-level `--erasure` (in `aletheia.agda-lib`) enables `@0` for zero-cost phantom parameters (e.g. `Timestamp μs`).

**Exceptions**: postulates require a separate `*.Unsafe.agda` module (drop `--safe` only there); allowlisted by name in `Shakefile.hs`. `cabal run shake -- check-invariants` rejects any other `^postulate` line or `Unsafe`-named module, and CI runs `check-invariants` on every build.

### Module Safety Flag Breakdown

273 total modules (`cabal run shake -- count-modules`):
- **268**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

272 of 273 modules use `--safe`. No modules require `--sized-types`. The per-commit module-count genealogy (which split/extraction added each module across A.2, Path A.4, Tracks D/E, and rounds R18–R23) lives in [PROJECT_STATUS.md](PROJECT_STATUS.md) and the `memory/project_*.md` round files — not duplicated here.

## Common Commands

See [Building Guide](docs/development/BUILDING.md). Quick reference:

```bash
# Type-check a single module
cd src && agda +RTS -N32 -M16G -RTS Aletheia/YourModule.agda

# Build everything (Agda → Haskell → libaletheia-ffi.so) — incremental + hash-safe
cabal run shake -- build

# Regenerate the foreign-lib MAlonzo module list (after adding/removing an Agda module)
cabal run shake -- gen-ffi-modules

# IWYU import analysis — regenerates the relevant .agdai (no full .hs/.so rebuild)
cabal run shake -- iwyu

# Tests (each from the right cwd)
cd python && python3 -m pytest tests/ -v
cd python && basedpyright aletheia/ benchmarks/ tests/
cd python && pylint aletheia/ tests/ benchmarks/
cd cpp && cmake -B build && cmake --build build && ctest --test-dir build
cd go && go test ./aletheia/ -v -count=1 -race

# Cross-language benchmarks
bash benchmarks/run_all.sh --frames 1000 --runs 5 --bench throughput
```

## Architecture

Three-layer design: [docs/architecture/DESIGN.md](docs/architecture/DESIGN.md).

Agda packages: **Parser/**, **CAN/**, **DBC/**, **LTL/** (Syntax, Incremental, Semantics, Adequacy, Coalgebra, SignalPredicate, SimplifySound, Reachable, JSON), **Trace/**, **Protocol/**. Full file tree: [README.md](README.md#project-structure).

## Development Workflow

1. Edit Agda source.
2. Type-check fast: `cd src && agda +RTS -N32 -M16G -RTS Aletheia/Parser/Combinators.agda`.
3. Full build: `cabal run shake -- build` (also rebuilds `libaletheia-ffi.so`).
4. Run tests for affected bindings.

Shake tracks Agda dependencies by content hash. First full build ~60s; an unchanged
rebuild is ~0.1s and a one-module edit ~12s (incremental — cabal recompiles only the
changed MAlonzo module + relinks). Adding/removing an Agda module: re-list it with
`cabal run shake -- gen-ffi-modules` (otherwise the build fails naming it, via the
foreign library's `-Werror=missing-home-modules` drift gate). Details:
[BUILDING.md](docs/development/BUILDING.md).

## Key Files

- **aletheia.agda-lib**: Agda library config (pinned stdlib version)
- **Shakefile.hs**: build orchestration (Agda → Haskell → shared library)
- **haskell-shim/aletheia.cabal**: Haskell package + `foreign-library aletheia-ffi`
- **haskell-shim/src/AletheiaFFI.hs**: FFI exports (Python ctypes, C++/Go dlopen)
- **python/pyproject.toml**: Python package config
- **cpp/CMakeLists.txt**: C++23 build (CMake 3.25+, FetchContent for nlohmann/json + Catch2)
- **docs/FEATURE_MATRIX.yaml**: cross-binding feature parity matrix; structural gate tests in `python/tests/`, `go/aletheia/`, `cpp/tests/` fail CI on silent symbol removal. Roadmap: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md).

## Important Notes

### Agda Compilation

- `--safe --without-K` mandatory (header pragma + `check-invariants`); the lone `--without-K`-only exception (`Substrate.Unsafe`) is documented in the flag breakdown.
- Generated MAlonzo lives in `build/`; never edit — modify Agda source.

### MAlonzo FFI Name Mangling

MAlonzo mangles names (e.g., `processJSONLine` → `d_processJSONLine_4`). Build auto-detects mismatches and prints exact `sed` fix commands — just run them. Triggers rarely (only when adding/removing definitions before `processJSONLine` in Main.agda). Keep `AletheiaFFI.hs` minimal; alternatives like COMPILE pragmas would compromise `--safe`.

### Haskell FFI Layer

3 files (~470 LOC, no business logic):
- **AletheiaFFI.hs** (~277 LOC): `foreign export ccall` wrappers around `processJSONLine` (JSON commands) and `processFrameDirect` (binary frames via `aletheia_send_frame`).
- **AletheiaFFI/Marshal.hs** (~95 LOC): Agda type construction helpers.
- **AletheiaFFI/BinaryOutput.hs** (~99 LOC): binary response encoding.

State managed via `StablePtr (IORef StreamState)`. All bindings load `.so` via ctypes/dlopen — no subprocess overhead.

### C++ Binding (`cpp/`)

Wraps `libaletheia-ffi.so` via `dlopen`. `IBackend` interface; `MockBackend` for tests. Strong types (`std::byte`, validated newtypes, `std::expected`). Custom `Logger` (~90L, callback-based, 16 event types matching Go's slog, zero-cost when null). RTS cores via `make_ffi_backend(path, rts_cores)` (default 1, once-per-process with mismatch warning). C++23, **Clang 22** (the supported toolchain — see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)); needs a libstdc++/libc++ with C++23 (`<expected>`). Style: `.clang-format` + `.clang-tidy`. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

### Go Binding (`go/`)

Wraps `libaletheia-ffi.so` via cgo + dlopen. `Backend` / `MockBackend` / `FFIBackend` (with C trampolines). Strong types (`[]byte` payload + DLC validation, validated CAN ID / DLC newtypes, sealed CanID/Predicate/Formula interfaces). `slog` via `WithLogger` option (16 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings. RTS cores via `WithRTSCores` functional option. `Client` is goroutine-safe via a 1-deep channel-token semaphore (`lockCh chan struct{}`) chosen over `sync.Mutex` so that `ctx`-aware `TryLock` cancellation works correctly (see `docs/architecture/CANCELLATION.md`); double-close safe; GHC RTS init thread-pinned (`LockOSThread`). Optional `go/excel/` is a separate Go module pulling `xuri/excelize`; depend on it only for the Excel loader. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

### Module Organization

Follow existing package structure (Parser, CAN, DBC, LTL, …). Include correctness properties alongside implementations (`Properties.agda`). Update Main.agda if new functionality needs FFI exposure.

### Import Naming Conventions

When stdlib operators clash, use **subscript suffix** for consistency:
- String: `_++ₛ_`, `_≟ₛ_`
- List: `_++ₗ_`
- Rational: `_+ᵣ_`, `_*ᵣ_`, `_-ᵣ_`, `_≤ᵣ_`

```agda
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.List using (List) renaming (_++_ to _++ₗ_)
open import Data.Rational using () renaming (_+_ to _+ᵣ_; _*_ to _*ᵣ_)

result   = "hello" ++ₛ "world"
combined = list1 ++ₗ list2
```

Underscores are invisible in infix usage but remain when passing operators as parameters (e.g., `foldr _++ₛ_ ""`).

## Troubleshooting

Build-time issues are catalogued in [BUILDING.md § Troubleshooting](docs/development/BUILDING.md#troubleshooting). Common ones:

- **Build failures**: `cabal run shake -- clean && cabal run shake -- build`.
- **MAlonzo name mismatch**: build prints exact `sed` command — run it.
- **Type-checking timeout**: always `+RTS -N32 -M16G -RTS`.
- **`hs_init` failure / `aletheia_init() returned null`**: `.so` built against different GHC than loaded. Rebuild (`cabal run shake -- build`); ensure no stale copy in `$LD_LIBRARY_PATH`.
- **`.so` load failure**: loader checks `_install_config.LIBRARY_PATH` → `LD_LIBRARY_PATH` → `/usr/local/lib`. Regen via `cabal run shake -- install` or set `ALETHEIA_FFI_PATH`.
- **ctypes signature mismatch (Python)**: `.so` and Python package versions drifted. Compare `python -m aletheia --version` vs `strings libaletheia-ffi.so | grep aletheia-ffi-`.
- **DBC validation rejection**: check `ValidationIssue.code` enum — table in [PROTOCOL.md § Error Code Reference](docs/architecture/PROTOCOL.md#error-code-reference). `aletheia validate --dbc <file>` to see all issues.
- **Property formula parse error**: JSON schema is strict (`"operator"` lowercase, predicates under `{"operator": "atomic", "predicate": {...}}`). Compare against `Signal("X").equals(1).to_dict()` output.

## Performance Considerations

- **Parser combinators**: structural recursion on input length, not fuel — fuel breaks termination or blows up type-checking. See `Parser/Combinators.agda`.
- **Type-checking**: always `+RTS -N32 -RTS` (StreamState/Main otherwise time out past 120s).
- **Hot path**: `Dec`-valued predicates allocate proof terms per call in MAlonzo. Replace with `Bool`-valued fast path + equivalence lemma. See `extractSignalCoreFast` for the pattern.

## Implementation Phases

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity); post-R17 parity-plan Tracks A–E all complete (matrix gates / DBC text parser / cancellation / doc harness / VAL_ promotion). **No active phase**; Phase 6 (Extensions & New Protocols — CLI parity stretch + Rust/Haskell bindings (Haskell native; Rust via .so) + python-can replacement + GHC native bignum + SOME/IP) is the candidate next track, goal-set pinned 2026-05-07 but not started.

---

## Notes for newcomers

Start with the [Project Pitch](docs/PITCH.md) for context.

**Operational pitfalls** (most are caught by build/lint, but easy to trip on first time):
- `Dec`-valued predicates on the streaming hot path: MAlonzo allocates per call. Use `Bool`-valued fast path + equivalence lemma (`extractSignalCoreFast`).
- Fuel-based parser combinators: structural recursion on `length input` only.
- Type-checking without `+RTS -N32 -RTS`: large modules time out past 120s.
- Running tools from the repo root: `pytest` / `basedpyright` / `pylint` need `cd python` first (config picks up nearest `pyproject.toml`).

**Key terms used elsewhere in this file:**
- **"Phase" (capital P) is reserved.** It denotes a **whole-project phase only** — Phase 1 … Phase 6 (see [PROJECT_STATUS.md](PROJECT_STATUS.md) § Project Phases). **Never call the sub-units of any other plan "phases"** — it conflates them with project phases and causes confusion. For the Rust binding's incremental deliverables use **"slice"** (the established term: "tracer-bullet slice", "a later Rust slice"); for other plans use "cluster" / "stage" / "step" / "track". Worked example: [docs/development/RUST_PARITY_PLAN.md](docs/development/RUST_PARITY_PLAN.md) organizes its work into *slices*, not phases. (Convention pinned 2026-06-14 at user request.)
- **MAlonzo**: Agda's Haskell backend. `agda --compile` produces a `MAlonzo/` directory of generated `.hs` files; the Cabal package and FFI shared library are built on top. Function names get mangled.
- **`Dec A`**: A type expressing decidability (`yes (a : A) ⊎ no (¬ A)`). Carries a *proof object* at runtime — that's why it allocates on hot paths.
- **`memory/<name>.md`**: a pointer to Claude Code's agent memory store (under `~/.claude/`, **outside this repository**) — written for the agent, not a repo-relative link, so it will not resolve in a repo checkout. The same convention appears in several docs (AGENTS.md, PROJECT_STATUS.md, …). Documented here as an explicit convention 2026-06-12 — it had accreted unratified, not by deliberate decision.

**Code style**: per-language conventions live in [AGENTS.md](AGENTS.md). Don't duplicate here.

**Pre-commit minimum** (doc-only changes): `agda +RTS -N32 -M16G -RTS src/Aletheia/Main.agda` → `cabal run shake -- build` → relevant binding tests.

**For code changes**, the Agda-side minimum is `build` PLUS the proof-side Shake gates — `build` only type-checks Main.agda's runtime transitive closure (the runtime path that flows into `libaletheia-ffi.so`), so Properties / *Roundtrip / *WF / Substrate.Unsafe modules are NOT reached by it. Run all of:
- `cabal run shake -- check-properties` — walks the proof tree (Properties / *Roundtrip / *WF + universal aggregator + Substrate.Unsafe); the actual proof-correctness gate
- `cabal run shake -- check-invariants` — `^postulate` / Unsafe-named-module allowlist (postulates only allowed in the substrate Unsafe module)
- `cabal run shake -- check-no-properties-in-runtime` — runtime modules must not import Properties (would pull lemmas into MAlonzo)
- `cabal run shake -- check-erasure` — `@0` erasure assumption that FFI Marshal.hs depends on (CANId proof slot compiled to `AgdaAny`; Timestamp newtype)
- `cabal run shake -- check-fidelity` — MAlonzo constructor-drift smoke test (binary FFI end-to-end)
- `cabal run shake -- check-ffi-exports` — diffs MAlonzo-mangled FFI export names against `haskell-shim/ffi-exports.snapshot`

Then [AGENTS.md § Step 4](AGENTS.md#step-4-implement-and-verify) defines the full 4-gate sequence around these (Agda gates → unit tests → lint gates → benchmarks); do not let this section drift from it.

**Resources**: [Agda Documentation](https://agda.readthedocs.io/), [Standard Library](https://agda.github.io/agda-stdlib/), [Agda Tutorial](https://agda.readthedocs.io/en/latest/getting-started/tutorial-list.html).

---

## Current Session Progress

**🦀 RUST TYPED BINDING ✅ 2026-06-14** (local `phase6/rust-binding-typed`, pending batch push) — past the tracer bullet into a typed client: validated value types (`CanId` Standard/Extended enum, `Dlc`, `Rational`, `Timestamp`, `TimeBound` — `Result`-returning ctors), native exhaustively-matchable `Predicate`/`Formula` enums serializing to the core's exact wire shape, and a `Client` that loads a DBC (`parse_dbc_text`), binds properties (`set_properties`), and streams frames through the **binary FFI** (`start_stream`/`send_frame`/`send_error`/`send_remote`/`end_stream` + `extract_signals`); `process` stays a raw JSON escape hatch. `Client` is `!Send + !Sync` (raw StreamState ptr, thread-pinned RTS); RAII free-str + `OnceLock` RTS latch carried from the tracer bullet. New `rust/src/{error,types,ltl,response}.rs` + rewritten `lib.rs`. `rust` FEATURE_MATRIX column (11 impl / 29 planned, all 40 rows) + **fourth** parity gate `rust/tests/feature_matrix.rs`; Python/Go/C++ gates validate it too. Planned: typed DBC doc model, Check DSL, client-side violation enrichment, CLI. Verified vs real `.so`: cargo test 7/7 (incl. violation detection + CAN-FD/BRS/ESI), clippy `-D warnings`, fmt, all 4 matrix gates.

**🪞 GO/C++ MOCK FIDELITY ✅ 2026-06-14** (local `fix/mock-binary-sentinel-convergence` → `03fff4b`'s predecessor in the batch) — Go + C++ MockBackends now record `<binary:OP>` sentinels for every binary-path op (matching Python), discarding args (their marshalling is verified by the real-`.so` round-trip tests). The mocks previously fabricated JSON event/command shapes (`{"type":"data"/"error"/"remote"}`, `{"command":"sendFrame"}`) that production never emits and the core rejects. Removed the strictly-dead serializers (Go `serializeDataFrame`/`Error`/`Remote`; C++ `serialize_send_frame`).

**🧹 DEAD JSON-STREAMING PRUNE ✅ 2026-06-14** (local `phase6/prune-dead-json-streaming` `2ea8ecf`) — removed the 5 test-only JSON streaming-command mirrors (`startStream`/`sendFrame`/`extractAllSignals`/`endStream`/`formatDBC`) from the verified core's command protocol: `StreamCommand` ctors (`Message.agda`) + `Routing.agda` parsers (+ the orphaned `parseCanIdDlc`/`parseBytePayload` chain + `handleSendFrame`) + `processStreamCommand` cases. Binding-side: C++ dead `serialize_*` + default `IBackend` impls → the six streaming endpoints are now **pure-virtual** (Cancel/Holding test doubles share a new `StubStreamingBackend` base); Python dead JSON ack-default markers. Live DBC/property JSON commands (`parseDBC`/`setProperties`/`validateDBC`/`parseDBCText`/`formatDBCText`) + all binary FFI handlers retained. **Zero proof entanglement** (proof-cost spike confirmed: no totality proof over `StreamCommand`; handlers stay live via the binary path). Benchmark-neutral (throughput same-session before/after, ≤±4% noise). Gates: 6 Agda proof gates (check-ffi-exports = no drift) + IWYU 0 + clang-22 ctest 12/12 + pytest 4889 + Go/Rust green.

**🔒 SINGLE-VENV ENFORCEMENT ✅ 2026-06-14** (local `chore/single-venv-enforcement` `03fff4b`) — `tools/check_venv_convention.py` (a `run_ci.py` source-hygiene gate): exactly one on-disk `pyvenv.cfg` (at `python/.venv`) + no tracked doc/script may create/activate a venv outside it. Caught + fixed a real bug the prose convention missed: `benchmarks/run_all.sh` activated a repo-root `$PROJECT_DIR/.venv`. Canonical rule in [AGENTS.md § Universal Rules](AGENTS.md); `.gitignore` collapsed to the single `.venv`; DEFERRED_ITEMS G.1 now gate-backed. Lesson: `memory/feedback_single_venv.md`.

**🔎 FEATURE_MATRIX SEMANTICS + C++ `mock_backend` RECLASSIFIED ✅ 2026-06-12** (PR #23 squash → `main` `253a019`) — investigated what the matrix actually guarantees: the structural gate enforces only entry-resolves (`implemented`) + reason-non-empty (`not_applicable`) — it **never** checks a status is *correct* (semantics = human judgment). Reclassified C++ `mock_backend` `not_applicable` → **`planned`**: the real capability is the *test-configurable, inspectable* mock (Python/Go ship it publicly; C++ keeps the `MockBackend` class test-internal at `cpp/src/detail/mock_backend.hpp` — the public surface ships only the fixed `make_mock_backend()` factory + the `IBackend` DI seam, its own `implemented` row). The old `not_applicable` reason named the conditions under which it "flips to implemented" — the tell of a `planned` item. Tightened the row description to "test-configurable"; swapped PARITY_PLAN's canonical `not_applicable` example to `lazy_streaming_batch` (a genuine per-idiom non-goal). New `planned` backlog item (DEFERRED_ITEMS **H.1**): promote the configurable C++ mock to a public `aletheia/testing.hpp`. Lesson: `memory/feedback_feature_matrix_status_semantics.md`.

**🟢 PHASE 6 — CLI PARITY (C++/Go) ✅ MERGED 2026-06-12** (PR #21 squash → `main` `e45b4a3`) — the Phase-6 "quick wins" track. Go CLI (`go/cmd/aletheia`) + C++ CLI (`aletheia::run_cli` — declared in `cpp/include/aletheia/cli.hpp`, defined in `cpp/src/cli/cli.cpp`, + thin `cpp/src/cli/main.cpp`; `aletheia-cli` binary): 5 subcommands (validate/extract/signals/format-dbc/mux-query) dispatching to the real verified core. Exposed canonical JSON + issue rendering idiomatically — Go `DBCDefinition.MarshalJSON`; C++ `to_canonical_json` + `to_string(IssueSeverity/IssueCode)`. FEATURE_MATRIX `cli` row → implemented ×3; functional tests `go/cmd/aletheia/main_test.go` + `cpp/tests/cli_tests.cpp` (real FFI, incl. mux selector + mismatch); run_ci clang-tidy glob extended to `src/cli/`. `check` deferred (needs `can_log_reader` / python-can item); `--dbc` text-only (JSON/.xlsx Python-only); the toolchain-bump quick-win was a no-op (basedpyright/pylint already latest). CoPilot review: 1 real bug (C++ mux-query ignored `--mux/--value`) fixed + 4 nits + 2 verified-FP. Workflow lessons: `memory/feedback_command_dribble_file.md`, `memory/feedback_verify_actions_before_claiming.md`.

**🔐 RELEASE-SIGNING + ACCESS HARDENING ✅ 2026-06-12** (PR #20 `8fdd5db` + follow-up `1042739`) — resolved the password-less-cosign-key follow-up: cosign key rotated to passphrase-protected (v2.0.0 re-signed; release verification now anchors on the published SHA-256 key fingerprint, not mutable `main`); write-collaborators removed (sole owner); GitHub rulesets — `v*` tag creation admin-only + `required_signatures` on `main`; GPG tag/commit signing (key exp **2028-06-10**, renew before). Finding: GitHub can't *enforce* signed tag objects (`required_signatures` is commit-only) — signed tags are a practice (`tag.gpgSign` + Verified badge). Detail: `memory/project_release_signing_hardening.md`.

**🏷️ 2.0.0 RELEASED 2026-06-11** (PR #18 squash → `main` `61a0530`, tag `v2.0.0`) — doc-accuracy audit + **clang-22 adoption** (CI + mutation lane built-from-source Mull-22 + ubsan + support-policy SSOT in `BUILDING.md`); FfiBackend mutation coverage (60/60 under clang-22); **benchmark PR regression gate** (`.github/workflows/benchmark.yml` + `tools/benchmark_gate.py`, baseline `benchmarks/gha_baseline.json` — GHA-measured, provisional single-run); **CPP_API.md + GO_API.md** references (harness-validated) closing cross-binding doc parity; PYTHON_API.md streaming-feature gaps; CLI `aletheia`-command accessibility; DRY/TOC doc simplification. The signed distribution shipped (first signed GitHub Release — cosign + Rekor); the cosign key was rotated to passphrase-protected on 2026-06-12 (see Release-signing hardening above). Detail in CHANGELOG `[2.0.0]` (21 BREAKING since v1.1.1). Lessons: `memory/feedback_no_shebang_in_tools.md` (ruff EXE001 / cache masking).

**A.2 — `BO_TX_BU_` message senders ✅ DONE 2026-06-11** — the verified DBC text round-trip now carries message senders (`BO_TX_BU_` as an 8th synthesized section, VAL_ analogue); `WellFormedTextDBCAgg` is strictly weaker; `parse_dbc_text` now attaches transmitters instead of dropping. Module count 269→**273**. (E.2 stays HOLD at 5/9.) Full detail + the green-slice commit map + the "never `rewrite` over a parser-bearing goal" lesson: `memory/project_a2_botxbu_senders.md`, `memory/feedback_no_rewrite_over_parser_goal.md`.

**`ci/pr-heavy-lanes` ✅ MERGED** (PR #16, 2026-06-10) — the Phase-2 heavy-lanes workflow (parallel repro/stability/mutation; repro REQUIRED, others ADVISORY) + the mutation-to-zero campaign (C++ 0 / Python 215→1 documented-equivalent / Go 0; baselines in `docs/MUTATION_BENCH.yaml`; no defenses deleted for the metric). Detail: `memory/project_mutation_to_zero.md`, `memory/feedback_mutation_no_defense_removal.md`.

**`ci-speed` ✅ MERGED** (PR #7, 2026-06-09) — the post-R23 fast-gate program: warm `check-properties` IS the proof gate (~13×), `tools/iwyu.py` is the `.agdai` import gate, tree-wide lint enforcement (ruff ALL + pylint 10 + basedpyright 0/0/0), renderer-faithfulness proofs. Module count 266. Detail: `memory/project_ci_speed_optimization.md`, `memory/project_agda_iwyu.md`.

**Branch & PR hygiene ✅ ENFORCED** — `.github/workflows/pr-full-ci.yml` runs `tools/run_ci.py` (all gates) on every `pull_request` + `push:main`; the `main` ruleset now **requires** the `tools/run_ci.py (all gates)` check (enabled by the user 2026-06-10, validated against the green merge sweep).  C++ builds with **Clang 22** (the supported toolchain — see [BUILDING.md § Toolchain support policy](docs/development/BUILDING.md#toolchain-support-policy)), enforced in `cpp/CMakeLists.txt`.  Detail: `docs/development/BRANCH_PR_HYGIENE.md`, `memory/project_cpp_compilers.md`.

**Post-merge cleanup** (branch `post-merge-cleanup`, 2026-06-10): ghcup-dir `chown` for CI log hygiene; new `docs/development/DEFERRED_ITEMS.md` (the in-source-deferral backlog + per-item re-examination); venv-convention docs standardized on `python/.venv` (closes DEFERRED_ITEMS **G.1**); this UPD.  Open backlog now lives in `DEFERRED_ITEMS.md` — `E.1` (owed bridge lemma), `A.2` (`BO_TX_BU_` text senders) are the DO/INVESTIGATE candidates; **`E.2` (`WellFormedTextDBCAgg` discharge) is IN PROGRESS** on branch `agda/e1-isidentstart-hspace-bridge` (bounded slice `8758236`); the rest are HOLD/CAN'T or parked by prior user decision.

**Phase 6 — CLI parity (C++/Go) ✅ done 2026-06-12** (the quick-wins track; see top). Remaining Phase 6 candidates (not started): Rust/Haskell bindings (Haskell native; Rust via `.so`), python-can replacement (`can_log_reader`), GHC native bignum, SOME/IP.

**Standard gates** (all run by `tools/run_ci.py`; the full ordered sequence is [AGENTS.md § Step 4](AGENTS.md#step-4-implement-and-verify) — the canonical source): Agda `build` + the proof gates (`check-properties` and siblings), Python `pytest`, Go `go test -race`, C++ `ctest` (Clang 22), tree-wide lint (ruff / pylint / basedpyright), IWYU (`tools/iwyu.py`), GHA meta (actionlint / pin / permission checks), and SPDX headers.

## Prior Tracks (closed) — see PROJECT_STATUS.md for narratives

- **Track E** ✅ 2026-05-08 — VAL_ promotion to `DBCSignal.valueDescriptions`; Plan-A bundled commit. Detail: `memory/project_track_e_val_promotion.md`.
- **Track D** ✅ 2026-05-04 — cross-binding doc-example harness (Python `pytest --markdown-docs` + Go `TestDocExamples` + C++ Catch2). Closed R17-DEF-6.
- **Track C** ✅ 2026-05-03 — cancellation contract bound across all 3 bindings. Detail: `memory/project_track_c_cancellation.md`.
- **Track B.3** ✅ 2026-05-03 — universal roundtrip + bindings + cantools dropped (LGPL contingency realised). Detail: `memory/project_b3e_parsedbctext.md`.
- **B.3.d universal target** — `∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d` proven in `Substrate/Unsafe.agda` (sole axiom consumer; co-located by Unsafe-module policy). Detail: `memory/project_b3d_universal_proof.md`.

## Format DSL toolkit (`DBC/TextParser/Format.agda`)

- **Core constructors**: `literal` / `ident` / `nat` / `stringLit` / `pair` / `iso` / `many` / `refined` / `altSum` / `withPrefix`.
- **Whitespace family** (each with distinct parser permissiveness — see `feedback_format_dsl_ws_family_discipline.md`): `ws` / `wsOpt` / `wsCanonOne` / `wsCanonTab` / `withWS` / `withWSOpt` / `withWSCanonOne` / `withWSCanonTab` / `withWSAfter`.
- **Refinement carriers**: `decRat` / `intDecRat` / `natDecRat`.
- **Sugar**: `discardFmt` (wire-only fields) / `nonNewlineRun` (opaque-tail consumer) / `newlineFmt` (LF/CRLF).
- **Cycle-break pattern**: when a Format module would close a cycle, extract cycle-relevant subset to a `Foundations.agda` submodule (used at 3d.5.c-ε / 3d.5.d-3c-A).

## Performance baseline

Path A profile (post-3d.4 + JSON-mirror, runtime impact retained from `320c5a9`): Stream LTL +12-38% across bindings (Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (Path A structural cost). All 3d.5+ Format DSL work + Track E sub-phases are proof-only and runtime-neutral on the streaming hot path. Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (requires explicit user approval per `feedback_no_suppression_without_approval`).

**Cross-binding parity roadmap**: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. **R17 deferrals all closed**: R17-DEF-1 (2026-05-07) by comprehensive check-fidelity coverage; R17-DEF-2 (2026-05-07) by re-verify against the Agda DBC truth set — B.1 Tier 1 + B.1.x Tier 2 + B.1.x commit-3 senders + Track E VAL_ ship every `DBC` / `DBCSignal` / `DBCMessage` field across all 3 bindings, with FEATURE_MATRIX rows (`dbc_metadata_tier1` / `_tier2` / `dbc_signal_receivers` / `dbc_message_senders` / `dbc_signal_value_descriptions` / `dbc_text_format`) + per-binding parity tests + CHECK 23 `unknown_value_description_target` IssueCode mirror; R17-DEF-3 by Track C.2; R17-DEF-4 by Track B.3; R17-DEF-5 by Track C.3; R17-DEF-6 by Track D.
