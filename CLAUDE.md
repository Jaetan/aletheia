# CLAUDE.md

Guidance for Claude Code (claude.ai/code) when working in this repository.

## Project Overview

Aletheia is a formally verified CAN frame analysis system using Linear Temporal Logic (LTL). Core logic in Agda with correctness proofs, compiled to Haskell, exposed through Python, C++, and Go APIs. Phase status: [PROJECT_STATUS.md](PROJECT_STATUS.md). Mission: [docs/PITCH.md](docs/PITCH.md).

## Development Environment

**Must be preserved across session compression.**

- Agda binary: `/home/nicolas/.cabal/bin/agda`
- Shell: `/usr/bin/fish` (config at `/home/nicolas/.config/fish/config.fish`)
- User binaries: `/home/nicolas/.local/bin`; libraries: `/home/nicolas/.local/lib`
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
  - **C++**: `Mull-19` (matches LLVM 19 / `clang-19` from apt). Extract the release deb locally to `~/.local/bin/`:
    ```bash
    sudo apt install clang-19   # one-time
    curl -fsSLO https://github.com/mull-project/mull/releases/download/0.33.0/Mull-19-0.33.0-LLVM-19.1.7-debian-amd64-13.deb
    mkdir -p /tmp/mull-extract
    dpkg-deb -x Mull-19-0.33.0-LLVM-19.1.7-debian-amd64-13.deb /tmp/mull-extract
    cp /tmp/mull-extract/usr/bin/mull-{runner,reporter}-19 ~/.local/bin/
    cp /tmp/mull-extract/usr/lib/mull-ir-frontend-19 ~/.local/bin/
    ```
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

**UPD is a doc-state sync only.** The resulting commit must contain ONLY doc-sweep edits. Pre-existing uncommitted work (refactors, structural cleanups, prior tasks) goes in its own commit at task completion, never bundled into UPD. See `memory/feedback_upd_scope.md`. Apply the 2-question pre-commit gate (`feedback_pre_commit_scope_check.md`) before committing the doc sweep.

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

247 total modules (`cabal run shake -- count-modules`):
- **242**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

246 of 247 modules use `--safe`. No modules require `--sized-types`. Per-commit module-count drift (Path A.4 cluster lift, Track E sub-phase additions, R18 cluster 14 extraction, R18 cluster 2 `Aletheia.Limits` extraction, R19 Phase 2 cluster 8 `Aletheia.DBC.Formatter.Bounded` extraction, etc.) is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md` / `memory/project_track_e_val_promotion.md` / `memory/project_review_round18.md`.

## Common Commands

See [Building Guide](docs/development/BUILDING.md). Quick reference:

```bash
# Type-check a single module
cd src && agda +RTS -N32 -M16G -RTS Aletheia/YourModule.agda

# Build everything (Agda → Haskell → libaletheia-ffi.so)
cabal run shake -- build

# Tests (each from the right cwd)
cd python && python3 -m pytest tests/ -v
cd python && basedpyright aletheia/
cd python && pylint aletheia/
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

Shake tracks Agda dependencies. First full build ~60s; subsequent ~5–15s.

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

Wraps `libaletheia-ffi.so` via `dlopen`. `IBackend` interface; `MockBackend` for tests. Strong types (`std::byte`, validated newtypes, `std::expected`). Custom `Logger` (~90L, callback-based, 15 event types matching Go's slog, zero-cost when null). RTS cores via `make_ffi_backend(path, rts_cores)` (default 1, once-per-process with mismatch warning). C++23, targets g++>=14 / clang>=21. Style: `.clang-format` + `.clang-tidy`. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

### Go Binding (`go/`)

Wraps `libaletheia-ffi.so` via cgo + dlopen. `Backend` / `MockBackend` / `FFIBackend` (with C trampolines). Strong types (`[]byte` payload + DLC validation, validated CAN ID / DLC newtypes, sealed CanID/Predicate/Formula interfaces). `slog` via `WithLogger` option (15 event types); `ViolationEnrichment.CoreReason` carries Agda core reason strings. RTS cores via `WithRTSCores` functional option. `Client` is goroutine-safe (`sync.Mutex`), double-close safe, GHC RTS init thread-pinned (`LockOSThread`). Optional `go/excel/` is a separate Go module pulling `xuri/excelize`; depend on it only for the Excel loader. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

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

[PROJECT_STATUS.md](PROJECT_STATUS.md). Current state: Phase 5.1 complete (binary FFI 4.3× CAN 2.0B / 9.1× CAN-FD; CAN-FD; C++/Go bindings; cross-language benchmarks; four-tier check interface with full parity); post-R17 parity-plan Tracks A–E all complete (matrix gates / DBC text parser / cancellation / doc harness / VAL_ promotion). **No active phase**; Phase 6 (Extensions & New Protocols — CLI parity stretch + python-can replacement + GHC native bignum + SOME/IP) is the candidate next track, goal-set pinned 2026-05-07 but not started.

---

## Notes for newcomers

Start with the [Project Pitch](docs/PITCH.md) for context.

**Operational pitfalls** (most are caught by build/lint, but easy to trip on first time):
- `Dec`-valued predicates on the streaming hot path: MAlonzo allocates per call. Use `Bool`-valued fast path + equivalence lemma (`extractSignalCoreFast`).
- Fuel-based parser combinators: structural recursion on `length input` only.
- Type-checking without `+RTS -N32 -RTS`: large modules time out past 120s.
- Running tools from the repo root: `pytest` / `basedpyright` / `pylint` need `cd python` first (config picks up nearest `pyproject.toml`).

**Key terms used elsewhere in this file:**
- **MAlonzo**: Agda's Haskell backend. `agda --compile` produces a `MAlonzo/` directory of generated `.hs` files; the Cabal package and FFI shared library are built on top. Function names get mangled.
- **`Dec A`**: A type expressing decidability (`yes (a : A) ⊎ no (¬ A)`). Carries a *proof object* at runtime — that's why it allocates on hot paths.

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

For full history (R6–R17, Path G, Phase 5.1, Tracks A/B.1–B.3, B.3.d Layers 1–4, Tracks C/D) see [PROJECT_STATUS.md](PROJECT_STATUS.md). Per-commit narratives + sub-phase tactical detail live in PROJECT_STATUS.md, `memory/project_b3d_universal_proof.md`, and `memory/project_track_e_val_promotion.md`. Resume notes / next-session entry point: [.session-state.md](.session-state.md).

**Active branch (2026-05-10): `review-r19`** — carry-over phase CLOSED + Phase 2 in flight.  Branch forked from `main` at `e37e6ea` 2026-05-09 (post R18 merge); not yet merged to `main` (live count via `git rev-list --count main..HEAD` per `feedback_self_referential_count_drift.md`).  Carry-over phase (clusters A-G, 9 of 9 R18 carry-overs) shipped 2026-05-09; per-cluster scope + commit hashes + closure narratives live in `review-r19-findings.md` and `memory/project_review_round19.md`.  R19-CARRY-1 partial (`@0`-erasure of `ℕToBitVec` shipped; Bool fast-path final RE-DEFER per cluster F empirical — Agda's `with ... in eq` ↔ outer `with`-abstraction barrier is at the elaboration mechanism, not the witness-slot semantics); R19-CARRY-2/3/4/5/6/7/8/9 closed.  Cluster G reopened 3 of cluster A's 4 "drop scope" items after user pushback (C++ `Rational::from_double` cross-binding asymmetry + `run_checks` logfile-existence precondition + `iter_can_log` reasoning correction).  Carry-over-phase lessons: `feedback_with_in_eq_outer_abstraction_barrier.md` (cluster D + F) and `feedback_drop_rationale_specificity.md` (cluster G).

**R19 Phase 2 in flight (started 2026-05-10)** — agent-driven review on the post-carry-over tip.  17 review agents (12 step-1 per-file + 4 system-level + 1 cross-doc) → 19 clusters ranked FIX-early / FIX-middle / DEFER-end-of-round per `feedback_review_round_dispositions.md`.  Cluster 18 adjudicated FIX-late by user (BRS/ESI cross-binding plumbing extends C FFI signature + propagates through 3 bindings + JSON wire).  Plan + findings live in `review-r19-phase2-findings.md` (seeded `a8c2503`, populated `efabe7b`, dispositions `1d3ebfa`).  **Phase 2 progress: 15 of 19 clusters closed** (7 FIX-early + 8 FIX-middle); 2 FIX-middle + 1 FIX-late + 1 DEFER pending.  Cluster 14 partial-shipped: 12 of 17 sub-themes closed (5 naming sub-batch `fd3d11d` + parseObjectList combinator `25510ef` + Go acquire helper `b3d8b3b` + C++ wrap_str_result `cb22dce` + InputBoundExceeded lift `479fd91` + AGDA-C-6.1/5.3 adjudicated design-held `00e08da` + can_id helpers `e42945b`).  5 remaining (AGDA-C-3.2 BoundKind ctor suffix ordering + 3.5 Standard/Extended suffix + 6.3 checkUnknown* helper + 6.4 Standard/Extended parameterization + 6.6 And/Or duality lift + GO-A-6.2 iota Stringer × 6 + GO-A-6.3 parseObjects[T] generic).

FIX-early ships (7 commits): cluster 6 AllObserved doc propagation `e8a1d8e`; cluster 2 CICD supply-chain hardening (sha256, ubuntu-24.04, snapshot.debian.org pin) `8a7333e`; cluster 4 test-discipline cleanup (atomic.Int32 lockWaiters, no time.Sleep, cast-not-suppress) `d29ec1e`; cluster 3 logger/event consistency `de45187`; cluster 1 doc drift mechanical batch (~80 doc fixes across 17 docs + 2 new binding-root READMEs) `8efd447`; cluster 15 stdlib dedup (`map-∘`, `m<n⇒m%n≡m` re-exports + 3 FP-after-audit closures) `1242dc5`; cluster 5 Agda+Go naming/hygiene mechanical batch (Go `Dbc*`→`DBC*` 52 IDs + `CanID`→`CANID` 40+ sites + 70+ godoc additions + AGDA-D-10.3 TraceEvent omission comment + GO-B-10.1 strdup rationale strengthened) `d3ad0ad` + stray-artifact cleanup `706d599`.

FIX-middle ships (8 commits): cluster 13 MAlonzo erasure surface guards extended (Maybe/Sigma builtins + 8 indirect helper accessors in ffi-exports.snapshot; closes AGDA-D-17.2 by-product) `a47554a`; cluster 11 async cancellation hardening (`asyncio.shield` on init/close + cancel-during-close test) `18b9387`; cluster 7 cross-binding wire-byte parity (Python `ensure_ascii=False`, Go negative-den reject + NaN/Inf reject, C++ GCD-normalising `rational_to_json` + `Delta`/`Tolerance` `double`→`Rational`) `08276a2`; cluster 12 cgo/FFI safety hardening (Go NUL-byte reject + `runtime.KeepAlive`, C++ endian static_assert + Rational throw + extraction-bin via `Rational::make` + `nextafter` overflow boundary + SSOT for `max_can_fd_payload_bytes`, Python `lstat` symlink reject + ZIP-bomb central-dir cap) `7f104c7`; cluster 9 extension points (Go `IsClosed()`, C++ `Logger::add_sink` multi-sink, IBackend `[MANDATORY]`/`[OPTIONAL]` grouping; PY-D-17.1 Backend Protocol deferred) `e909d0f`; cluster 10 API ergonomics asymmetries (DBCVarType/DBCAttrScope Stringer, async `is_closed`, typed `ValidationError`; 6 breaking-change items deferred) `0425550`; cluster 16 Python boundary cleanup (testing.py public path, `check_dbc_text_size_bound` re-exported via `aletheia.client`, Python>=3.13 floor, can_log narrow ImportError; 6 medium follow-ups deferred) `088f3b8`; cluster 8 adversarial-input bound enforcement (kernel + bindings + handler + formatter proofs — 8 sub-phases a/b/c/d/e.1-4 across 22 modified + 1 new module `Aletheia.DBC.Formatter.Bounded`; module count 246 → 247) `5bebba3`; cluster 14 naming sub-batch (5 findings: AGDA-C-3.1 FP — `formatChars` follows `format*` API convention complementing `emit*-chars` per-section family + `formatChars-body` / `parseTextChars-on-formatChars` are load-bearing theorem names with ~80 references; 3.3 `checkDuplicate*`→`checkAllDuplicate*` 51 sites across 6 files; 3.4 `valueEntryList-*`→`valueEntry-list-*` 8 sites; 5.1 drop trailing " in request" from `MissingTypeField`; 5.2 harmonize 3 CAN ID range-errors on "<label> N exceeds limit M" + `DLCExceedsMax` lifted to `maxDLC-FD` literal); cluster 14 internal refactors (AGDA-C-6.5 `parseObjectList-roundtrip` combinator collapses 4 *-list-go templates `25510ef`; GO-A-6.1 `Client.acquire` helper collapses 15-site lock pattern `b3d8b3b`; CPP-A-1.1 `FfiBackend::wrap_str_result` helper collapses 8-site FFI deleter pattern `cb22dce`; CPP-A-6.2 `can_id_value` / `can_id_is_extended` promoted to `<aletheia/types.hpp>` collapsing 14-site `std::visit` + `std::holds_alternative<ExtendedId>` pattern `e42945b`); cluster 14 API-shape refactor AGDA-C-6.2 InputBoundExceeded lift to top-level `Error` (25 files: kernel + 3 bindings + 2 doc sections; wire codes `parse_*`/`frame_*`/`dbc_text_*_input_bound_exceeded` consolidated to single `input_bound_exceeded` with `bound_kind` discriminator) `479fd91`; cluster 14 AGDA-C-6.1 InContext lift + AGDA-C-5.3 missing InContext adjudicated design-held `00e08da` (per-ADT InContext is structurally idiomatic for recursive-ADT contextualization; lifting would change every sub-parser's return-type contract).  Cluster 16 cycle lesson saved as `feedback_circular_reexport_via_sibling.md` — `aletheia.limits` cannot re-export `_types.py`'s helper because `_types.py` imports BOUND_KIND/MAX from limits at the top; sibling public surface (`aletheia.client`) avoids the runtime cycle.

Phase 2 remaining work: cluster 14 (combinator-first refactor batch — LARGE, ~10 sub-themes spanning Agda + C++ + Go), cluster 17 (Python domain model coherence — LARGE, predicate values `float`→`Fraction` + DBCSignal presence discriminator + flat AletheiaError → kind-tagged hierarchy), cluster 18 FIX-late (BRS/ESI plumbing — ~4-6 weeks of cross-binding work; best ordered AFTER cluster 9 so new fields get bound checks + Backend-aware tests in one pass), cluster 19 DEFER-end-of-round (hot-path allocations).  Adjudicated FPs Phase 2: AGDA-A-29.1-4 (already inline-documented), CPP-B-12.4 (audit verified parse_* exception containment).  Reclassified to FIX (folded into cluster 5): AGDA-D-10.3, GO-B-10.1.  Module count 247 (cluster 8 e.4 added `Aletheia.DBC.Formatter.Bounded`).

**Cluster 8 closed 2026-05-11** (defense-in-depth bound checks at parser surfaces; load-bearing closes item d cross-binding parity for all 3 bindings by formal proof rather than C++-only mirroring).  Eight sub-phases shipped: **(a)** `parseJSON` post-parse `jsonDepth` check (`length input` fuel + post-parse refinement, NOT fuel-as-bound — rolled back initial fuel attempt per user "no fuel" preference); **(b)** `parse_dbc_text` inner cap across Python/Go/C++ (3 bindings + cross-binding regression tests); **(c)** Structured `bound_kind / observed / limit` in C++ `AletheiaError` + wire JSON (lifted via `is_input_bound_exceeded_code` discriminator in `make_json_error`); **(d)** C++ `parse_bounded` schema-aware extension — closed by-product of (e.4) not mirrored, per user framing "if we have a kernel proof, all 3 bindings inherit"; **(e.1)** `Identifier` validity-record refinement (3rd conjunct `length name <ᵇ suc max-identifier-length`; cascade tiny — only `Primitives.agda:decompose-valid` needed two `T-∧-split`s); **(e.2)** `parseProperty` atom-count cap (new `atomCount` in `LTL/Syntax.agda`; post-parse refinement); **(e.3)** DBC cardinality caps at the **handler boundary** — first wired inside `parseDBCWithErrors` + `parseMessageBody` and broke ~all roundtrip proofs (`pattern refl` mismatch on new `if-then-else` bind), reverted and moved to `handleParseDBC` / `handleParseDBCText` with `signalsBound` / `firstDBCOverBound` helpers — lesson saved as `feedback_handler_vs_parser_bound_placement.md`; **(e.4)** Formatter length-preservation lemmas in new `src/Aletheia/DBC/Formatter/Bounded.agda` (3 lemmas, ~1 LOC each via stdlib `length-map` + `subst`; wired into `Shakefile.hs` `check-properties` walk; module count 246 → 247).  All gates green: build 2m, check-properties 8m, Python 811p+1s, Go ok, C++ ctest 10/10.  Wire-error refinement AGDA-D-13.4 phase 2a + phase 2b shipped 2026-05-11 same-session as cluster 8 closure: **phase 2a** (`8a81786`) — typed `ParseErr (InputBoundExceeded NestingDepth observed limit)` at the `processJSONLine` handler boundary; structured `bound_kind / observed / limit` triple emitted by `Protocol/ResponseFormat.errorExtras` for every `InputBoundExceeded` constructor across `ParseError` / `FrameError` / `DBCTextParseError`; cross-binding wire-symmetric lifting closed for all 3 bindings (Python `build_error_response` + `ErrorResponse` TypedDict extension, Go `inputBoundExceededFromResponse` + `*InputBoundExceededError` via `errors.As`, C++ already had `make_json_error` since cluster 8c).  Kernel end-to-end tests added to Python `TestNestingDepthBound::test_nested_at_depth_63_rejected`, Go `TestCrossBinding_NestingDepthLiftsToInputBoundExceeded`, C++ `nesting depth over limit lifts to InputBoundExceeded`.  **Phase 2b** — same handler-boundary playbook applied to atom-count: `parseProperty` (LTL/JSON.agda) now returns just the structural parse (dropping its post-parse bound check); `parseAllProperties` (Protocol/Handlers.agda) inserts the `atomCount prop <ᵇ suc max-atom-count-per-property` discriminator and emits typed `ParseErr (InputBoundExceeded AtomCount observed limit)` on overflow (was untyped `HandlerErr PropertyParseFailed` pre-2b — conflated shape-malformed with shape-OK-but-over-bound).  Manual over-bound verification 2026-05-11: 1025-atom balanced And-tree → `code=parse_input_bound_exceeded` + `bound_kind=atom_count` + `observed=1025` + `limit=1024` (109.2s elapsed; existing test docstring documents the timing budget, so over-bound case stays manual-only — CI test exercises acceptance path).  Phase 2b shipped `0a50989` (closes R19 cluster 8 phase e.2 typed-error half; cross-binding tests deferred to NestingDepth lifter proxy per BoundKind-generic lifter design + inline comments in Go + C++ files).  Phase 2c (`IdentifierLength`, requires parser-monad rewrite — genuinely invasive, deferred pending approach choice with user) still pending.  Pre-existing O(N²) `parseDBC` scaling (51s @ 1000 messages, >30min @ 10001) prevents canonical-limit over-bound CI tests — bound is verified by code inspection + per-binding under-bound acceptance tests; lesson saved as `feedback_parsedbc_quadratic_scaling.md`.

**Memory-bound build infra shipped 2026-05-11 via `43fcd4b`** (separate from cluster 8 scope; OOM-suspected shell crash prompted): `cabal build` capped at `-j16 --ghc-options="+RTS -A64M -M3G -RTS"` (worst-case peak 48 GB on a 62 GiB host; was unbounded `-j` × multi-GB workers).  Plus 4 doc-drift fixes adding the canonical `-M16G` to recommended `agda +RTS` invocations (CLAUDE.md:232, BUILDING.md:564/586/587).  Lesson saved as `feedback_parallel_memory_budget.md` — caps must hold at every spawned layer; N×peak budget against WSL2's ~30 GiB practical limit, not the 62 GiB host total.

**Prior R18 review round** merged via `4518fef` (`--no-ff` per project convention) onto `main` 2026-05-09 after all 17 hard clusters + end-of-round basedpyright `benchmarks/` promotion closed.  17 review agents → ~610 findings → 17 clusters ranked FIX-early / FIX-middle / DEFER-end-of-round per `memory/feedback_review_round_dispositions.md`.  **Rounds 1-10 + all 17 hard clusters CLOSED + end-of-round follow-up CLOSED**; **112 hard findings closed cumulatively** (cluster 17 contributes 2: AGDA-B-22.1 CANId proof-field `.(…)` irrelevance migration + AGDA-D-11.3 close-related-domain-types asymmetry by-product; end-of-round basedpyright `benchmarks/` promotion: 282 → 0 errors).  Final orchestrator e2e on the post-merge tip: ALL 27 STEPS PASSED in 18m35s (`tools/ci-output/ci-review-r18-2026-05-09T07-23-55Z.log`, falsifiable evidence per `feedback_gate_claim_integrity.md`).  Per-cluster commit hashes + scope detail + gate logs live in `memory/project_review_round18.md` and PROJECT_STATUS.md.  Local `main` is 59 commits ahead of `origin/main`; not yet pushed (per CLAUDE.md "never push without explicit user direction").

**Cluster 7 closed 2026-05-09** — mutation testing infrastructure across all 3 bindings (`mutmut` Python, `gremlins` Go, `Mull` C++) + `tools/run_ci.py` CLI overhaul (argparse with `--full` / `--san` / `--repro` / `--stability` / `--mutation` flags + paired `--no-<lane>` + env-var fallback) + `docs/operations/MUTATION.md` procedure doc + `docs/MUTATION_BENCH.yaml` SSOT + `tools/check_mutation_setup.py` static gate (Shake `phony "check-mutation-setup"` + `tools/run_ci.py` step 13 always-on) + `tools/mutation_run.py` dynamic runner (opt-in via `--mutation` / `ALETHEIA_MUTATION_CHECK=1`).  Baselines established 2026-05-09: **Python 65% / 1478 mutants / 496 survivors**; **Go 100% / 662 mutants / 0 survivors**; **C++ 56% / 39 mutants / 17 survivors**.  AGENTS.md cat 14(g) names `go-mutesting` for Go but it's unmaintained since 2021 and panics on Go 1.26 internals; substituted with the actively-maintained `gremlins` (same operator set).  Mull-19 + clang-19 chosen because Mull releases lag LLVM by 2-3 versions; clang-21 is system default but Mull-19/LLVM-19.1.7 + apt clang-19 is the working pair.  Tool-install steps documented in CLAUDE.md § Development Environment + `docs/development/CI_LOCAL.md` § Opt-in lanes + `docs/operations/MUTATION.md` § Installation.  Survivor lists per binding archived in `benchmarks/mutation/<short-sha>/<binding>.raw.txt`; eliminating them is separate follow-up backlog (per AGENTS.md "an unjustified survivor is a test gap" — each is its own finding).  Side-effect: this commit also includes a pre-existing CLAUDE.md compaction from earlier in the same session (per `feedback_pre_commit_scope_check.md` 2-question gate; the compaction was structurally unrelated but the diff was already in flight when cluster 7 work landed on the same file).

**Three follow-ups shipped 2026-05-09 same-session as cluster 7:**

1. **Cluster 6 second follow-up `44d7aee`** — stability bench warmup 1 → 7 cycles in both Python (`python/benchmarks/stability.py`) and C++ (`cpp/benchmarks/stability_bench.cpp`).  Cluster 7's first orchestrator e2e (with `+stability`) failed at step 30/30 — Python harness reported ~137-154 MiB RSS leak, C++ ~138 MiB, both above the 50 MiB soft threshold.  Root cause: cluster 6's single-cycle warmup (Python 10 frames, C++ 100 frames) was far too short to reach GHC RTS heap steady state; MAlonzo dictionary realization + lazy Agda structure construction settle around cycle 7 of 100k-frame batches.  Fix: warmup loop now runs `7 × frames` cycles (~700K frames) before measurement opens.  Verified Python 9.21 MiB / Go 0.009 MiB / C++ 11.26 MiB RSS Δ — all well under cap.  Go was unaffected (`FFIBackend.Init` runs `hs_init` once at process start; subsequent harness cycles incur no RTS heap growth).  Cluster 6 closure narrative remains accurate (gates exist, fire correctly, now pass) — this is harness initialization tightening, not a re-opening.

2. **Cluster 7 follow-up `003f97b`** — `tools/mutation_run.py` + `tools/check_mutation_setup.py` code-quality cleanup.  `MutationReport` dropped redundant `total_mutants` / `score_pct` required fields, promoted to `@property` derived from `killed + survived`; removed unused `_score()` helper; extracted `_check_cpp_tools() -> str | None` for the three mull-19/clang++-19/mull-ir-frontend-19 prereq checks (collapsed three near-identical early-return guards into one); removed unused `_hot_path: list[str]` parameter from `run_go`; added module-level docstrings; pre-compiled the section-header regex.  No behavior change.

3. **Cluster 7 second follow-up `32932bd`** — promote `python/benchmarks/` into the pylint gate.  Surfaced when `44d7aee`'s commit message claimed `pylint scope excludes python/benchmarks/` — the exclusion turned out to be a leftover from review round 12 (`60661a1` 2026-04-12) that `feedback_pylint_10_mandatory.md` later overrode for `tests/` only; `benchmarks/` was never re-litigated.  Per `feedback_no_subsumption_asymmetry.md` this is the kind of leftover the codebase shouldn't carry.  Closed via real refactor (no suppressions): NEW frozen dataclasses in `python/benchmarks/_common.py` — `FrameSpec` (bundles `can_id` / `dlc` / `payload` / `signals`; pre-built `CAN20_SPEC` / `CANFD_SPEC` instances drop too-many-arguments on every per-frame helper from N+3 to N+0); `BenchmarkConfig` (CLI knobs); `LatencyContext` (per-suite parameter bundle for `latency.py`); `MemorySnapshot` / `ThroughputSnapshot` (in `sysinfo.py`).  NEW shared helpers — `DEFAULT_CAN20_PROPERTIES` / `DEFAULT_CANFD_PROPERTIES` (closes R0801 duplicate-code across throughput / latency / scaling); `stream_frames` / `run_streaming_benchmark` / `emit_json_report`.  **Real-bug fix in `violations.bench_cli`** (W0632): was unpacking 2 of 3 return values from `aletheia.cli._run_checks` (returns `(violations, unresolved, total_frames)`), silently using `unresolved` (typically 0) as the FPS divisor — the prior CLI lane fps numbers were wrong.  Now unpacks all 3 and divides by `total_frames`.  11 missing docstrings added; `.format()` → f-string in simplification.py:249; useless `f` prefix removed from sysinfo.py:124.  Gate config: `python/pyproject.toml` `[tool.pylint.main].ignore` dropped `"benchmarks"`; `tools/run_ci.py:463` extended to `pylint aletheia/ tests/ benchmarks/`; AGENTS.md Python scope expanded.  All 8 benchmark scripts smoke-tested end-to-end after refactor.  10.00/10 on `aletheia/ tests/ benchmarks/`.

**Cluster 17 closed 2026-05-09** — CANId proof-field `.(…)` irrelevance migration per AGENTS.md G-A4 (the canonical example named in the guideline).  `CAN/Frame.agda:39-41` migrated `T (n <ᵇ standard-can-id-max) → CANId` slot from relevant to `.(…)`-irrelevant.  `_≟-CANId_` collapses from `cong (Standard x) (T-irrelevant p q)` to bare `yes refl` after `≟ ℕ`.  MAlonzo output: `data T_CANId_8 = C_Standard_12 Integer | C_Extended_16 Integer` (was `Integer AgdaAny`) — proof cell erased.  **Cascade scope much larger than the finding's "Medium effort" estimate** — surfaced to user mid-cluster, user approved bite-the-bullet propagation: (1) `Prelude.ifᵀ-witness` accepts `f : .(T b) → A` and `.(pf : T b)` (LHS `(λ p → f p)` η-bridge keeps `ifᵀ_then_else_`'s relevant `f` arg unchanged so DLC `mkDLC n p` and DecRat lambdas keep working); (2) `IntDecRat.isInt` and `NatDecRat.isNat` `.(…)`-migrated as cascade — `cong (mkX _) (T-irrelevant ...)` simplifies to `refl` via record η on irrelevant fields; (3) helper signatures in `MetadataRoundtrip.agda` + `MessageRoundtrip/{Standard,Extended}.agda` take `.(pf : T (...))`; (4) `Comments/Comment.agda` adds local `T-materialize : (b : Bool) → .(T b) → T b` (irrelevant absurd `()` on `T false`) + local `<ᵇ⇒<-irr : ∀ m n → .(T (m <ᵇ n)) → m < n` to bridge stdlib `<ᵇ⇒<` (which requires relevant input); (5) Marshal.hs / ConstructorTest.hs drop the `unsafeCoerce ()` second arg; (6) Shakefile.hs `check-erasure` updated to assert single-Integer ctor shape (was asserting `Integer AgdaAny`).  **AGDA-D-11.3 closed as by-product** (per advisor): runtime-layer asymmetry resolved (CANId proof field and `DLC.bounded` both compile to no runtime cell post-cluster-17); mechanism asymmetry (`.(…)` vs `@0` are orthogonal Agda primitives) deliberately preserved — DLC's record has η so `@0` works there, CANId's data ctor doesn't have η so `@0` would have left `_≟-CANId_` requiring relevant proof access.  Cat 16 hot-path bench clean: Stream LTL +14-28% across all 3 bindings (matches cluster 2's post-Track-A-D pattern); CAN-FD Signal Extraction / Frame Building -4.7% to -8.1% identical to cluster-2's WSL2 noise floor + Path-A geometry — NOT a cluster-17 regression.  Closes 2 hard findings (AGDA-B-22.1 + AGDA-D-11.3).  Module count 246 unchanged.

**End-of-round follow-up CLOSED 2026-05-09** — `python/benchmarks/` promoted into the basedpyright gate.  282 errors at start (lower than the 325 documented at cluster 7 closure due to cluster 7 second follow-up's intervening refactors) → 0 errors.  Scope: typed every `dict` / `list[dict]` parameter and return through `DBCDefinition` / `LTLFormula` / new per-file `_BenchResult` / `_LatencyStats` / `_FormulaResult` TypedDicts; replaced 7 `reportImplicitStringConcatenation` callsites with explicit `+`; promoted `aletheia/cli.py` `_run_checks` / `_Violation` → public `run_checks` / `Violation` and added a NEW `aletheia.testing` module re-exporting them (per `feedback_test_interface_via_di.md`); added a NEW `AletheiaClient.is_closed` property so stability harness can drop its `pylint: disable=protected-access` access into `_state`; promoted `excel_loader.py` `_DBC_HEADERS` / `_CHECKS_HEADERS` / `_WHEN_THEN_HEADERS` → public, dropping the 3 R0801 duplicate-code rows test_excel_loader carried; extracted `tests/_yaml_shape.py:as_str_object_dict` and `tests/_dbc_helpers.py:assert_non_terminating_rational` to dedupe the remaining R0801 between test pairs; added `tools/run_ci.py:basedpyright` step `benchmarks/` and AGENTS.md scope line.  Side-effect 1: pylint's R0801 cluster on the test side was already breaking 10/10 at cluster 7 second follow-up `32932bd` (gate-claim integrity issue per `feedback_gate_claim_integrity.md` — actual baseline was 9.97/10) so this commit ALSO repairs that to a real 10.00/10.  Side-effect 2: `aletheia/testing.py` collides namespace with the FEATURE_MATRIX `mock_backend` row's "promoting to aletheia.testing is a separate design decision" hypothetical; matrix reason text updated to acknowledge the namespace exists for an unrelated purpose.  Final gates: `basedpyright aletheia/ benchmarks/` 0/0/0; `pylint aletheia/ tests/ benchmarks/` 10.00/10; pytest 790 passed; all 8 benchmark scripts smoke-tested end-to-end.

Module count drift this round: 244 → 245 (cluster 14 — `Aletheia.DBC.TextParser.WellFormed` extracted) → **246** (cluster 2 — `Aletheia.Limits` extracted hosting `BoundKind` + 11 numeric bounds + 7 wire codes for UR-2 adversarial-input bounds).

**Track E (VAL_ promotion to `DBCSignal.valueDescriptions`) ✅ COMPLETE 2026-05-08** on branch `b3d-3d5-format-dsl` — E.1→E.12 shipped as a single Plan-A bundled commit. Module count 237 → **244** + 1 new Python `aletheia/validation.py`. Three load-bearing constraints from advisor 2026-05-04 — **C1** encounter-order via `(message-index, signal-index, val-desc-index)`, **C2** `attachValueDescs ∘ collectFromMessages ≡ id` (CM_-class proof), **C3** Python `dbc_to_text` defers to Agda via FFI command (`formatDBCText`) — all closed. Per-sub-phase tactical detail + architectural patterns live in `memory/project_track_e_val_promotion.md`.

**Earlier 2026-05-07**: naming-hygiene rename (parity-plan **Phase A–E → Track A–E** across 79 files + 23 memory files; "Phase" was reused for two unrelated structural systems); Phase 6 goal-set pinned (CLI parity stretch + python-can replacement + GHC `--bignum=native` rebuild + SOME/IP); R17-DEF-1 (FFI `unsafeCoerce` drift guard) closed via comprehensive check-fidelity coverage on all 11 FFI exports; R17-DEF-2 (DBC metadata depth) closed via re-verify against the Agda DBC truth set. **All R17 deferrals now closed.**

**Standard gates passed at every closure** — `cabal run shake -- {build, check-properties, check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity, check-ffi-exports, count-modules, check-runbook, check-stability-bench}` + Python `pytest tests/` + Go `go test ./aletheia/ -count=1 -race` + C++ `ctest --test-dir cpp/build` + lint gates (basedpyright / pylint 10/10 / gofmt + go vet / clang-format + clang-tidy). Per-closure gate logs live in PROJECT_STATUS.md.

## Prior Phases (closed) — see PROJECT_STATUS.md for narratives

- **Track D ✅ COMPLETE 2026-05-04** — cross-binding doc-example harness (Python `pytest --markdown-docs` + Go `TestDocExamples` + C++ Catch2 `doc_example_tests`); R17-DEF-6 closed by D.2 `d0ae26b` + D.1 `82d0347`. Every ```cpp``` / ```go``` / ```python``` fence in tracked markdown files runs end-to-end against the real Agda core; harness immediately surfaced multiple dead doc API references.
- **Track C ✅ COMPLETE 2026-05-03** — cancellation contract bound across all 3 bindings: C.0 SSOT `05108cf` + C.3 Go ctx `eef9dcc` + C.4 C++ stop_token `ef1292d` + C.1+C.2 Python async + send_frames_iter `c8ab95b`. Cancel at FFI boundaries; commit-prefix-and-report; behavioral parity by language idiom. FEATURE_MATRIX `cancellation_contract`/`lazy_streaming_batch` × 3 rows flipped. See `memory/project_track_c_cancellation.md`.
- **Track B.3 ✅ COMPLETE 2026-05-03** — universal roundtrip (B.3.d `bca99f2`) + JSON binding + ParsedDBCResponse + C++/Go bindings (B.3.e/h/i `bc7a5fc`) + cross-binding parity gate (B.3.j `3673cd2`+`3404dec`) + Python migration to verified parser (B.3.f `019d014`) + cantools dropped (B.3.g `2daa2fb`). LGPL contingency for cantools fully realised.
- **B.3.d universal target** — `∀ d → WellFormedDBC d → parseText (formatText d) ≡ inj₂ d` proven in `Substrate/Unsafe.agda` (sole axiom consumer; co-located by Unsafe-module policy — see `memory/feedback_unsafe_module_policy.md`). Layer 3 fully migrated to Format DSL (BO_ / ValueTable / BU_ / EV_ / CM_ / Preamble / BA_DEF_* / BA_*); Layer 4a/4b/4c-(a)/(b)/E all closed.

## Format DSL toolkit (`DBC/TextParser/Format.agda`)

- **Core constructors**: `literal` / `ident` / `nat` / `stringLit` / `pair` / `iso` / `many` / `refined` / `altSum` / `withPrefix`.
- **Whitespace family** (each with distinct parser permissiveness — see `feedback_format_dsl_ws_family_discipline.md`): `ws` / `wsOpt` / `wsCanonOne` / `wsCanonTab` / `withWS` / `withWSOpt` / `withWSCanonOne` / `withWSCanonTab` / `withWSAfter`.
- **Refinement carriers**: `decRat` / `intDecRat` / `natDecRat`.
- **Sugar**: `discardFmt` (wire-only fields) / `nonNewlineRun` (opaque-tail consumer) / `newlineFmt` (LF/CRLF).
- **Cycle-break pattern**: when a Format module would close a cycle, extract cycle-relevant subset to a `Foundations.agda` submodule (used at 3d.5.c-ε / 3d.5.d-3c-A).

## Performance baseline

Path A profile (post-3d.4 + JSON-mirror, runtime impact retained from `320c5a9`): Stream LTL +12-38% across bindings (Bool fast path); Signal Extraction -2-9% / Frame Building -1-7% (Path A structural cost). All 3d.5+ Format DSL work + Track E sub-phases are proof-only and runtime-neutral on the streaming hot path. Baselines NOT refreshed per user "wait and see" 2026-04-28; COMPILE-pragma escape hatch deferred (requires explicit user approval per `feedback_no_suppression_without_approval`).

**Cross-binding parity roadmap**: [docs/development/PARITY_PLAN.md](docs/development/PARITY_PLAN.md), locked after R17. **R17 deferrals all closed**: R17-DEF-1 (2026-05-07) by comprehensive check-fidelity coverage; R17-DEF-2 (2026-05-07) by re-verify against the Agda DBC truth set — B.1 Tier 1 + B.1.x Tier 2 + B.1.x commit-3 senders + Track E VAL_ ship every `DBC` / `DBCSignal` / `DBCMessage` field across all 3 bindings, with FEATURE_MATRIX rows (`dbc_metadata_tier1` / `_tier2` / `dbc_signal_receivers` / `dbc_message_senders` / `dbc_signal_value_descriptions` / `dbc_text_format`) + per-binding parity tests + CHECK 23 `unknown_value_description_target` IssueCode mirror; R17-DEF-3 by Track C.2; R17-DEF-4 by Track B.3; R17-DEF-5 by Track C.3; R17-DEF-6 by Track D.
