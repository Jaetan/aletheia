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

**Size budget**: after the sweep, check `wc -c CLAUDE.md`. If it exceeds **40.0 kB**, compress in the same UPD commit — push per-cluster narrative detail into the appropriate `memory/project_*.md` file (e.g. `project_review_round20.md`) and replace with a one-line index pointer, mirroring how prior rounds compressed (e.g. R6-B8.2's `970f704` compression of Current Session Progress). The compression IS doc-state sync; do not split into a separate commit.

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

265 total modules (`cabal run shake -- count-modules`):
- **260**: `--safe --without-K`
- **4**: `--safe --without-K --no-main` (Main.agda, Main/JSON.agda, Main/Binary.agda, Parser/Combinators.agda)
- **1**: `--without-K` only — `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`, the allowlisted Unsafe substrate hosting the two `String ↔ List Char` bridging axioms (`toList∘fromList`, `fromList∘toList`) AND the B.3.d outer-wrap `parseText-on-formatText` consumer — co-located here to keep the trusted-axiom-consuming surface at one allowlisted module (mirrors stdlib's `Data.String.Unsafe`; structurally unprovable in `--safe --without-K` because Agda's String primitives reduce only on closed terms).

264 of 265 modules use `--safe`. No modules require `--sized-types`. Per-commit module-count drift (Path A.4 cluster lift, Track E sub-phase additions, R18 cluster 14 extraction, R18 cluster 2 `Aletheia.Limits` extraction, R19 Phase 2 cluster 8 `Aletheia.DBC.Formatter.Bounded` extraction, R20 cluster V `Aletheia.DBC.BoundWalks` extraction, R20 cluster Y stage 2 `Aletheia.DBC.RationalRenderer` (+`.Properties`) lift, R21 cluster 9 `DecRatParse/Properties` split into 5 phase submodules, R21 cluster 9 follow-up `Properties/Primitives` split into MuxMarker + Bools sibling submodules at `543acee`, R21 cluster 9 follow-up `Format` split into `Format/RegressionTests` sibling at `000761b`, R21 cluster 9 follow-up `Format/AttrDef` split into `Format/AttrDef/HeadHelpers` at `9421604`, R21 cluster 9 follow-up `Aggregator/Dispatcher/Attribute/Assign` split into `Assign/Bridges` at `9c7740d`, R21 cluster 9 follow-up `Refine/ValueDescriptions` split into `ValueDescriptions/UnresolvedRVDs` at `627ad25`, R21 cluster 9 follow-up `Properties/Attributes/Line` split into `Line/Alt5` at `5b48948`, R22 AGDA-D-15.1 final closure `Format/AttrLine` split into `Format/AttrLine/Builders` at `0b360fd`, R23 AGDA-D-10.1 `Protocol/Handlers/Properties` routing-proof addition at `050ba2f`, ci-speed renderer-proof linchpin `DecRat/RationalSoundness.agda` addition (264→265), etc.) is recorded in PROJECT_STATUS.md and `memory/project_b3d_universal_proof.md` / `memory/project_track_e_val_promotion.md` / `memory/project_review_round18.md` / `memory/project_smart_rational_renderer.md` / `memory/project_review_round21.md`.

## Common Commands

See [Building Guide](docs/development/BUILDING.md). Quick reference:

```bash
# Type-check a single module
cd src && agda +RTS -N32 -M16G -RTS Aletheia/YourModule.agda

# Build everything (Agda → Haskell → libaletheia-ffi.so)
cabal run shake -- build

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

Wraps `libaletheia-ffi.so` via `dlopen`. `IBackend` interface; `MockBackend` for tests. Strong types (`std::byte`, validated newtypes, `std::expected`). Custom `Logger` (~90L, callback-based, 16 event types matching Go's slog, zero-cost when null). RTS cores via `make_ffi_backend(path, rts_cores)` (default 1, once-per-process with mismatch warning). C++23, targets g++>=14 / clang>=21. Style: `.clang-format` + `.clang-tidy`. Inventory: [PROJECT_STATUS.md § Key Metrics](PROJECT_STATUS.md#key-metrics).

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

**Active branch: `ci-speed`** — forked from `main` at `f6025e8` (post-R23 merge, 2026-05-26).  Module count **265** — the renderer-proof linchpin `DecRat/RationalSoundness.agda` is this branch's first Agda module (264→265); prior CI-speed work was tooling (Python/Shakefile).  Live commit count: `git rev-list --count main..HEAD` per `feedback_self_referential_count_drift.md`.

**2026-06-07 — pre-merge items 1–3 DONE (9 commits; full detail `memory/project_ci_speed_optimization.md`)**: **item 1 + namespace review** (`06343c0`→`1287459`) — `aletheia` is the sole public package (`aletheia.client`→internal, no public re-exports, guard test locks it); `__all__` hygiene; domain sub-namespaces unified/renamed (`dbc_converter`+`dbc_queries`→`dbc`; `error_codes`+`issue_codes`→`codes`; `protocols`→`types`, 83-file); top-level convenience-complete (Tier 2=A, 50 names).  A first over-aggressive pass (demoting dsl/loaders too) was REVERTED — meaningful sub-namespaces are good; the only smell is a name defined in a PRIVATE module + a redundant 2nd public facade (only `aletheia.client` had it).  **item 2 Fraction-pipeline** — `2db0b68` drop `RationalNumber` (`property_index`/`timestamp`→`int` at parse boundary, RESTORES Go/C++ parity — Python was the outlier) · `4d66870` `JSONValue` type + loader getters→covariant `Mapping[str,JSONValue]` (~71-err cascade resolved NO casts/NO object via `dict.update()` widening) · Chunk C verified no-op (float ingress-only; internal+output `Fraction`; output FORMATTING FFI-unified via `aletheia_format_rational` — byte-identical across bindings, user-flagged, untouched).  **item 3 opaque-type sweep** — `69f7999`+`48017dc` (tree already ~clean — ZERO opaque returns; fixed `tuple[str,str,str]` whitelist→`PrivateImport` NamedTuple, `cli` signal-unit `type` alias, benchmark (name,X)→NamedTuples).  All gates green per commit (ruff(ALL)/bp-0/pylint-10/4822p/doc-harness/mutation/changelog).  **Pre-merge program: items 1–3 ✅; NEXT = item 4 (renderer-proof — exploratory; renderers already FFI-delegate, so it's the Agda-theorem/test-tightening question) → branch/PR-hygiene → merge `ci-speed`→main.**

**2026-06-06 (later) — pre-merge "where do we stand" audit + lint-gate ENFORCED + CL10-2 (2 commits)**:
- `66ba302` **lint gate enforced** — `ruff` (`check` + `format --check`, `select=["ALL"]`) is now a run_ci step over the whole Python tree INCL `tools/` (BASE_STEPS 32→33, renumbered); `../tools/` added to the pylint + basedpyright steps.  ruff(ALL) + tools/ were enforced NOWHERE before (campaign done-but-unprotected).  ruff.toml `extend-exclude=["python/mutants"]` (mutmut generated).  Verified green tree-wide; runner.step 36 == 33+3.
- `60296fa` **CL10-2** — Go `BuildFrame(ctx,id,signals,dlc)` → `(ctx,id,dlc,signals)` (matches UpdateFrame + Python/C++ `build_frame(id,dlc,signals)`); Go-only; 6 call sites; in-source DEFERRED block removed; CHANGELOG 2.0.0 breaking entry; gofmt/build/vet/`go test` green.
- **Audit correction**: R23 = 57/57 closed, **ZERO carry-overs** — the 2 C++ items first mis-flagged as deferred (CPP-D-15.1/15.2) were already DONE in R23 (`8aff66b`/`e15d7d8`; `class Rational`, `namespace check`).  **REMAINING pre-merge program** (full detail in `.session-state` LATEST⁸): (1) AletheiaError dual-path → (2) Fraction B/C + loader JSONValue [[project_object_sweep]] → (3) opaque-sweep [[project_opaque_type_sweep]] → (4) renderer-proof [[project_rational_renderer_proof]] → branch/PR-hygiene → merge.  PARKED deliberately: CL10-3 (Go FormatDBC speculative; note `client.go:396`) + Agda-`Fin` (MAlonzo Peano perf hazard).

**2026-06-06 — IWYU CUTOVER + CONSOLIDATION DONE: the `.agdai` reader is THE CI import gate; oracle RETIRED; obsolete tools DELETED; ONE tool `tools/iwyu.py` (5 commits `dafcfae`→`c27b7b2`)**:
- User: the `.agdai` reader is the keeper, all other import-resolution obsolete; then "one aggregated tool for the whole import story".  **`tools/iwyu.py`** = the single public tool (`--check` gate = named+wildcard in ONE warm load / `--apply` wildcards / `--self-test` fixtures) + **`tools/_iwyu.py`** = engine + **`tools/_warm.py`** = WarmAgda infra + `tools/agda-iwyu-reader/` (Haskell, store `package.db` build).
- **DELETED** (all superseded by the reader): `warm_dead_imports` / `prune_unused_imports` / `warm_prune` / `warm_apply` / `_dead_edit` / `_agda_imports` / `scan_dead_imports`(+.ignore) / `test_warm_dead_imports`.  **Oracle RETIRED** — the reader's correctness rests on `--self-test` (synthetic fixtures 31/31), now WIRED into CI (run_ci step 10; was enforced nowhere — advisor-caught).
- run_ci steps 9-10 = `iwyu --check --diff` + `iwyu --self-test` (BASE_STEPS stays 32); pre-commit hook = `iwyu --check` advisory.  `dafcfae` first removed the SignalList dead wildcard (aliased-dup edge: NARROWABLE-mislabel, actually DEAD — verified by removal+recompile).  ruff(ALL)/format/bp-0-0-0/pylint-10 on all IWYU modules; `--check` exits 0 clean / 1 on injected dead.  **NOT merged** (task 3: deferred/review items remain).  Full detail: `memory/project_agda_iwyu.md` (2026-06-06).
- *(Superseded history)* 2026-06-04's dead-import gate (warm_dead_imports sieve + recompile-confirm, `15f23d9`/`2e5adcb` apply-fixpoint + convergence) and the GREENLIT `.agdai` reader R&D are the predecessors of the above; recorded in `memory/project_agda_iwyu.md`.
- **Branch/PR-hygiene enforcement — PLAN SAVED, DEFERRED**: local hooks enforce gates *by convention* (bypassable `--no-verify` + opt-in install); to enforce server-side = a required `pull_request` check running full `run_ci.py` on GHA + branch protection (repo is PUBLIC ⇒ Actions free).  Plan + untested v1 workflow draft (toolchain via ghcup, C++/LLVM footgun, `--diff`-vs-`--all` choice, rollout order) in `docs/development/BRANCH_PR_HYGIENE.md` (`5116d6a`); revisit before/with the `ci-speed`→main merge.  Fixed a pre-existing `gha-checks.yml` meta-gate bug in passing (`feeac9f`: invoked `python3 tools/check_*.py` → ModuleNotFound post-`-m`-migration; now `python3 -m tools.<check>`).

**2026-05-31 — check-properties→warm rename (`1a569a2` — the warm process IS the `check-properties` target now, ~13× 629s→39s) + tests/ ruff(ALL) COMPLETE (166→0, `5848e00`/`6c3ec4f`/`1869b3e`, S103-via-`Path.chmod` lesson in [[feedback_ruff_all_lint_campaign]]) + the dead-import gate reframed to the full `.agdai` IWYU R&D** (warm_iwyu wildcard-narrowing built `8fed3d8`/`fbd8999`/`a408f8f` then SUPERSEDED by the 2026-06-04 reader → the 2026-06-06 cutover above; warm_iwyu deleted).  Detail: `memory/project_ci_speed_optimization.md` + `memory/project_agda_iwyu.md`.  (Sub-agents are Bash-denied at session level — can't run ruff/pylint; do lint yourself.)

**2026-05-29 (later) → 05-31 — `python/tests/` ruff(ALL) + Fraction-pipeline Chunk A + basedpyright-gate expansion (15 commits)**: tests/ ruff(ALL) 166→0 (6 groups; wide rows→`tests/_excel_helpers.py`; new rule [[feedback_no_object_type_escape]]); Fraction Chunk A (`b3eddf4`→`e8f0130` — ONE internal `Fraction`, `_enrichment` retyped, weakNext cross-binding parity fix); tests/ basedpyright-gate 415→0 + wired into run_ci (`36c86cd`).  Detail: `memory/project_ci_speed_optimization.md`.

**2026-05-29 — `python/aletheia/` root-level slice COMPLETE (6 commits `8431a8d`→`696990d`)**: whole-tree ruff(ALL) package phase, one commit/file (checks_runner/checks/yaml_loader/excel_loader/cli/dsl), serial per [[feedback_wsl2_crash_resource_discipline]]; `python/aletheia/` (root + asyncio/ + client/) ruff(ALL)+pylint-10+bp-0/0/0 clean.  Patterns (T201→`_emit()`, ERA001 em-dash, R0801 break-via-rename, PLR2004→named-const, scripted D400/D415) folded into [[feedback_ruff_all_lint_campaign]]; full per-file detail in `memory/project_ci_speed_optimization.md`.

**2026-05-28 (later) — User crash directive + review-mark sweep**: User flagged 4 WSL2 crashes during long Claude sessions; new rule [[feedback_wsl2_crash_resource_discipline]] — commit often, serial-by-default, cap parallelism ≤2-3, budget-check before heavy ops, no `run_ci` / full check-properties / full bench unless asked.  5 commits this session: `a7ba765` (4-file root-deps ruff(ALL)), `5156c78` (asyncio/ review-marks), `fcbe717` (foundation + __init__ review-marks), `148bb29` (client/ review-marks, ~40 sites), `4680394` (tools/ review-marks, ~41 sites).  ~120 marks total stripped from already-ruff-clean dirs.  **New rule [[feedback_no_review_process_marks_in_code]]**: round refs (`R20`), finding IDs (`PY-D-24.1`), cluster labels (`cluster P`), agent labels don't belong in production source — they make code harder to read and rot fast.  Backward sweep on uncleaned dirs folds into ruff(ALL) commits per the agreed plan.

**R23 ✅ MERGED to main** (merge `4cb5220` + finalize `f6025e8`, 2026-05-26; 57/57 findings: 54 FIX + 3 FP-VERIFIED).  Headline AGDA-D-10.1 (`SignalPredicate.signalName : List Char → Identifier`; reason-carrying JSON parser, forked validity walk removed; handler verdict→wire-error routing PROVEN in `Protocol/Handlers/Properties.agda`).  Per-round detail in `memory/project_review_round*.md`; per-finding YAML at `.archive/reviews/r23/findings/`.

**CI-speed gate optimization** (post-R23 user directive — *gates must be fast so every prospective contributor runs them, manually + often*; full detail in `memory/project_ci_speed_optimization.md`).  **Commits on `ci-speed`: `git rev-list --count main..HEAD`** (warm-process work + 2026-05-27 lint campaign + 2026-05-28 review-mark sweep + 2026-05-30→31 tests/ basedpyright-gate to 0 + wiring).  The **basedpyright gate includes `tests/`** (`36c86cd`); **warm `check-properties` is now THE proof gate** (`1a569a2` — auto in `run_ci`); the **`tools/` lint steps** are still not wired into `run_ci`; the **import gate is the `.agdai` reader `tools/iwyu.py`** (run_ci steps 9-10; the recompile/sieve/prune tools were DELETED + the oracle retired 2026-06-06 — see [[project_agda_iwyu]]).
- **Core insight**: ONE warm `agda --interaction-json` process loads stdlib + shared interfaces ONCE (vs ~14s per-invocation reload × N) — directly attacks the user's "calling Agda too often" hypothesis.
- **Steps 9-10 (the IWYU gate)** — `tools/iwyu.py --check --diff` judges named + wildcard imports via the `.agdai` reader in ONE warm load (no recompile-confirm), + `iwyu --self-test` runs the fixture matrix.  Replaced the recompile/sieve `warm_dead_imports` gate 2026-06-06; the reader reads `iSignature`/`iHighlighting`/`iInsideScope` so it sees inferred-use cases the old highlighting sieve over-flagged.  Detail: [[project_agda_iwyu]].
- **Steps 1-8 (check-properties, was 629s)** — `tools/warm_check_properties.py` IS the `check-properties` Shake target now (cold batch deleted, `1a569a2`): all 45 proof modules in one warm process, **~13×** (629s → ~40s). Equivalence verified (catches proof-obligation failures; writes `.agdai`; single-source `proofModules :: [String]`).
- **#1 production-usability ✅** (`1312115`): portable (no hardcoded paths — reuses prune's repo-root `SRC_DIR`/env `AGDA_BIN`; `tools/` is now a package, invoked `python -m tools.X`); pylint 10.00 + basedpyright 0/0/0 (no disables).
- **Lint-compliance campaign ✅ tools/ (2026-05-27)** — all of `tools/` now passes **ruff `select=["ALL"]` + pylint 10.00 + basedpyright 0/0/0**, **zero suppressions** (user: "state of the art rigorous", fix don't suppress).  Root `ruff.toml` (minimal each-rationale'd ignores + `allowed-confusables`; flagged **S603** as the lone judgment-ignore — no structural fix); full `python -m tools.X` migration (Shakefile + run_ci + install_hooks); `tools/_common.py` (shared helpers) + `tools/_agda_imports.py` (prune substrate split — clears C0302); the 3 module-level `# pylint: disable` removed via refactor; `eval`→safe-AST evaluator (`check_limits_parity`); `oneshot_dead_imports.py` deleted.  Done largely via parallel agents (verify each).  **Whole-tree package phase IN PROGRESS** — pattern proven on `dbc_queries.py` (TC006↔W0611 via TYPE_CHECKING+string-cast; TID252→absolute).  Reusable patterns: `memory/feedback_ruff_all_lint_campaign.md`; live detail: `.session-state.md`.
- **`python/aletheia/client/` ✅ 2026-05-28** (commit `b9b237f`, **recovery + cleanup**) — all 15 files: ruff `check` + `format` clean, pylint 10.00, basedpyright 0/0/0, **875 tests pass**.  80→0 ruff findings; net suppressions **−1**.  Highlights: `_format_formula_inner` 15-arm LTL `if op ==` chain → 2 family handlers (`_format_unary` / `_format_binary`) + `_format_never` + 4 token tables reusing the existing `_UNARY_OPS`/`_BINARY_OPS` frozensets (mirrors `_walk_formula`) — REMOVES 2 pre-existing pylint disables; the 24-site TRY003 cluster turned out mechanical (msg-var extraction = same statements as EM101/EM102, like the cleaned `_signal_ops.py`/`rational.py` siblings); `send_frame`'s C901 cleared by extracting `_handle_property_batch` (off the ack fast path); 1 approved `# noqa: PLR0913` on `send_frame` mirroring its existing too-many-arguments disable (CAN-frame wire contract, parity with C++/Go positional calls — matches `_backend.py` dual-comment precedent).  Byte-identical formatter output verified by `test_enrichment` exact-`==` `never` + metric substring assertions (47/47).  Strengthened user rules in this commit's session: `feedback_no_suppression_without_approval` (every suppression discussed first w/ rationale + alternatives, minimal scope, no unnecessary hot-path indirection) + `feedback_fix_tool_gate_violations` ("pre-existing" never a reason to skip — applies to formatters too, not just linters).
- **Roadmap**: (lint) ✅ **tree-complete + FULLY gate-enforced** — ruff(ALL)+pylint-10+bp-0/0/0 across `tools/`+`python/`(aletheia/tests/benchmarks)+`examples/`, and all three are now run_ci steps incl `tools/` (`66ba302`).  The old "4 R0801 dedupe / wire tools/ / next dirs" items are DONE (R0801 moot — combined pylint 10.00; benchmarks/examples ruff 0).  (warm) check-properties ✅ wired; **IWYU gate ✅ DONE** ([[project_agda_iwyu]]).  **REMAINING pre-merge program** (`.session-state` LATEST⁸): AletheiaError dual-path → Fraction B/C+loader JSONValue → opaque-sweep → renderer-proof → branch/PR-hygiene → merge `ci-speed`→main.  CL10-2 done (`60296fa`); CL10-3 + Agda-`Fin` PARKED.

**Standard gates** (`check-properties` now runs the warm process — same verdicts, cold batch removed; otherwise ci-speed is tooling-only, no Agda/runtime change): `cabal run shake -- {build, check-properties, check-invariants, check-no-properties-in-runtime, check-erasure, check-fidelity, check-ffi-exports, check-bound-enforcement, count-modules, check-runbook, check-changelog, check-limits-parity}` + Python `pytest tests/` + Go `go test ./aletheia/ -race` + C++ `ctest --test-dir cpp/build` + lint gates.

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
